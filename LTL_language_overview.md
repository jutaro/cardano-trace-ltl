Cardano Trace LTL Overview
==========================

Goal
----
Explain a derivative-driven fragment of linear temporal logic that is suitable for Cardano trace analysis.

1. Temporal Vocabulary
----------------------
- The logic offers implication, conjunction/disjunction, and negation, plus a small family of temporal constructs: universal and existential quantifiers over trace suffixes, strict and weak “next” operators, bounded repetitions of those next operators, and the classical “until”.
- Weak next behaves like strict next whenever another event exists but is considered satisfied automatically once the trace ends. The bounded repetition variant simply chains that weak obligation across a fixed number of steps, enabling “in the reasonably proximate future” requirements without referencing wall-clock time.
- Atomic formulas are left abstract—they represent predicates over individual trace records. Everything else in the system manipulates those predicates symbolically.

2. Atomic Predicates & Trace Records
------------------------------------
- Each trace record should be normalised into a canonical structure that exposes the metadata the Cardano node already emits: timestamp, namespace (e.g., `["Forge","Loop","ForgedBlock"]`), severity, host, thread id, slot number, block number, plus an extensible map of additional fields (block hash, failure reason, ledger point, etc.).
- Atomic predicates state facts about that structured record: “namespace equals Forge.ForgedBlock”, “slot equals 423115”, “reason belongs to {BlockFromFuture, SlotIsImmutable}”, “severity is at least Warning”, “field `prev` matches a given block hash pattern”.
- Compound atoms are simply conjunctions of such facts; disjunctions are handled at the surrounding LTL level.

3. Trace Model
--------------
- A trace is a finite or infinite sequence of the normalised records, ordered by timestamp. For finite traces we append a distinguished terminal marker so weak operators can observe that the stream ended.

4. Derivative Perspective
-------------------------
- The logic is interpreted via derivatives: consuming an event rewrites the current obligation into a new formula that describes what must hold for the remaining suffix. This mirrors Brzozowski derivatives for regular expressions, extended to the temporal combinators.
- Brzozowski derivatives originate in regular-expression theory: for a regex `R` and an input symbol `a`, the derivative `∂ₐ R` recognises exactly those suffixes `w` for which the concatenation `a·w` belongs to `R`. Iteratively taking derivatives as each symbol arrives lets one perform deterministic matching without constructing an automaton up front. Our temporal setting follows the same idea—treat each log record as the “symbol”, rewrite the obligation, and inspect the residual formula instead of building a separate monitor.
- Strict next simply exposes its child after one event, weak next falls back to `True` at the trace boundary, `until` unfolds into “either the right side becomes true now, or the left side holds and we keep waiting”, and the quantifiers (“eventually” / “always”) respectively add disjunctions or conjunctions with their own derivatives.
- Because every rewrite references other formulas already present in the logic, the process stays symbolic: no evaluation happens until a trace record is inspected.
- Quantifiers deserve a special note in light of the conversation above. For `∀F`, the derivative with respect to the current event `e` splits into “`F` must hold for `e`” AND “`∀F` must continue to hold for all future events.” This is exactly what the rewrite `deriv (∀F)` → `(deriv F) ∧ (∀F)` expresses. The existential case uses disjunction instead. In Cardano traces “time” usually means “slot”, yet several log messages can share the same slot. To stay faithful to the mathematical meaning (“consume everything that happened at `i` before moving to `i+1`”), feed every event that belongs to slot `i` through the derivative before advancing to slot `i+1`, or bound the number of intra-slot events you are willing to consider.

5. Simplification & Verdicts
----------------------------
- After each derivative step we simplify: flatten nested conjunctions/disjunctions, remove redundant `True`/`False`, collapse duplicate subformulas, and optionally drop weak-next obligations just before the last two events of a finite trace.
- To produce a final Boolean verdict on a finite trace, evaluate the simplified residual formula with a conservative interpretation: unresolved universal obligations become `True` (they were forced by the terminal marker), everything else defaults to `False`. This matches the usual “lasso” approximation used in runtime verification, where the observed prefix is treated as the stem of a lasso and the last state is assumed to loop forever; by assuming that eventual repetition, we ask whether any suffix compatible with that stem-and-loop pattern could violate the property.

6. Automata & Offline Monitoring
--------------------------------
- If the alphabet of atomic predicates you care about is finite (e.g., a bounded collection of namespaces and slot-labelled events), the derivative process can only produce finitely many distinct residual formulas. Each residual formula can therefore be treated as a “state” in a deterministic monitor: feed an event, take the derivative, simplify, land in another state. By enumerating all such states and recording which state each event causes you to enter, you effectively synthesise a deterministic automaton or lookup table that implements the original LTL property.


7. Worked Examples (concrete notation)
--------------------------------------
Let `proxNext_k φ` abbreviate “φ must hold within the next `k` events, tolerating early termination” and treat each trace namespace as an atom. The following invariants operate on the standard Cardano forging messages:

1. **Leadership outcome within a window**
   `StartLeadershipCheck ⇒ proxNext_k (NodeIsLeader ∨ NodeNotLeader)`
   Use a `k` large enough to cover expected intermediate bookkeeping events so overlapping leadership checks don’t interfere.

2. **Forge adoption chain**
   `ForgedBlock ⇒ proxNext_k (AdoptedBlock ∨ DidntAdoptBlock ∨ ForgedInvalidBlock)`
   Guarantees every forged block is followed swiftly by an adoption verdict; weak next ensures the rule is vacuously true if the node shuts down immediately after forging.

3. **Failure diagnostics lead to cannot-forge**
   `(SlotIsImmutable ∨ BlockFromFuture ∨ NoLedgerState ∨ NoLedgerView ∨ ForgeStateUpdateError) ⇒ proxNext_k NodeCannotForge`
   Ensures that every recorded failure reason triggers the explicit `NodeCannotForge` event, preventing silent drops.

4. **Ledger ticking and mempool snapshot sequence**
   `NodeIsLeader(slot) ⇒ proxNext_k ForgeTickedLedgerState(slot)`
   `ForgeTickedLedgerState(slot) ⇒ proxNext_k ForgingMempoolSnapshot(slot)`
   `ForgingMempoolSnapshot(slot) ⇒ proxNext_k ForgedBlock(slot)`
   These bindings force the per-slot forging pipeline to respect the documented ordering, matching the flowchart published in the consensus repository.

5. **Consensus flow edges**
   `BlockContext ⇒ proxNext_k (LedgerState ∨ NoLedgerState)`
   `LedgerState ⇒ proxNext_k (LedgerView ∨ NoLedgerView)`
   `LedgerView ⇒ proxNext_k (ForgeStateUpdateError ∨ NodeCannotForge ∨ NodeNotLeader ∨ NodeIsLeader)`
   Encodes each edge in the forging diagram so that missing or reordered messages are caught immediately.

6. **Immutable or future tip aborts the slot**
   `(SlotIsImmutable ∨ BlockFromFuture) ⇒ proxNext_k NodeNotLeader`
   Mirroring the early branches in `Ouroboros/Consensus/Node/Tracers.hs`, the node must record that it will not lead the slot whenever the tip inhabits the same/future slot, preventing it from silently forging on stale ancestors.

7. **Adoption thread crashes bubble up**
   `AdoptionThreadDied ⇒ proxNext_k NodeCannotForge`
   If the adoption worker dies (e.g., due to an async exception) the forger cannot safely continue; this invariant forces an explicit `NodeCannotForge` so operators see the failure instead of a quiet stall.

8. **Invalid forge triggers a fresh leadership cycle**
   `ForgedInvalidBlock(slot, block) ⇒ proxNext_k (NodeCannotForge(slot) ∧ proxNext_k StartLeadershipCheck(slot+1))`
   Use the slot numbers embedded in the trace payload to bind the next leadership check to the successor slot. This captures the expectation that forging an invalid block should immediately halt forging for that slot and restart the leadership pipeline for the next slot.

9. **Ledger anchor consistency**
   `LedgerState(slot, point) ⇒ proxNext_k ForgeTickedLedgerState(slot, point)`
   Both events expose the anchor point; comparing the `point` fields ensures the ticker processes exactly the ledger snapshot that was previously fetched, matching the code path between `TraceLedgerState` and `TraceForgeTickedLedgerState`.
