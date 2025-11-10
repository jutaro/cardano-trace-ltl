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
- When data arrives out of order (e.g., from multiple log files), first merge everything into an ordered map keyed by `(timestamp, namespace)`, then iterate through that map to feed the temporal monitor. This preserves causal order while retaining all metadata for the predicate layer.

4. Derivative Perspective
-------------------------
- The logic is interpreted via derivatives: consuming an event rewrites the current obligation into a new formula that describes what must hold for the remaining suffix. This mirrors Brzozowski derivatives for regular expressions, extended to the temporal combinators.
- Strict next simply exposes its child after one event, weak next falls back to `True` at the trace boundary, `until` unfolds into “either the right side becomes true now, or the left side holds and we keep waiting”, and the quantifiers (“eventually” / “always”) respectively add disjunctions or conjunctions with their own derivatives.
- Because every rewrite references other formulas already present in the logic, the process stays symbolic: no evaluation happens until a trace record is inspected.

5. Simplification & Verdicts
----------------------------
- After each derivative step we simplify: flatten nested conjunctions/disjunctions, remove redundant `True`/`False`, collapse duplicate subformulas, and optionally drop weak-next obligations just before the last two events of a finite trace.
- To produce a final Boolean verdict on a finite trace, evaluate the simplified residual formula with a conservative interpretation: unresolved universal obligations become `True` (they were forced by the terminal marker), everything else defaults to `False`. This matches the usual “lasso” approximation used in runtime verification.

6. Automata & Offline Monitoring
--------------------------------
- Repeatedly applying derivatives to every formula over a finite alphabet of atomic predicates yields a finite set of residual formulas—the “states” of a deterministic monitor. Enumerating these provides an automaton or table-driven checker that can be embedded into tooling, batching, or benchmarking pipelines.
- Because simplification keeps the residual set small, it is practical to precompute these states for frequently used specifications (leadership outcome, forging success, adoption flow, etc.).

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
