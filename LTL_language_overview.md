Cardano Trace LTL Overview
==========================

Goal
----
Provide a portable description of the derivative-based LTL fragment so it can be used as the specification core for Cardano node trace analysis.

1. Language Core
----------------
- `LTL a` is a GADT over a payload `a` that embeds: universal and existential quantification (`ForallLTL`, `ExistsLTL`), strict and weak next operators (`NextLTL`, `WNextLTL`), bounded repetitions of each next variant (`RepeatNextLTL`, `RepeatWNextLTL` with an `idx` counter), the standard `UntilLTL`, variadic disjunction/conjunction (`OrLTL`, `AndLTL`), negation, booleans, atomic predicates (`BaseLTL`), and explicit pattern variables with optional match ranges (`VarLTL`). The weak-next operator (`WNextLTL`) states that the nested formula must hold at the next event if one exists, but it is satisfied vacuously when the trace ends immediately—making it ideal for specifications that should tolerate early termination.
- Equality is structure-based except for `BaseLTL`, which compares via a cached 32-bit hash. Keeping the hash field in any reimplementation helps deduplicate common atoms when building monitors or automata.

2. Atomic Predicates & Trace Labels
-----------------------------------
- `PropType` is a `(String, String)` key–value pair, meaning atomic propositions correspond naturally to fields in Cardano telemetry (e.g., `"component" = "Forge"`, `"severity" = "Warning"`).
- `Prop` is a mini-logic with `BaseProp`, `TrueProp`, and `AndProp`. This is sufficient because all temporal structure lives in `LTL`, and disjunction emerges from the outer formula.
- A helper `eval` can map a domain-specific description down to a `Prop`. For Cardano we can map structured trace objects into conjunctive claims like “block no == 425” ∧ “slot == 100” before feeding them into `BaseLTL`.

3. Event Stream Model
---------------------
- Traces are lists of `Event Props`. Each `Event props` captures the observed key–value map for one log record or state snapshot. `TerminalEvent` marks that no more events follow; it is essential for interpreting weak next and `Until`.
- In the Cardano node pipeline, an event could be derived from `TraceObject` payloads, after normalising them into the `Map String String` representation expected by `Props`.
- When richer payloads are required, first store them as `OrderedMap (timestamp, namespace) -> Map String String`. Each entry keeps the raw cardano-node data (slot, block hash, failure reason) as a key/value map, keyed by its exact timestamp and namespace. During monitoring, iterate over the ordered map in chronological order, convert each `(ts, ns, attrs)` entry to an `Event attrs'` where `attrs'` extends `attrs` with canonical fields like `"timestamp" = show ts` and `"namespace" = ns`, and feed that stream to `derivativeSimp`. This preserves order (critical for the derivative semantics) while giving formulas access to both the namespace and any domain-specific fields.

4. Derivative Semantics
-----------------------
- The derivative `deriv :: LTL a -> Event b -> LTL a` rewrites a formula after consuming one event—this mirrors Brzozowski derivatives for regular expressions but extended with temporal operators. Iterating derivatives over a trace (`derivative` / `derivativeSimp`) yields the residual obligation for the suffix.
- Key rewrite rules: `NextLTL φ` becomes `φ` after a real event but collapses to `False` at `TerminalEvent`; `WNextLTL φ` behaves like `Next` on events yet evaluates to `True` when the trace ends (vacuous satisfaction). Repetition nodes decrement `idx` until exposing the nested formula. `UntilLTL x y` rewrites to `deriv y` OR (`deriv x` AND the original `Until`). `ExistsLTL` behaves like “eventually”: derivative is `φ' ∨ ExistsLTL φ`. `ForallLTL` is “always”: derivative is `φ' ∧ ForallLTL φ`, but it becomes `True` once `TerminalEvent` is reached.

5. Simplification & Satisfaction
--------------------------------
- `simp` and its fixpoint version `simplify` remove redundant structure: flatten nested conjunctions/disjunctions, drop `True`/`False`, and deduplicate equivalent children. This keeps the state space finite when derivatives are repeatedly applied.
- `removeWeak` replaces all weak-next constructs with `True`. This is used right before the final two steps of a finite trace (`… , penultimate, TerminalEvent`) so that vacuous obligations do not block satisfaction.
- `isSat` maps any residual formula to a boolean by interpreting unresolved temporal structure conservatively (`ForallLTL` becomes `True`, everything else defaults to `False`). Combining `derivativeSimp`, `removeWeak`, and `isSat` yields `checkDerivSimpLTL`, a practical monitor for Cardano traces that already append `TerminalEvent`.
- Exploratory helpers such as `possibly`, `definitelyTrue`, and `definitelyFalse` enumerate all boolean valuations for remaining atoms, which is useful when a trace prefix leaves the verdict unknown but an operator (e.g. CLI) still wants to report “definitively good/bad/pending”.

6. Automata & Monitoring Hooks
------------------------------
- Because simplification keeps the derivative closure finite, repeatedly deriving every formula over a finite alphabet of events produces the state set of a deterministic monitor. Functions like `allStates`, `nfa`, and `nfaFinalStates` (easy to port) automate this, allowing the Cardano toolchain to precompile LTL specs into NFAs/Büchi automata for efficient runtime checks.
- Suggested Cardano usage: define the event alphabet by bucketing recurring trace labels (e.g., leadership checks, mempool status, networking), emit `TerminalEvent` whenever a bounded scenario ends (block forging attempt, slot interval), and apply the derivative monitor to flag violations or certify compliance of the observed behaviour.

7. Worked Examples
------------------
The leadership/forging trace layer already emits rich names such as `StartLeadershipCheck`, `SlotIsImmutable`, `NodeIsLeader`, `ForgedBlock`, `AdoptedBlock`, etc. Treat each namespace as an atomic predicate via `BaseProp ("Namespace", tag)` or a richer key/value pair when additional details (slot, hash) are required.

**Leadership outcome within a bounded window**
- Define base atoms
  `pStart = BaseProp ("Namespace","StartLeadershipCheck")`
  `pLeader = BaseProp ("Namespace","NodeIsLeader")`
  `pNotLeader = BaseProp ("Namespace","NodeNotLeader")`.
- Encode “after every leadership check we must soon learn whether we are leader” as
  `StartLeadershipCheck ⇒ proxNext_k (NodeIsLeader ∨ NodeNotLeader)`
  where `proxNext_k φ` is modeled by the weak bounded-next:
  `proxNext_k φ ≜ RepeatWNextLTL { idx = k, ltl = φ }`.
  Setting `k` to the maximum number of intermediate bookkeeping events ensures the monitor only scans the “reasonably proximate future” and won’t confuse overlapping leadership checks.

**Forged block must conclude with an adoption verdict**
- Atoms: `pForged = BaseProp ("Namespace","ForgedBlock")`, `pAdopted`, `pDidntAdopt`, `pInvalid`.
- Specification:
  `ForgedBlock ⇒ proxNext_k (AdoptedBlock ∨ DidntAdoptBlock ∨ ForgedInvalidBlock)`
  using the same `proxNext_k`. Because `RepeatWNextLTL` degrades to `True` when the trace ends, premature termination does not spuriously fail the check, yet a long-lived trace must still emit one of the three follow-up messages within `k` steps.

**Failure reason implies cannot-forge decision**
- Failure predicates: `pImmutable = BaseProp ("Namespace","SlotIsImmutable")`, `pFuture = BaseProp ("Namespace","BlockFromFuture")`, `pNoLedgerState`, `pNoLedgerView`, `pForgeStateUpdateError`, etc.
- Outcome predicate: `pCannotForge = BaseProp ("Namespace","NodeCannotForge")`.
- Template:
  `(SlotIsImmutable ∨ BlockFromFuture ∨ NoLedgerState ∨ NoLedgerView ∨ ForgeStateUpdateError) ⇒ proxNext_k NodeCannotForge`.
  This guarantees that every recorded failure explanation is followed quickly by a `NodeCannotForge` event, making it easy to alert on missing diagnostics.

**Optional richer linking**
- When events carry unique identifiers (e.g., slot number, block hash), lift them into the proposition payload and use conjunctions to correlate cause and effect beyond time proximity. Example:
  `ForgeChainRoot(slot, point)` AND `ForgedBlock(slot, _)` ⇒ `AdoptedBlock(slot, _)` within the same `proxNext_k`.
  Since these atoms include the slot, traces with overlapping slots remain distinguishable even if windows overlap.

**Forge flow straight from consensus**
- The consensus repo documents the full forge state machine (`ouroboros-consensus-diffusion/Ouroboros/Consensus/Node/Tracers.hs:177-234`), making it easy to encode per-edge obligations. Translate each box/arrow into an LTL clause:
  1. `BlockContext ⇒ proxNext_k (LedgerState ∨ NoLedgerState)` ensures that once the forger selects an ancestor, it either acquires or fails to acquire the ledger state immediately after.
  2. `LedgerState ⇒ proxNext_k (LedgerView ∨ NoLedgerView)` mirrors the next arrow in the diagram (ledger view forecast).
  3. `LedgerView ⇒ proxNext_k (ForgeStateUpdateError ∨ NodeCannotForge ∨ NodeNotLeader ∨ NodeIsLeader)` captures the final branching point before forging.
  4. `NodeIsLeader ⇒ proxNext_k ForgedBlock` and `NodeNotLeader ⇒ proxNext_k StartLeadershipCheck` (if you want to force a new cycle) guard the success/failure split.
  5. `ForgedBlock ⇒ proxNext_k (AdoptedBlock ∨ DidntAdoptBlock ∨ ForgedInvalidBlock)` is the adoption edge at the bottom of the flowchart.
- Each clause is instantiated with the event namespace exposed by `cardano-node` (`Cardano/Node/Tracing/Tracers/Consensus.hs:1733-1974`), so you can map them to `BaseProp ("Namespace","LedgerView")`, etc.

**Ledger ticking and mempool snapshot (cardano-node)**
- The node repo exposes debug namespaces `ForgeTickedLedgerState` and `ForgingMempoolSnapshot` (`cardano-node/src/Cardano/Node/Tracing/Tracers/Consensus.hs:1518-1742`). These mark the final preparations between “we are leader” and “we forged a block”.
- Two useful invariants are:
  - `NodeIsLeader(slot) ⇒ proxNext_k ForgeTickedLedgerState(slot)` — leaders should tick the ledger before forging.
  - `ForgeTickedLedgerState(slot) ⇒ proxNext_k ForgingMempoolSnapshot(slot)` and `ForgingMempoolSnapshot(slot) ⇒ proxNext_k ForgedBlock(slot)` — ensures mempool snapshotting and actual forging happen back-to-back for the same slot (use slot equality in the payload map).

**Forge errors surface as cannot-forge**
- Both repos expose `TraceForgeStateUpdateError` and `TraceNodeCannotForge`. When the forge state fails to evolve (KES exhaustion, etc.), `TraceNodeCannotForge` must be emitted with the same slot (`Cardano/Node/Tracing/Tracers.hs:1174-1178`). Encode:
  `ForgeStateUpdateError(slot, reason) ⇒ proxNext_k NodeCannotForge(slot, reasonTag)`.
- You can extend the consequent with `NodeNotLeader` if the policy is to immediately abandon the slot.

**Leadership cycle liveness**
- Using the start/end markers from consensus (`TraceStartLeadershipCheck`, `TraceNodeIsLeader`, `TraceNodeNotLeader`) enforce that every leadership check terminates quickly:
  `StartLeadershipCheck(slot) ⇒ proxNext_k (NodeIsLeader(slot) ∨ NodeNotLeader(slot) ∨ SlotIsImmutable(slot, _) ∨ BlockFromFuture(slot, _) ∨ NoLedgerState(slot, _) ∨ NoLedgerView(slot, _) ∨ ForgeStateUpdateError(slot, _))`.
- This clause is stronger than the earlier “leader vs not leader” invariant because it enumerates every failure edge listed in the consensus flowchart, ensuring no leadership attempt stalls silently.

These examples can be fed directly into the derivative pipeline: parse the trace into `Event Props`, instantiate `proxNext_k` with the desired bound via `RepeatWNextLTL`, and run `checkDerivSimpLTL` to flag violations after Cardano node monitoring.
