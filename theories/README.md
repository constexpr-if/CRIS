# `theories` — the CRIS framework

Logical path: `CRIS.*` (see [`_CoqProject`](../_CoqProject)).

This is the framework proper: everything needed to *state* what a CRIS module
is, *prove* one module refines another, and *conclude* observable behaviour
inclusion. The worked examples that use it live in
[`library/`](../library/).

```
                     ┌──────────────┐
                     │     lib      │  tactics, Any, alists, SAT, BiProset, ITree helpers
                     └──────┬───────┘
                            │
                     ┌──────▼───────┐
                     │ iris_system  │  uPred, GRA/own, sProp, invariants, atomic updates
                     └──────┬───────┘
                            │
                     ┌──────▼───────┐
                     │    common    │  coreE/callE/crisE/lmodE, Beh, ConcRA, IRed
                     └──────┬───────┘
                            │
                     ┌──────▼───────┐
                     │   modules    │  SMod → Mod → LMod → itree coreE
                     └──────┬───────┘
                            │
              ┌─────────────▼─────────────┐
              │        simulations        │  wsim → isim → msim → lsim → gsim → refines
              └──────┬─────────────┬──────┘
                     │             │
             ┌───────▼──────┐ ┌────▼──────────┐
             │    filter    │ │  cancellation │
             └──────────────┘ └───────────────┘
```

---

## Subdirectories

| Directory | Files | Contents |
| --- | --- | --- |
| [`lib/`](lib/) | 14 | Generic Coq support: `sflib` and `Coqlib` (tactics), `StdAxioms` (the classical axioms CRIS assumes), `Any` (universal type), `AList`, `SubPerm`, `Red`/`LAuto` (rewriting automation), `exco`/`exco_stream` (coinductive containers), **`SAT`** (the stratified-syntax framework), `ITreelib`, `ltac2_lib`, **`BiEnrichedProset`** (`PROP`-enriched preorders and their `j`-tactics) |
| [`iris_system/`](iris_system/) | 20 | CRIS's separation logic: a **step-index-free** `uPred` with a *strong* `bupd` ([`base_logic/`](iris_system/base_logic/)), the global resource algebra `GRA` and `own` ([`iprop.v`](iris_system/iprop.v), [`own.v`](iris_system/own.v)), the stratified proposition syntax [`sProp.v`](iris_system/sProp.v), world satisfaction / fancy updates / invariants ([`invariants.v`](iris_system/invariants.v), [`syn_invariants.v`](iris_system/syn_invariants.v)), ghost-state libraries ([`lib/`](iris_system/lib/)), and relational atomic updates ([`atomic.v`](iris_system/atomic.v)) |
| [`common/`](common/) | 7 | The event signatures (`coreE`, `callE`, `lstateE`, `pgE`, `agE`, and the two program signatures `lmodE` and `crisE`), observable behaviours (`Tr.t`, `Beh.of_itree`), the concurrency RA (`TID`/`YIELD`), function names, the `ired` framework, and the two preludes `Common.v` / `CRIS.v` |
| [`modules/`](modules/) | 9 | What a program *is*: `fspec`/`fspec_rel`, `specmap`, sandboxing, and the three module types `SMod.t` → `Mod.t` → `LMod.t` with the translations between them (`SModTr`, `ModTr`, `LModTr`) |
| [`simulations/`](simulations/) | 30 | The simulation tower `wsim → isim → msim → lsim → gsim`, the proof tactics, and the two adequacy theorems |
| [`filter/`](filter/) | 2 | Event filters: `CFilter` (by function name) and `SFilter` (the concurrency events), with module introduction/elimination |
| [`cancellation/`](cancellation/) | 13 | Inlining (`MInline`) and the theorem that all specification scaffolding may be erased once discharged (`Cancel.cancel`) |

## The three keys to the design

**1. No step-indexing.** `uPred` is a plain upward-closed predicate on
resources, `▷` is the identity, and every proposition is timeless. What Iris
recovers from step-indexing, CRIS recovers from a **stratified syntax**: a
proposition stored in an invariant is not an `iProp` but a term
`GTerm.t n` of an explicitly level-indexed language, and an invariant at level
`n` may only mention levels `< n`
([`lib/SAT.v`](lib/SAT.v), [`iris_system/sProp.v`](iris_system/sProp.v)).

**2. Imaginary specifications.** A module carries, per function, an *optional*
specification. `SMod.to_mod` compiles those specifications into
`Assume`/`Guarantee`/`Take`/`Choose` events that a simulation proof can exploit
— even though no real program performs them. The soundness of this is exactly
[`cancellation/`](cancellation/): once every function is verified, the
scaffolding can be cancelled.

**3. Linking is a commutative monoid.** `Mod.add` (`★`) with `Mod.empty` (`⌽`)
is commutative and associative *up to Leibniz equality*, achieved by keeping
scope lists sorted and making function maps `option`-valued so that a name
defined twice becomes `None` rather than an error. Together with
`ctx_refines` this makes modules a `BiProset`
([`simulations/ctxrefine/CtxRefineFacts.v`](simulations/ctxrefine/CtxRefineFacts.v)),
so refinement proofs compose with the `j`-tactics of
[`lib/BiEnrichedProset.v`](lib/BiEnrichedProset.v).

## Where to start

- To *use* the framework: `From CRIS.common Require Import CRIS.` pulls in
  everything. Then read [`modules/`](modules/) for how to write a module and
  [`simulations/msim/`](simulations/msim/) for how to prove one.
- To *understand* it: [`common/Events.v`](common/Events.v) →
  [`modules/`](modules/) → [`simulations/`](simulations/).
- To *change the logic*: [`iris_system/`](iris_system/).
