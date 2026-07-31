# `theories/simulations` — the simulation tower

Logical path: `CRIS.simulations.*`.

This directory contains no `.v` files of its own; it groups the four layers
that take a user-written proof down to a statement about observable
behaviour. The chain, as the header comment of
[`lsim/LSim.v`](lsim/LSim.v) puts it, is

```
wsim → isim → msim → lsim → gsim
```

with contextual refinement sitting on top of all of it.

| Subdirectory | Files | What it defines |
| --- | --- | --- |
| [`msim/`](msim/) | 16 | The **module simulation** and everything a user touches: the raw `paco8` relation `msim`, its `iProp` packaging `isim`, the invariant-carrying `wsim`, the module-level statement `ISim.t`, and the whole `c*`/`i*`/`w*` tactic suite |
| [`lsim/`](lsim/) | 4 | The **low-level simulation** between `LMod.t`s, with a per-thread world (`LWorld`, `le_mine`, `le_others`); `lsim_lmod`, `lsim_mod`, and adequacy into `gsim` |
| [`gsim/`](gsim/) | 5 | The **global simulation** on closed `itree coreE` programs, with the three-valued measure `smj`; `gsim_mod`, and adequacy into `Beh.of_itree` |
| [`ctxrefine/`](ctxrefine/) | 5 | `Beh`, `refines`, `ctx_refines`, the two top-level adequacy theorems (`ISim_closed_adequacy`, `main_adequacy`), and the `BiProset` structure on modules |

---

## Reading order

For a **user**, only `msim/` and the top-level statements of `ctxrefine/`
matter:

1. State your goal as `ISim.t open ms mt Ist` (or `closed` for a whole
   program).
2. Start with `cStartModSim` / `cStartFunSim`
   ([`msim/TacticsInit.v`](msim/TacticsInit.v)).
3. Drive it with `cStep`, `cCall`, `cYield`, `cCoind`, …
   ([`msim/Tactics.v`](msim/Tactics.v)).
4. Conclude with `main_adequacy` (open) or `ISim_closed_adequacy` (closed)
   ([`ctxrefine/`](ctxrefine/)).

For someone **changing the metatheory**, the order is bottom-up:
`gsim/GSim.v` → `gsim/GSimAdequacy.v` → `lsim/LSim.v` →
`lsim/LSimAdequacy.v` → `msim/MSim.v` → `msim/MSimAdequacy.v` →
`msim/ISim.v` → `msim/ISimAdequacy.v` → `ctxrefine/`.

## How the layers differ

| | `gsim` | `lsim` | `msim` | `isim` / `wsim` |
| --- | --- | --- | --- | --- |
| programs related | `itree coreE R` | `itree lmodE` in an `LMod.t` | `itree crisE` in a `Mod.t` | same as `msim` |
| state | none | `lstateT` (kv store + resource) | `gmap key (option Any.t)` | same |
| resources | none | inside the state | an explicit `Σ` argument | inside the `uPred` |
| invariant | none | `LWorld.wf`, one entry per thread | `Ist : ist_type Σ` | same, plus `winv Ep` for `wsim` |
| progress | `smj` (three-valued) | two booleans | two booleans | two booleans |
| lives in the logic? | no | no (but `lsim_mod` does) | no (but `isim` does) | yes |

Each adequacy step erases one of these columns: `msim → lsim` turns the
explicit resource into part of the state
([`msim/MSimAdequacy.v`](msim/MSimAdequacy.v)); `lsim → gsim` interleaves the
threads and erases the per-thread worlds
([`lsim/LSimAdequacy.v`](lsim/LSimAdequacy.v)); `gsim → Beh` erases everything
but the observable events ([`gsim/GSimAdequacy.v`](gsim/GSimAdequacy.v)).

## The two adequacy theorems

```coq
(* whole program, ctxrefine/ClosedAdequacy.v *)
ISim_closed_adequacy : ISim.t closed Ms Mt Ist ⊢ refines Mt Ms

(* open module, ctxrefine/MainAdequacy.v *)
main_adequacy : ISim.t open Ms Mt Ist ⊢ ctx_refines Mt Ms
```

The `open`/`closed` distinction is the `contextuality` flag from
[`msim/MSimCommon.v`](msim/MSimCommon.v): in the `closed` setting a call to an
undefined function is vacuously simulated (`msim_call_none`), which is only
sound when nothing further will be linked in.
