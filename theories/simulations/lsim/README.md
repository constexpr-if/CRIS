# `theories/simulations/lsim` — the low-level (thread-pool) simulation

Logical path: `CRIS.simulations.lsim`.

`lsim` is the *local* simulation relation between two `LMod.t`s — that is,
between programs already reduced to `itree lmodE`, where resources have been
turned into part of the state and only the concurrency structure remains. It
is the layer directly below `msim`:

```
wsim → isim → msim → lsim → gsim
```

(The comment at the top of [`LSim.v`](LSim.v) says outright: *"You would not
like to delve into the definitions unless for changing the metatheory."*)

Its distinguishing feature is the **per-thread world**: instead of a single
invariant, `lsim` carries a `list world`, one entry per thread, plus the two
orderings `le_mine` (how *my* entry may evolve) and `le_others` (how the
*other* entries must be preserved).

---

## `LSim.v`

**`Record LWorld`** — a carrier `world`, an initial element `winit`, the
invariant `wf : list world → lstateT * lstateT → Prop`, and a preorder `wle`
with `wle_refl` / `wle_trans`.

**`Section LORDER`** (fixing `lw` and `my_tid`):
- `le_mine w w'` — the list may grow, and *my* entry may only increase w.r.t.
  `wle`;
- `le_others w w'` — the length is unchanged and every *other* entry is
  literally equal;
- `le_mine_refl`, `le_mine_trans`, `le_others_refl`, `le_others_trans`,
  `le_others_inc` (stability under spawning a new thread).

**`lsim_def`** — the step relation, with the same inductive/coinductive split
as `msim`. Constructors: `lsim_ret`, `lsim_call` (the caller gives up its world
entry, satisfying `wf`, and gets back an entry related by `le_mine`),
`lsim_io`, `lsim_inline_src` / `_tgt`, `lsim_tau_src` / `_tgt`,
`lsim_choose_src` (∃) / `lsim_choose_tgt` (∀), `lsim_take_src` (∀) /
`lsim_take_tgt` (∃), `lsim_supdate_src` / `_tgt` (run an `SUpdate`),
**`lsim_spawn`** (the world list is extended with `winit`),
**`lsim_yield`** (the same world protocol as `lsim_call`), `lsim_gettid`,
`lsim_call_none` / `lsim_spawn_none`, and `lsim_progress` (which may also
weaken along `le_others`).

`_lsim` ties the inductive knot; `final_rel RR w0 w1 st_src st_tgt r_s r_t`
requires `le_mine w0 w1`, `RR w1 (st_src, st_tgt)` and equal return values; and
`lsim RR w0 ps pt w src tgt := paco8 _lsim bot8 _ _ (final_rel RR w0) …`.

**Metatheory.** `lsim_def_mon`, `lsim_tarski` (inner induction principle),
`lsim_mon`, `lsim_wmon` (weaken along `le_others`), `lsim_ind`,
`lsim_mon_rr`, `lsim_flag_mon`, `lsim_progress_flag`, `lsim_flag_down`,
`lsim_bot_flag_up`.

**Up-to closures.** `lsim_indC` / `lsim_indC_mon` / `lsim_indC_spec` (apply one
inductive step), `lsimC` / `lsimC_spec_aux` / `lsimC_spec`, `lflagC` /
`lflagC_mon` / `lflagC_spec` (weaken flags and worlds), `lbindR` / `lbindC` /
`lbindC_wrespectful` / `lbindC_spec` (the bind rule).

**`sim_fsem`** — two function bodies are related for every world in which the
current thread has an entry and `wf` holds.

**`Section LSim`** — the module-level statement
```coq
Record lsim_lmod (ms_src ms_tgt : LMod.t) (lworld : LWorld) := {
  wf_nil;      (* wf holds of the empty world and the initial states *)
  wf_winit;    (* wf is preserved by appending winit (i.e. by spawning) *)
  sim_fnsems;  (* every source function has a sim_fsem-related target function *)
}
```
with `wf_sim_miss` (if the target lacks a function, so does the source).

## `LSimMod.v`

Lifts `lsim_lmod` from `LMod.t` to `Mod.t` and into the logic:

```coq
lsim_mod Ms Mt : iProp Σ    (* sealed *)
  := "for a resource r: if Mt is well-formed then so is Ms, and for every
      valid rs splitting as Own rt ∗ Own r ∗ winv (∅,∅) there is an LWorld lw
      with lsim_lmod (Mod.to_lmod Ms rs) (Mod.to_lmod Mt rt) lw"
```
built directly as a `uPred` (the monotonicity obligation is discharged with
`Own_extends`). `lsim_mod_unseal` and the introduction rule
`lsim_mod_intro`.

Since the `Unreleased` CHANGELOG entry, the older `lsim_mod` was renamed
`lsim_lmod` and this `Mod.t`-level `lsim_mod` took its place.

## `LSimAdequacy.v` — from `lsim` to `gsim`

- `b2smj : bool → smj` — translate a boolean progress flag into the
  three-valued `smj` measure used by `gsim` (`true ↦ smj_mid`,
  `false ↦ smj_bot`).
- **`lsim_gsim`** (the bulk of the file) — if `lsim_lmod ms_src ms_tgt lw` and
  every thread in the pool is individually `lsim`-related in a compatible
  world, then the two *scheduled* programs
  `interp_stateE (iterV (handle_callE (LMod.prog ms)) (my_tid, itrs)) st` are
  `gsim`-related. The proof is a coinduction over the schedule with an inner
  `lsim_ind`, driven by the `z*` tactics of
  [`../gsim/GSimTactics.v`](../gsim/GSimTactics.v).
- **`lsim_adequacy`** — the packaged statement:
  `lsim_lmod ms_src ms_tgt lw → gsim eq smj_bot smj_bot (LMod.compile ms_src arg) (LMod.compile ms_tgt arg)`.

## `LSimTactics.v`

Paco hints (`lsim_mon`, `cpn8_wcompat`), the `ired`-based normalisers
`ired_s`, `ired_t`, `ired_both`, `prep`; `apply_lsimC_spec` and
`guclo_lflagC` (which recover the implicit `fl_src`/`fl_tgt`/`lw`/`my_tid`
from the goal); the stepping tactics `_step`, `step`, `steps`; and the
`hide` / `unhide` pair for temporarily abstracting a subterm.
