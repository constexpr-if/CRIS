# `library/scheduler` — a user-level scheduler, and logically atomic triples

Logical path: `CRIS.scheduler`.

The largest and most load-bearing of the example libraries. It does two
things:

1. It implements a **user-level scheduler** (`Sch.spawn`, `Sch.yield`,
   `Sch.join`) on top of CRIS's primitive `Spawn`/`Yield`/`GetTid`, and proves
   the implementation (`SchI`) refines its abstraction (`SchA`). The
   abstraction is what turns raw thread identifiers into ownership-carrying
   `Tid` tokens and gives `join` a specification.
2. On top of that, it provides the **logically atomic triples** of
   [`Atomic.v`](Atomic.v) — the `{{{ P }}} body {{{ RET ret, Q }}} @ N` and
   `<<{ ∀∀ x, αP, ∃∃ ret, αQ }>> @ N` notations — which is how concurrent data
   structures are specified in CRIS.

Everything here builds on the relational atomic updates of
[`theories/iris_system/atomic.v`](../../theories/iris_system/atomic.v).

---

## `SchHeader.v` — the interface and the client-side `yield` loop

- Signatures `SchHdr._spawn`, `SchHdr.spawn`, `SchHdr.yield`, `SchHdr.join`,
  and `SchHdr.exports`. The scope string is `SCH := "sch"` (`Opaque`).
- `Section FSpec`: `sfunN` / `sfunU` (the `SAny.t`-valued analogues of
  `cfunN`/`cfunU` — the scheduler passes thread arguments as `SAny.t` so they
  can be re-boxed into `Any.t`), and `interp_cond` (interpret a
  level-existential syntactic proposition `{n & GTerm.t n}`).
- **`Module Sch`** — what a *client* writes:
  - `Sch.spawn`, `Sch.join`;
  - **`Sch.yield`** (notation **`𝒴`**) — not a single call but an
    angelically-controlled loop: repeatedly `Choose (option bool)` to decide
    whether to yield again (`Some true`), spin (`Some false`) or stop (`None`).
    Sealed under `SCH`.
  - `Sch.terminate` — yield forever;
  - **`Sch.yield_namespace N`** (notation **`𝒴@{N}`**) — the same loop, but
    each yield is bracketed by `Guarantee (winv (↑N,↑N))` … `Assume (winv (↑N,↑N))`,
    i.e. the invariants in `N` are released across the scheduling point.
    `𝒴@{None}` is `𝒴`.
- Unfolding lemmas `yield_unfold`, `yield_namespace_yield`,
  `yield_namespace_unfold`, with the helpers `option_Guarantee`,
  `option_Assume`. `Sch.yield_namespace` is `simpl never`.
- Yielding loops: `yield_iter body arg` / `unfold_yield_iter` and
  `yield_namespace_iter N body arg` / `unfold_yield_namespace_iter` — a loop
  that yields before every iteration and once more on exit. This is the
  skeleton every atomic operation is built from.

## `SchI.v` — the implementation

`thpool := list (nat * option SAny.t)` — for each user-level thread, its
underlying CRIS thread id and (once finished) its return value.
`choose_index ths` angelically picks a runnable index.

State: two keys in scope `["sch"]`, `v_ths := "sch" ↯ "ths"` (the pool) and
`v_tid := "sch" ↯ "tid"` (the current user-level thread).

Functions (all with mask `msk_real (msk_scp scopes msk_true)`, no specs):
- `inner_spawn (fn, arg)` — the trampoline actually handed to the primitive
  `Spawn`: run `fn`, store the result in the pool, then `Sch.terminate`;
- `spawn (fn, arg)` — primitive-`Spawn` the trampoline, append a pool entry,
  return the new *user-level* index;
- `yield ()` — sanity-check that the stored thread id matches `GetTid`,
  angelically choose the next thread, update `v_tid`, and issue the primitive
  `Yield`;
- `join tid` — loop until the pool entry has a result, yielding in between
  (possibly forever).

`SchI.smod` / `SchI.t := SMod.to_mod ∅ smod`, initial state
`{[v_ths # [(0, None)]↑; v_tid # 0↑]}`, and `SchI.real : Mod.real_mod t`.

## `SchA.v` — the abstraction

**Ghost state.** `joinRA := gmap_viewUR nat (agreeR (SAny.t -d> SAny.t -d> leibnizO {n & GTerm.t n}))`
(each thread's postcondition, stored *syntactically* so it can live in an
invariant) and `newtidRA := gmap_viewUR nat (agreeR nat)` (user-level ↦
primitive thread id). Classes `schGpreS` / `schGS`, functor lists `newschΓ` /
`newschΣ`, `subG_schGpreS`.

**Predicates** (`Section SchRA`): `JoinFrag`, **`JoinHandle mtid postS`**
(a ¼ share — holding it entitles you to `join` and receive `postS`),
`JoinAuth`; `TidFrag`, **`Tid mtid stid := TidFrag mtid stid ∗ TID stid ∗ YIELD stid`**
(the right to run as thread `mtid`), `TidAuth`, `PYIP`, and `Tid_Auth_Tid`.

**`fspec_sch E fsp`** — wrap a spec so that it additionally threads
`winv (E,E)` and the `Tid mtid stid` token; `fspec_spawnable`,
`fn_spawnable`, `fspec_sch_spawnable` characterise which specs a function must
have to be `spawn`-able.

**Specs** `inner_spawn_spec`, `spawn_spec`, `yield_spec E`, `join_spec`, and
the spec map `SchA.sp E`. The abstract bodies (`inner_spawn`, `spawn`,
`yield`, `join`) are the same shape as `SchI`'s but manipulate the ghost state
instead of the concrete pool; `SchA.smod E`, `SchA.t sp`, `SchA.init_cond`,
and the allocation lemma `sch_alloc`.

**Client-side spawn.** `spawn_f fn arg fsp` (notation **`𝒮@{fn, arg, fsp}`**)
with the two simulation rules `wsim_spawn_f_src` and `wsim_spawn_f_tgt`.

## `SchIAproof.v` — `SchI ⊒ SchA`

Under `SchA.sp sp_user ⊤ ⊆ sp`, `sp_user ⊆ sp` and `sp.2` (imaginary
concurrency enabled), with `Ist` relating the abstract ghost state to the
concrete `v_ths`/`v_tid`: one lemma per function (`simF_inner_spawn`,
`simF_spawn`, `simF_yield`, `simF_join`), then `sim : ⊢ ISim.t … SchAMod SchIMod Ist`
and `ctxr` (contextual refinement via `main_adequacy`).

## `SchTactics.v` — reasoning about yields

The hardest part of using the scheduler is matching a *source* yield loop
against a *target* yield loop, since either side may spin an arbitrary number
of times. This file provides the machinery.

- `Section wsim`: `wsim_yield_tgt_rr`, `wsim_yield_tgt_ir`, `wsim_yield_i_i`,
  `wsim_yield_src`.
- `Section yield_namespace`: the namespace-annotated counterparts
  `wsim_yield_namespace_src`, `wsim_yield_namespace_ir`,
  `wsim_yield_namespace_N_N`, `wsim_yield_namespace_i_N`.
- `solve_msk` (with the goal-local fast path added in the `Unreleased`
  CHANGELOG entry), and the first-generation tactics `sYieldRR`, `sYieldIR`,
  `sYieldII`.
- `Section MSIM`: `msim_flag_src_down`, `msim_flag_tgt_down`.
- **`Section SREL`** — `srel`, a `paco4` "structural equality up to yields"
  relation between two `itree crisE`s, with one constructor per event
  (`srel_def_ret`, `_tau`, `_tau_r`, `_choose_diff`, `_choose_r`, `_choose`,
  `_take`, `_io`, `_assume`, `_assumeres`, `_guarantee`, `_call`, `_spawn`,
  `_yield`, `_get_tid`, `_sput`, `_sget`), its metatheory (`_srel_tarski`,
  `srel_def_mon`, `_srel_mon`, `_srel_mon_auto`, `_srel_flag_mon`), up-to
  closures (`srel_flagC`, `srel_eqC`, `srel_bindC`) and — crucially — the
  bridge `msim_srelC` / `msim_srelC_spec`, which lets an `srel` be consumed
  inside an `msim` proof. The payoff is **`srel_yy_y`** and
  `srel_yy_y_namespace`: *two consecutive yields are equivalent to one*.
- `Section ISIM`: `isim_yy_y`, `wsim_yy_y`, `wsim_yy_y_namespace` — the same
  collapsing, at the `isim`/`wsim` level.
- `Section proofmode`: the `tac_*` lemmas backing the tactics —
  `tac_wsim_yield_r_r`, `tac_wsim_yield_N_r`, `tac_wsim_yield_i_r`,
  `tac_wsim_yield_N_N`, `tac_wsim_yield_i_N`, `tac_wsim_yield_i_i`.
- **`sYield`** — the user tactic. It inspects which pair of yield forms
  (`𝒴`/`𝒴@{N}`, source/target) the goal has and applies the right `tac_*`
  lemma, discharging the mask side conditions with `solve_msk` and locating
  the `Ist`/`Tid` hypotheses with `iAssumptionCore`.
  Also `sYields` (iterate) and `sYieldS` (source-only).
  Since the `Unreleased` CHANGELOG entry, `sYields` requires progress and
  `sYield` introduces fresh continuation states atomically.
- A commented-out `Section RealLAT` (`wsim_lat_real_both`, `wsim_lat_real_tgt`).

## `Atomic.v` — logically atomic triples

- `fspec_winv` — a `WP` instance for `winv (E,E) ∗ P`, so the `wsim` tactics
  automatically move the world in and out.
- **`atomic_fun P body Q`** — the callee-side wrapper: `Take` a namespace `N`
  and a meta `x`, `Assume` the *private* precondition `winv (↑N,↑N) ∗ P N x`,
  run the body, `Guarantee` the *private* postcondition. Eight
  `{{{ … }}} body {{{ … }}} @ N` notations cover the presence/absence of the
  `∀∀ x`, `∀∀ x2` and `RET ret` binders.
- **`atomic_try αP αQ`** — the atomic update point itself: `Take` the public
  state `x2`, `Assume` the public precondition `αP x2`, then angelically
  `Choose` to either **abort** (re-`Guarantee` `αP x2`) or **commit**
  (`Guarantee (αQ x2 ret)`).
- **`atomic_update_sem N αP αQ := yield_namespace_iter (Some N) (λ _, atomic_try αP αQ) tt`** —
  retry the update point, yielding (and releasing `N`'s invariants) between
  attempts. Notations `<<{ ∀∀ x, αP, ∃∃ ret, αQ }>> @ N` and its three
  abbreviations; `unfold_atomic_update_sem`.
- The soundness lemmas relating these operational definitions to the
  *logical* `atomic_update`/`atomic_acc` of `iris_system/atomic.v`:
  `atomic_fun_src`, `atomic_fun_tgt`, `lais_triple_tgt_sem`,
  `atomic_i_funsem`, `atomic_i_sem`, `atomic_N_funsem`, `atomic_N_sem`,
  `atomic_N_inv_sem`, `atomic_sem_funsem`, `atomic_sem_sem`,
  `atomic_update_src_sem`; plus the yield-normalisation lemmas
  `yield_iter_prepend_yield_src`, `yield_namespace_iter_prepend_yield_src`,
  `atomic_update_sem_prepend_yield_src`.
- `Section proofmode`: `tac_wsim_yield_i_r`, `tac_atomic_N_funsem`,
  `tac_atomic_fun_tgt`, `tac_atomic_sem_funsem`.
