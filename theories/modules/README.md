# `theories/modules` — modules, specifications, and the interpretation tower

Logical path: `CRIS.modules`.

This directory defines *what a program is* in CRIS and how the three levels of
description are compiled into one another.

```
  SMod.t                     spec module:  emask × (option fspec_rel × fbody)
    │  SMod.to_mod sp   (SModTr.trans: wrap Hoare pre/post around every call)
    ▼
  Mod.t                      module:       emask × fbody          (itree crisE)
    │  Mod.to_lmod r    (SB.sandbox: enforce the mask;
    │                    ModTr.trans: discharge agE/pgE into resources+state)
    ▼
  LMod.t                     low-level module:                     itree lmodE
    │  LMod.compile     (LModTr.trans: interleave threads, thread state)
    ▼
  itree coreE Any.t          closed program — its behaviour is Beh.of_itree
```

Every stage is a **`interpV`-based translation**, so it inserts no spurious
`Tau`s beyond the ones the semantics intends (see
[`theories/lib/ITreelib.v`](../lib/ITreelib.v)), and every stage registers a
`red_database` instance or a `SRed`/`SBRed`/`Red` module of reduction lemmas so
that `ired` can normalise it.

---

## `FSpec.v` — function specifications

- `Record fspec := fspec_mk { meta : Type; precond, postcond : meta → Any.t → Any.t → iProp Σ }`.
  Both take *two* `Any.t`s: the **virtual** (specification-level) value and the
  **physical** (implementation-level) value — CRIS is a relational framework.
- `fspec_rel := (Any.t → Any.t → iProp Σ) → (Any.t → Any.t → iProp Σ) → Prop` —
  a *relation on* pre/post pairs, which is what modules actually store; and
  `Record FSpec fsp := { Precond; Postcond; related : fsp Precond Postcond }`
  an inhabitant of such a relation. `idx_to_rel`, `fspec_to_rel` (a coercion),
  `fspec_to_rel_satisfy`, `fsp_none`, `fsp_some`, `fspec_flat`.
- Canonical specs: `fspec_trivial` (equality of virtual and physical values),
  `fspec_bot` (strongest: `True` ↦ `False`), `fspec_top` (weakest, with
  `meta := False`), and the bodies `fbody_trivial`, `fbody_ub`, `fbody_nb`.
- Builders: `fspec_simple`, `fspec_simple_typ`, `fspec_virtual`,
  `fspec_virtual_typ`, `to_physical`, `add_fspec` (sum of metas).
- `fbody := Any.t → itree crisE Any.t`.
- Physicality predicates: `fspec_physical`, `fspec_rel_physical`.
- **`fspec_imply fsp0 fsp1`** — "`fsp0` is a *stronger* spec than `fsp1`",
  formulated as an `iProp` (the file's comment derives the direction from the
  consequence rule). With `fspec_bot_strongest`, `fspec_top_weakest`,
  `fspec_imply_refl`.
- `fspec_winv E fsp` — a spec that additionally threads `winv (E, E)`.
- `Arguments precond/postcond : simpl never`.
- **Notation** (`cris_scope`): `[]`, `[x]`, `[x; y; …; z]` for iterated
  `add_fspec`, and `meta0 x` … `meta19 x` for injecting into the resulting
  nested sum of meta types.

## `Sp.v` — specification maps

`specmap := gmap fname fspec_rel * bool` — a per-function spec together with a
flag ("imaginary concurrency" — see `HoareSpawn`/`HoareYield` in `SModTr.v`,
which only wrap concurrency events when the flag is set).

`fn_has_spec_in sp f fsp` (the map contains a spec at least as strong as
`fsp`), the coercion `gmap_to_specmap`, and the `Empty`, `Union`, `SubsetEq`
instances with `specmap_subseteq_reflexive` / `_transitive`.

## `Sandbox.v` — mask enforcement

`SB.msk_default` — the events every function may always perform
(`Choose`, `Take` at propositional types, `Guarantee`, `AssumeRes`).
`SB.handle msk` passes an event through if `msk` or `msk_default` allows it,
and otherwise replaces it by `Take False` (undefined behaviour).
`SB.sandbox msk := interpV (handle msk)`; `SB.sandbox_body` applies it to a
`(emask, fbody)` pair.

`Module SBRed` gives the reduction lemmas `bind`, `tau`, `ret`, `vis`,
`assumeK`, `guaranteeK`, `unwrapUK`, `unwrapNK`, `ruK` (for `RealUpdateK`).
`sandbox_sandbox` shows sandboxing is idempotent along `msk_sub`.
Notations `░ it` (printing) and `⇓sbox( msk )` (parsing).

## `LMod.v` — low-level modules

```coq
Record LMod.t := mk { fnsems : gmap fname (Any.t → itree lmodE Any.t);
                      initial_st : lstateT }.
```
`LMod.prog` (lookup by `funid`), and `LMod.compile ms : Any.t → itree coreE Any.t`
— look up the `entry` function, run it through `LModTr.trans`, and project the
result. This is the closed program whose `Beh.of_itree` is the observable
behaviour.

## `LModTr.v` — the concurrency and state interpretation

- `pure_state`, `handle_stateE` (run an `SUpdate`), `interp_stateE` — thread
  the `lstateT` through.
- `ths_state := nat * list (itree lmodE Any.t)` — the current thread id and the
  thread pool.
- **`handle_callE prog`** — one scheduling step, as an `itreeV` so that no
  extra `Tau` is inserted for visible events. It looks up the running thread
  and dispatches on its head: `Ret` at thread 0 finishes the program (any other
  thread returning is UB); `Tau` steps; a non-`callE` event is emitted and the
  continuation stored back; and for `callE`:
  - `Call fn arg` — inline the callee's body followed by a `Tau`;
  - `Spawn fn arg` — append `bd arg` as a new thread, returning its index;
  - `Yield tid'` — switch the current thread to `tid'`;
  - `GetTid` — return the current thread id.
- `interp_callE prog itr := iterV (handle_callE prog) (0, [itr])` and
  `LModTr.trans prog itr st := interp_stateE (interp_callE prog itr) st`.

## `ModTr.v` — discharging separation-logic obligations into state

This is where the `agE` (`Assume`/`AssumeRes`/`Guarantee`) and `pgE`
(`SPut`/`SGet`) events of `crisE` become concrete operations on the low-level
state `lstateT`, whose second component holds the *resource* `Σ` (as an
`Any.t`).

- Resource plumbing: `put_res`, `get_res`; key-value plumbing: `put_kv`,
  `get_kv`, `handle_pgE`.
- `handle_Assume P` — `Take` a new resource `mr'` and `assume (✓ mr' ∧ (Own mr' ⊢ |==> P ∗ Own mr))`;
  i.e. the environment must hand over a resource that can be split into `P` and
  the old one.
- `handle_AssumeRes r` — `assume (✓ (r ⋅ mr))` and add `r`.
- `handle_Guarantee P` — dually, `Choose` `mr'` and `guarantee (✓ mr' ∧ (Own mr ⊢ |==> P ∗ Own mr'))`.
- `handle_agE`, `handle_crisE`, `ModTr.trans := interpV handle_crisE`,
  `ModTr.trans_fnsem`.
- `Module Red` — reduction lemmas `bind`, `tau`, `ret`, `call`, `spawn`,
  `yield`, `pg`, `core`, `triggerUB`, `triggerNB`, `unwrapU`, `unwrapN`,
  `Assume`, `AssumeRes`, `Guarantee`, `ext`, and the `red_database` instance
  `rdb` for `ModTr.trans`.

## `Mod.v` — modules

The central data type of the framework.

```coq
Record Mod.t := mk {
  scopes     : list string;
  fnsems     : gmap fname (option (emask * fbody));
  initial_st : gmap key (option Any.t);
  sorted_scopes; well_scoped_fns; well_scoped_init; nodup_init }
```

The maps are `option`-valued so that **linking is total**: `uwnd _ _ := Some None`
maps a name defined in both modules to `None` ("conflicting"). Scopes are kept
`merge_sort`ed so that linking is *definitionally* commutative. The three proof
fields require that a function's mask only touches keys in the module's scopes,
that the initial state only mentions those scopes, and that (given `NoDup`
scopes) every initial cell is defined.

- `Mod.wf` = every `fnsems` entry is `Some` (no conflicts) and `scopes` is
  duplicate-free.
- `Mod.empty` (notation `⌽`) and `Mod.add` (notation **`★`**, right
  associative), `Mod.addL`, with `t_eq` (extensionality via proof irrelevance),
  `add_comm`, `add_wf`, `add_wf_inv`, `dom_fnsems_add`, `maxlen_scopes_add`,
  `lookup_add_l`, `lookup_add_r`, `mod_dom_subseteq`; and in `ModFacts`
  `mod_add_assoc`, `mod_add_empty_l`, `mod_add_empty_r`, registered as the
  `Comm`/`Assoc`/`LeftId`/`RightId` instances `_mod_add_comm`,
  `_mod_add_assoc`, `_mod_left_id`, `_mod_right_id`. So `(Mod.t, ★, ⌽)` is a
  commutative monoid *up to Leibniz equality*.
- `Mod.to_lmod ms r` — sandbox each body, translate it with `ModTr.trans_fnsem`,
  and pair the initial key-value store with the initial resource `r`.
  `to_lmod_fnsems`.
- `real_mod md` — the module performs no `Assume` and only takes at
  propositional types (i.e. it is an *implementation*, not a specification);
  `real_mod_add`.
- A block of generic `union_with uwnd` lemmas: `dom_union_with`,
  `map_Forall_union_with_inv_gen`, `map_Forall_union_with_inv`,
  `map_Forall_union_with`, `lookup_union_with_l`, `lookup_union_with_r`,
  `insert_union_with_l'`, `insert_union_with_r'`,
  `map_Forall_insert_union_with`; then their `Mod`-specific instances
  `lookup_fnsems_inv`, `lookup_fnsems_l`, `lookup_fnsems_l_2`,
  `lookup_fnsems_r`, `lookup_fnsems_r_2`, `lookup_fnsems_None_l`,
  `lookup_fnsems_None_r`, `lookup_fnsems_l2`, `lookup_fnsems_r2`,
  `lookup_fnsems_None`.
- Automation: `mod_tac1` / `mod_tac` (discharge the four record obligations),
  `scope_solver`, `_real_mod_solver` / `real_mod_solver`, `mod_eq_solver`
  (normalise a `★`-expression up to AC), `unfold_fnsem`, and a set of
  `Hint Extern`s in the **`simpl_map`** database that resolve
  `Mod.fnsems (_ ★ _) !! _ = _` goals. `Mod.add` and `Mod.fnsems` are
  `simpl never`.

## `SMod.v` — specification modules

```coq
Notation fnsemmap := gmap fname (option (emask * (option fspec_rel * fbody))).
Record SMod.t := mk { scopes; fnsems : fnsemmap; initial_st; … }
```
Same shape as `Mod.t`, but each function additionally carries an optional
specification. Parameterised by `crisG` (so `winv` etc. are available).

- `t_eq`, `is_real` (no function has a spec), `empty`, `add` (notation
  **`☆`**), `add_comm`, `addL`.
- **`to_mod sp ms : Mod.t`** — replace each `(fspo, fbd)` by
  `SModTr.trans_fnsem sp (fspo, fbd)`, i.e. wrap the body in its Hoare
  pre/post and every call in a Hoare call. `to_mod_add`, `to_mod_addL`.
- **`to_mod_cancel sp ms`** — the same but using `SModTr.trans_cancel`, which
  passes the function's own mask to the translation. `to_mod_cancel_add`.
- `update_spec f ms` (map a function over every spec), `filter mskF ms`
  (intersect every mask with `mskF msk`) with `filter_add`,
  `cancel ms` (drop every spec) with `cancel_add`.
- `sp_core_from md` / `sp_from md` — read the module's own specs back out as a
  `specmap` (with the concurrency flag set), with `sp_core_from_lookup`,
  `sp_core_from_add_lookup`, and `lookup_sp_from`.
- `cancellable ms` — every mask satisfies `img_msk` and `call_msk`, which is
  what the cancellation transformation in
  [`../cancellation/`](../cancellation/) requires; `cancellable_add`.

## `SModTr.v` — the Hoare-wrapping translation

`fnsem := emask * (option fspec_rel * fbody)`.

- **`HoareFun fspo body`** — the callee side. With a spec: `Take` an
  `FSpec fsp` and a virtual argument, `Assume` the precondition, run the body,
  `Choose` a physical return value, `Guarantee` the postcondition. Without a
  spec: just `tau;; body arg`.
- **`HoareCall fspo omsk fn varg`** — the caller side, dual: `Choose` the
  `FSpec` (degraded to `fspec_trivial` if the optional mask `omsk` rejects this
  call), `Choose` a physical argument, `Guarantee` the precondition, perform
  the `Call`, `Take` a virtual result, `Assume` the postcondition.
- **`HoareSpawn`**, **`HoareYield`**, **`HoareGetTid`** — the concurrency
  counterparts, active only when the `specmap`'s boolean flag ("imaginary
  concurrency") is set. They trade the `TID`/`YIELD` tokens and `winv (⊤,⊤)` of
  [`../common/ConcRA.v`](../common/ConcRA.v) across the scheduling point.
  `omask_check` decides whether a given event is in the optional mask.
- `SModTr.handle sp omsk`, `_trans sp omsk := interpV (handle sp omsk)`,
  `trans sp := _trans sp None`, `trans_fnsem`, `trans_cancel` (which passes the
  function's own mask as `omsk`). `trans_fnsem` is `simpl never`.
  Notations `↧ it` (printing) and `⇓smod( sp )` (parsing).
- `Module SRed` — two parallel sets of reduction lemmas, one for `_trans`
  (prefixed `_`) and one for `trans`: `bind`, `tau`, `ret`, `vis_agE`,
  `vis_pgE`, `vis_coreE`, `vis_call`, `vis_spawn`, `vis_yield`, `vis_gettid`,
  `assumeK`, `guaranteeK`, `unwrapUK`, `unwrapNK`, plus the `trigger`-form
  versions `yield`, `spawn`, `gettid`, `call`, `pg`, `core`, `ag`, and
  `ru` / `ruK` for `RealUpdate`.
