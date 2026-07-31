# `theories/simulations/msim` — module simulation, its Iris embedding, and the tactics

Logical path: `CRIS.simulations.msim`.

This is where CRIS proofs are actually written. Three layers, each a
refinement of the previous:

| Layer | Type | Purpose |
| --- | --- | --- |
| **`msim`** ([`MSim.v`](MSim.v)) | a `paco8` relation on `Σ → Prop` | the raw coinductive simulation, defined *outside* the logic |
| **`isim`** ([`ISim.v`](ISim.v)) | an `iProp Σ` | the same relation packaged as a separation-logic proposition |
| **`wsim`** ([`WSim.v`](WSim.v)) | `winv Ep -∗ isim …` | `isim` with the world/invariant bundle threaded, so `iInv`, fancy updates and masks work |

The user-facing tactics ([`Tactics.v`](Tactics.v)) dispatch on which of the
last two is in the goal, so the same `cStep`/`cCall`/`cCoind` script works at
both levels.

---

## `MSimCommon.v` — shared vocabulary

- `Variant contextuality := open | closed` — whether the module is being
  related in an arbitrary context (`open`, calls to unknown functions must be
  simulated) or as a whole program (`closed`, calls to undefined functions are
  vacuous).
- Type abbreviations `ist_type Σ` (a relation between the source and target
  key-value states, as an `iProp`), `retr_type Σ Rs Rt` (state × return value
  on both sides), `msim_type Σ Rs Rt` (the shape of the simulation relation:
  two progress flags, two `state × itree` pairs, and a resource).
- State-invariant combinators: `IstProd` (split the state along a module
  decomposition), `IstSB scopes Ist` (restrict to a scope set), `IstEq`
  (the two states are equal), `IstTrue`, `IstFalse`, and `ist_with_eq Ist`
  (the standard return relation: equal return values plus `Ist`).
- `submseteq_NoDup`.

## `MSim.v` — the coinductive simulation

**The `hsupd` "resource may be updated first" modality.**
`hsupd P fmr := ✓ fmr → ∃ fmr0, P fmr0 ∧ (Own fmr ⊢ |==> Own fmr0)`. A comment
explains why it is stated this way rather than as an `iProp`: an
`iProp`-valued definition would make `_msim` fail the positivity check.
Lemmas: `hsupd_mon`, `hsupd_incl`, `hsupd_merge`, `hsupd_update`,
`hsupd_extends`, `hsupd_wf`.

**`_msim'`** — the step relation, parameterised by the *coinductive*
continuation `msimc` (used only by `msim_progress`) and the *inductive* one
`msimi`. Its 24 constructors:
`msim_ret`, `msim_call` (both sides call the same function: the resource must
split into `Ist st_src st_tgt` and a frame `FR` that is handed back
afterwards), `msim_io`, `msim_inline_src` / `msim_inline_tgt` (replace a call
by the callee's body followed by a `Tau`), `msim_tau_src` / `_tgt`,
`msim_take_src` (∀) / `msim_choose_tgt` (∀) — the *demonic* side —
`msim_choose_src` (∃) / `msim_take_tgt` (∃) — the *angelic* side —
`msim_sput_src` / `_tgt`, `msim_sget_src` / `_tgt`, `msim_assume_src`,
`msim_assume_res_src`, `msim_guarantee_tgt`, `msim_guarantee_src`,
`msim_assume_tgt`, `msim_assume_res_tgt`, `msim_spawn`, `msim_yield` (same
resource protocol as `msim_call`), `msim_gettid`, `msim_call_none` /
`msim_spawn_none` (only in the `closed` setting: calling an undefined function
is vacuously simulated), and `msim_progress` (the only place the coinductive
knot is used — allowed only when both progress flags are `true`).

**`_msim`** wraps `_msim'` in the well-formedness side conditions
(`fl_src`, `fl_tgt`, and both states must be conflict-free) and in `hsupd`;
`msim := paco8 _msim bot8`.

**Metatheory.** `_msim_tarski` (the induction principle for the *inner*
inductive fixed point), `_msim'_mon`, `_msim_mon`, `_msim_mon_auto`,
`_msim_flag_mon`, `msim_flag_mon`, `msim_progress_flag`.

**Up-to closures** (each with a `_mon`, a
`compatible8`/`wrespectful8` proof, and a `_spec` lemma into
`gupaco8 _msim (cpn8 _msim)`):
- `msimC` — take one step;
- `msim_flagC` — weaken the progress flags;
- `msim_bindC` — the bind rule;
- `msim_extendC` — enlarge the resource (`fmr ≼ fmr'`);
- `msim_wfC` — assume the resource is valid;
- `msim_updateC` — update the resource first (`hsupd`);
- `msim_frameC` — **frame** an `iProp` `CTX` around the whole simulation (the
  longest proof in the file: every constructor's resource discipline has to be
  re-established with the frame present);
- `msim_nodupC` — assume the well-formedness side conditions.

## `MSimFacts.v`

`msim_ist_frame` — frame a proposition `P` into *both* the state invariant and
the return relation.

## `MSimAdequacy.v` — from `msim` to `lsim`

Bridges the module-level simulation to the low-level thread-pool simulation of
[`../lsim/`](../lsim/).

- `own_upd_in_middle`, `ctx_sem ctx := [^(⋅) list] r ∈ ctx, r` — the resources
  owned by the other threads.
- **`interp_inv Ist`** — the world relation: `mr_src` is valid and can be
  updated into `ctx_sem ctx ⋅ mr ⋅ mr_tgt`, where `mr` satisfies the state
  invariant. `IstWorld Ist` packages it as an `LWorld` (with `wle := eq`).
- Thread-context bookkeeping: `ctx_set`, `ctx_add`, `ctx_set_sem`,
  `ctx_add_sem`, `le_mine_in`, `ctx_set_le_others`, `ctx_le_mine_sem`.
- **`msim_adequacy`** — `msim closed … ⊢ lsim …` (a comment notes adequacy
  requires `contextuality = closed`). One case per `_msim'` constructor.

## `FnsemLookup.v` — typeclass-driven function lookup

Computing `Mod.fnsems (A ★ B ★ …) !! fn` by `simpl` is prohibitively slow, so
lookups are resolved by *certificate search* in a dedicated, deliberately
opaque hint database.

- `Create HintDb fnsem_lookup` with `Hint Variables/Constants/Projections Opaque`
  and only `Mod.fnsems`, `SMod.fnsems` transparent. The header comment
  explains the discipline: extensions must register their instances here so
  unsupported heads stay opaque, and recursive builders must use
  `notypeclasses refine` so their premises are left to the enclosing search.
- `Class MapLookupResult m k result` for concrete leaf maps, with instances
  `map_lookup_result_empty`, `map_lookup_result_insert_hit` (cost 5),
  `map_lookup_result_insert` (cost 10).
- `Class FnsemLookupResult m fn result` for composed modules, with
  `fnsem_lookup_result_add` (for `★`, cost 10) and
  `fnsem_lookup_result_to_mod` (for `SMod.to_mod`, cost 30).
- Matching `Hint Extern`s that build the instances with `open_constr`
  placeholders and `notypeclasses refine`.

(`ISim.v` adds `sandbox_fnsemmap` and `fnsem_lookup_result_sandbox` to the same
database.)

## `ISim.v` — the simulation as a separation-logic proposition

**Construction.** `rel` is the type of "coinduction hypotheses" as `iProp`s;
`iunlift g` turns such a hypothesis back into a `Prop`-level relation
(requiring the resource to be valid and to entail `g`);
`ibot := λ …, False`. Then

```coq
isim g RR ps pt sti_src sti_tgt : iProp Σ :=
  UPred Σ (gpaco8 _msim (cpn8 _msim) bot8 (iunlift g) _ _ RR ps pt sti_src sti_tgt) _
```

— the `uPred` whose model is literally "this resource makes the simulation
hold". Monotonicity is discharged by `msim_extendC`. `isim` is `Opaque` after
the section.

**Interface lemmas.** `iunlift_ibot`, `isim_init` (enter the model),
`isim_final` (leave it), `iunlift_mon`, `isim_mono_knowledge`, `isim_mono`,
`isim_nodup_src` / `_tgt`, `isim_upd` and the `ElimModal` instance
`isim_elim_upd`, `isim_wand`, `isim_frame`, `isim_bind`.

**Simulation rules** — one per `_msim'` constructor, but now stated as
entailments so they can be applied with `iApply`:
`isim_ret`, `isim_tau_src` / `_tgt`, `isim_io`,
`isim_take_src` / `isim_take_tgt` / `isim_choose_src` / `isim_choose_tgt`
(and the `_fspec` variants, which pre-destruct the `FSpec` record so the user
sees the meta argument directly),
`isim_asm_src` / `_tgt`, `isim_guar_src` / `_tgt`,
`isim_sput_src` / `_tgt`, `isim_sget_src` / `_tgt`,
`isim_assume_src` / `isim_assume_res_src` / `isim_assume_tgt` /
`isim_assume_res_tgt`, `isim_guarantee_src` / `_tgt`,
`isim_triggerUB_src`(`_trigger`), `isim_triggerNB_tgt`(`_trigger`),
`isim_unwrapU_src` / `isim_unwrapN_src` / `isim_unwrapU_tgt` /
`isim_unwrapN_tgt`, `isim_call`, `isim_inline_src` / `_tgt`, `isim_spawn`,
`isim_yield`, `isim_gettid`, `isim_call_none`, `isim_spawn_none`,
`isim_reset`, `isim_progress`, `isim_flag_mon`, and **`isim_coind`** — the
Löb-style coinduction principle, which is what `cCoind` applies.

**`Section FancyReal`** — the rules for `RealUpdate` (the prophecy epilogue
from [`../../common/Events.v`](../../common/Events.v)):
`isim_ru_src_advanced_general`, `isim_ru_src_advanced`,
`isim_ru_src_general`, `isim_ru_src`, `isim_ru_tgt_general`, `isim_ru_tgt`,
`isim_ru_tgt_simple_general`, `isim_ru_tgt_simple`. The source-side rules
require the extracted proposition to be `precise` (see
[`../../iris_system/precise.v`](../../iris_system/precise.v)).

**Module-level statements.**
`isim_fsem fl_src fl_tgt Ist ctx fs ft` — persistently, for every argument and
pair of related states, the two function bodies are `isim`-related.
`sandbox_fnsemmap` (apply `SB.sandbox_body` to a whole `fnsems` map) with its
`FnsemLookupResult` instance and a `simpl_map` hint.
`Module ISim`: **`ISim.sim_fun fn`** (for each source function there is a
target function with the same name, and the two are `isim_fsem`-related) and
**`ISim.t`** — the top-level statement:
```coq
ISim.t ctx ms mt Ist := ⌜Mod.wf mt⌝ →
  ⌜scopes ms ⊆+ scopes mt ∧ map_Forall (const is_Some) (fnsems ms)⌝
  ∧ Ist (initial_st ms) (initial_st mt) ∗ ∀ fn, sim_fun fn.
```
(Since the `Unreleased` CHANGELOG entry, `sim_fsem`, `ISim.sim_fun` and
`ISim.t` are all `iProp`s.)

## `ISimFacts.v`

- `isim_ist_frame` — the `iProp` counterpart of `msim_ist_frame`.
- **`isim_refl`** — reflexivity: a sandboxed tree is simulated by itself,
  provided the state invariant is preserved by the writes and determines the
  reads that the mask allows. Proved by `isim_coind` and a case analysis via
  `case_itrH`.
- `isim_reflL` / `isim_reflR` — reflexivity for one side of an `IstProd`
  decomposition (the other side's scopes must be disjoint from the mask's
  footprint).
- `ISim_refl` (`⊢ ISim.t ctx M M IstEq`), and **`ISim_reflL` / `ISim_reflR`** —
  the *horizontal compositionality* results: to prove
  `C ★ A ⊑ C ★ B` (resp. `A ★ C ⊑ B ★ C`) it suffices to prove the functions
  of `A` and let reflexivity handle `C`.
- A large commented-out `Section LAT` about `lat_img` / `lat_real`.

## `ISimAdequacy.v`

`ISim_wf` (`ISim.t` transfers well-formedness from target to source),
`ISim_dom` (the source's function domain is contained in the target's), and
**`ISim_adequacy` : `ISim.t closed ms mt Ist ⊢ lsim_mod ms mt`** — the
composition of `msim_adequacy` with the module-level packaging.

## `WSim.v` — `isim` plus the invariant world

**`Class WP P`** — a typeclass that decomposes a proposition into a world
component and a remainder: `P ∗-∗ winv (WP_space, WP_space) ∗ WP_remainder`.
Instances: `WP_refl`, `fspec_winv_precond`, `fspec_winv_postcond`. This is what
lets the `Assume`/`Guarantee` tactics automatically move `winv` in and out of
the mask.

**`wsim fl_s fl_t Ist Ep g RR ps pt st_s st_t := winv Ep -∗ isim open …`**
(sealed). Note it always uses `open` contextuality.

The whole `isim` rule set is mirrored: `wsim_ret`, `wsim_call`, `wsim_io`,
`wsim_tau_src`/`_tgt`, `wsim_inline_src`/`_tgt`, `wsim_take_src`(`_fspec`),
`wsim_take_tgt`(`_fspec`), `wsim_choose_src`(`_fspec`),
`wsim_choose_tgt`(`_fspec`), `wsim_sput_src`/`_tgt`, `wsim_sget_src`/`_tgt`,
`wsim_assume_src`, `wsim_assume_res_src`, `wsim_assume_tgt`,
`wsim_assume_res_tgt`, `wsim_guarantee_src`/`_tgt`, `wsim_spawn`,
`wsim_yield`, `wsim_gettid`, `wsim_reset`, `wsim_progress`, `wsim_flag_mon`,
`wsim_coind`, `wsim_frame`, `wsim_bind`.

**Mask-aware rules** built on `WP`: `wsim_guarantee_src_WP`,
`wsim_assume_src_WP`, `wsim_assume_tgt_WP`, `wsim_guarantee_tgt_WP` — giving
away a `winv (E,E)` shrinks the ambient mask, receiving one grows it.

**Derived / structural.** `wsim_unwrapU_src`, `wsim_unwrapN_src`,
`wsim_asm_src`/`_tgt`, `wsim_guar_src`/`_tgt`, `wsim_mono_knowledge`,
`wsim_mono`, `wsim_nodup_src`/`_tgt`, `wsim_init_winv`,
**`wsim_fupd`** (eliminate a fancy update, bumping the world level as needed),
`wsim_own_upd`, `wsim_upd`; the proof-mode instances
`wsim_elim_own_upd`, `wsim_elim_upd`, `wsim_elim_fupd_gen` (cost 10),
`elim_fupd_wsim_same_mask`, `elim_fupd_wsim_simple`,
`wpsim_add_modal_FUpd`; and the conversions `wsim_isim`, `isim_wsim`,
`wsim_unfold`, `wsim_fold`. Outside the section: `wsim_consequence`,
`wsim_bind_strong`, and a `FancyReal` section mirroring the eight
`isim_ru_*` rules.

## `WSimFacts.v`

Currently only a commented-out `Section LAT` (the `wsim` counterparts of the
commented-out `isim_lat_*` lemmas).

## `SimNotations.v` — display notations

- `m1 +# m2` for `union_with uwnd m1 m2`.
- `{[ k1 # a1 ; … ; k20 # a20 ]}` — literal `gmap … (option _)` maps
  (20 arities), used for module `fnsems`/`initial_st`.
- `{[ k1 @ a1 ; … ; k20 @ a20 ]}` — literal `gmap fname fspec_rel` maps,
  applying `fspec_to_rel` to each entry (20 arities).
- Printing notations laying the goal out as
  `<intuitionistic context> □ / <spatial context> ∗ / st_src / st_tgt / ---isim--- / itr_src / itr_tgt { RR }`,
  in all four empty/non-empty combinations, plus variants for a goal of the
  form `P ∗ ISIM` or `P -∗ ISIM`; and the same eight-way family for `wsim`
  (which additionally displays the parameters `Ew E g ps pt`).

## `TacticsCommon.v` — normalisation infrastructure

- Small helpers: `cong`, `string_app_inv`, `inv_string`, `prove_nodup`,
  `prove_precise`, `ereplace`, `move_aux`, `fnsems_nodup`, `clear_st`,
  `simpl_sp`, `iIntrosFresh`, `des_pairs`, `set_marker`, `hide_ihyps`,
  `only_itree_s` / `only_itree_t`, `show_itree`, `show_until`,
  `prove_sub_perm`, `prove_sb_cond`, `unfoldPrePost(_term)`.
- Coinduction plumbing: `combine_quant`, `combine_quant_dep`,
  `destruct_quant`, `destruct_quant_dep`, and the tactics `combine_quant` /
  `destruct_quant` that pack a coinduction hypothesis's quantifiers into one
  (dependent) pair and unpack them again.
- `CRIS` (a seal key), `unfold_mod`, `unfold_cris_defs`.
- **Head normalisation.** The file documents the grammar it works with (itree
  terms, ktree terms, *stuck* terms, and *head-normal* terms). `red_bind`,
  `red_SB`, `red_S` push one interpreter layer through one head constructor;
  `msk_solve` decides a mask test; `_hnorm_itr` and `hnorm_itr` drive them
  recursively, unfolding `trigger`, `assume`, `guarantee`, `unwrapU`/`N`,
  `RealUpdate`, `HoareCall`, `fbody_trivial`, `cput`, `cgetU`/`cgetN`,
  `cfunU`/`cfunN`, `ccallU`/`ccallN`, `triggerUB`/`NB`.
- `replace_s` / `replace_t` and the user-level **`cNormS` / `cNormT`**
  (head-normalise the source / target tree in the goal) and
  `cNormInlineS` / `cNormInlineT`.
- **Certificate-based lookup driver.** `fnsem_lookup_outer_head`,
  `fnsem_lookup_replace_outer_head`, `fnsem_lookup_delta_outer_once(_opt)`,
  `fnsem_lookup_has_module_arg`, `fnsem_lookup_has_map_arg`, and the mutually
  recursive `fnsem_lookup_normalize_module_args` /
  `fnsem_lookup_normalize_map_args` / `fnsem_lookup_normalize_module` /
  `fnsem_lookup_normalize_map`, which expose module aliases *structurally*
  (one delta step at a time, keeping fix/iota reduction out) before handing
  off to `typeclasses eauto with fnsem_lookup`. `rewrite_fnsem_lookup`,
  `prove_inline_cond` (with the `simpl_map` fallback).
- Legacy `alist`-based tactics (`alist_find_simpl`, and a commented-out
  `alist_upd_simpl`).

## `ITactics.v` — tactics for `isim` goals

Step tactics `_istep_s` / `istep_s` / `isteps_s` (source: `Tau`, `Take`,
`Assume`, `AssumeRes`, `assume`), `_istep_t` / `istep_t` / `isteps_t`
(target: `Tau`, `Choose`, `Guarantee`, `guarantee`), `_istep` / `istep`
(both sides: `Ret`, `IO`, `GetTid`, `Spawn`).
"Force" tactics, which *commit* to a witness on the angelic side:
`iforce_s` / `iforces_s` (source `Choose`, `Guarantee`, `unwrapN`) and
`iforce_t` / `iforces_t` (target `Take`, `Assume`, `assume`, `unwrapU`,
`AssumeRes`, `RealUpdate`).
Inlining: `iinline_s` / `iinline_t`.
Structured steps: `icall … as (vret st_src st_tgt) IST`, `ispawn as (ntid)`,
`iyield … as (st_src st_tgt) IST`, `ibind`, `iby_coind CIH`,
`iIst IST with H`.

## `WTactics.v` — tactics for `wsim` goals

- Symbolic map reasoning, needed because module states are built from
  `union_with`/`insert`/`singleton`: `is_key_in`,
  `solve_map_lookup_symbolic`, `state_lookup_simpl`, `state_insert_simpl`
  (with a TODO about its complexity), `simpl_set`.
- The `wsim` mirror of `ITactics`: `_wstep_s`/`wstep_s`/`wsteps_s`,
  `_wstep_t`/`wstep_t`/`wsteps_t`, `_wstep`/`wstep`,
  `wforce_s`/`wforces_s`, `wforce_t`/`wforces_t`, `winline_s`/`winline_t`,
  `wcall`, `wspawn`, `wyield`, `wby_coind`, `wbind`, `wIst`.
  The `Assume`/`Guarantee` cases first try the `WP` typeclass (via
  `tcsearch` from [`../../lib/ltac2_lib.v`](../../lib/ltac2_lib.v)) so the
  mask is adjusted automatically, falling back to the plain rule.
  `SPut`/`SGet` cases additionally derive the no-conflict side condition with
  `wsim_nodup_src`/`_tgt`.

## `Tactics.v` — the user-facing `c*` tactics

`iwcase itac wtac` dispatches on whether the goal is an `isim` or a `wsim`.
Everything below is defined once and works at both levels.

- Simplification: `copset_diff_union`, `copset_union_diff`, `cSimpl_copset`,
  `cSimpl_des`, and **`cSimpl`** (clears trivial hypotheses, normalises
  `Any`/`SAny` up/downcasts and pairs, simplifies `coPset` arithmetic,
  `simpl_sp`, `move_aux`).
- Tree surgery: `prependRetS`/`prependRetT`, `appendRetS`/`appendRetT`,
  `unfoldIterS`/`unfoldIterT`, `unfoldIterCS`/`unfoldIterCT`.
- **Goal folding.** `cris_r`, `cris_s`, `cris_t` are identity wrappers used to
  *hide* the return relation and the two continuations behind local
  definitions so that goals stay readable; with the lemmas
  `abstract_ret_rel(_gen)`, `abstract_cont_src(_gen)`, `abstract_tau_src(_gen)`,
  `abstract_cont_tgt(_gen)`, `abstract_tau_tgt(_gen)` and the tactics
  `cShowR`/`cHideR`, `cShowS`/`cHideS`, `cShowT`/`cHideT`.
- **Main tactics:** `cStepS`, `cStepT`, `cStepsS`, `cStepsT`, `cStep`
  (`as pat`), `cForceS` / `cForceT` (with an optional witness), `cForcesS` /
  `cForcesT`, `cInlineS` / `cInlineT`, `cCall`, `cSpawn`, `cYield`, `cBind`,
  `cIst`, `cByCoind`, and **`cCoind CIH g LEg with x1 … xn`** for
  0–19 generalised variables (each arity packs the variables into a nested
  pair with `combine_quant` before applying `isim_coind`/`wsim_coind`).

## `TacticsInit.v` — starting a proof

- `rewrite_fnsem_lookup_in` — resolve a lookup *inside a hypothesis*, with the
  `fnsem_lookup_normalize_map` fallback.
- **`cStartModSim`** — begin a proof of `ISim.t`. First tries `ISim_reflR`
  (so that only the changed sub-module has to be proved); otherwise unfolds
  `ISim.t` by hand, discharges the scope/`NoDup` obligations with `mod_tac`,
  and splits into the initial-state goal and the per-function goal, with the
  functions outside the source's domain closed automatically.
- **`cStartFunSim`** — begin a proof of `ISim.sim_fun`: resolve the source
  function body by certificate lookup, produce the target body, discharge the
  lookup side condition with `prove_inline_cond`, introduce the argument and
  the two states, switch to `wsim` with `wsim_isim`, and unfold
  `SB.sandbox_body`, `SModTr.trans_fnsem`, `SModTr.HoareFun`, `cfunU`/`cfunN`.
