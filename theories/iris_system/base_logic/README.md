# `theories/iris_system/base_logic` — CRIS's own `uPred` base logic

Logical path: `CRIS.iris_system.base_logic`.

This is a fork of Iris's `iris.base_logic.upred` / `bi` / `derived` /
`proofmode` stack, specialised for CRIS. Two changes drive everything:

1. **No step-indexing.** `uPred M` is a plain, upward-closed predicate on the
   resource `M` — `uPred_holds : M → Prop` with monotonicity `x1 ≼ x2` — and
   `uPredO` is `discreteO`. Consequently the later modality `▷` is *definitionally
   the identity* (`uPred_later_def P := P`, and `later_eq : (▷ P = P)%I`), every
   proposition is `Timeless`, and `BiLaterMixin` is discharged by
   `bi_later_mixin_id`.
2. **A "strong" basic update.** `uPred_bupd_def Q x := ∃ x', ∀ yf, ✓ (x ⋅ yf) → ✓ (x' ⋅ yf) ∧ Q x'`
   — the resulting resource `x'` is chosen *before* the frame `yf`, i.e. the
   update must work uniformly for all frames. This is stronger than Iris's
   `bupd` and is what makes the frame-independent extraction lemmas
   (`bupd_ownM_update_2`, `bupd_ownM_update_3`) below provable.

The file header of `upred.v` notes that it corresponds to `IProp.v` in earlier
CRIS developments.

---

## `upred.v` — the model

**The type.** `Record uPred (M : ucmra) := UPred { uPred_holds : M → Prop; uPred_mono : … }`,
with `uPred_holds` a local coercion, `Add Printing Constructor`, and
`Params (@uPred_holds) 2`.

**OFE structure.** `uPred_equiv'` (extensional equality on *valid* resources),
`uPred_equiv_equivalence`, `uPredO := discreteO (uPred M)`, `uPred_compl`,
`uPred_cofe` (via `cofe_finite`), `uPred_proper`, `uPred_holds_ne`.

**Functor action.** `uPred_map` (along a `CmraMorphism`), `uPred_map_ne`,
`uPred_map_id`, `uPred_map_compose`, `uPred_map_ext`, `uPredO_map`,
`uPredO_map_ne`. (`uPredOF` and its contractiveness are commented out —
without step-indexing there is no recursive-domain equation to solve.)

**Entailment and connectives.** `uPred_entails`, and the sealed definitions
`uPred_pure`, `uPred_and`, `uPred_or`, `uPred_impl` (quantifying over larger
resources), `uPred_forall`, `uPred_exist`, `uPred_internal_eq`, `uPred_sep`,
`uPred_wand`, `uPred_plainly` (`P ε`), `uPred_persistently` (`P (core x)`),
`uPred_later` (the identity), `uPred_ownM` (`a ≼ x`), `uPred_bupd`. Each comes
with its `_def`, `_aux`, `_unseal` triple. `uPred_cmra_valid` is commented out
throughout — validity is expressed with pure propositions instead.

**`Module uPred_primitive`.** The `unseal` tactic plus the full set of
primitive rules, stated with local notations:
- entailment: `entails_po`, `entails_anti_sym`, `equiv_entails`;
- non-expansiveness: `pure_ne`, `and_ne`, `or_ne`, `impl_ne`, `sep_ne`,
  `wand_ne`, `internal_eq_ne`, `forall_ne`, `exist_ne`, `later_ne`,
  `plainly_ne`, `persistently_ne`, `ownM_ne`, `ownM_proper`, `bupd_ne`;
- intro/elim: `pure_intro`, `pure_elim'`, `pure_forall_2`, `and_elim_l/r`,
  `and_intro`, `or_intro_l/r`, `or_elim`, `impl_intro_r`, `impl_elim_l'`,
  `forall_intro`, `forall_elim`, `exist_intro`, `exist_elim`;
- BI: `sep_mono`, `True_sep_1`, `True_sep_2`, `sep_comm'`, `sep_assoc'`,
  `wand_intro_r`, `wand_elim_l'`;
- persistently: `persistently_mono`, `persistently_elim`,
  `persistently_idemp_2`, `persistently_forall_2`, `persistently_exist_1`,
  `persistently_and_sep_l_1`;
- plainly: `plainly_mono`, `plainly_elim_persistently`, `plainly_idemp_2`,
  `plainly_forall_2`, `plainly_exist_1`, `prop_ext_2`,
  `persistently_impl_plainly`, `plainly_impl_plainly`;
- later (all trivial): `later_mono`, `later_intro`, `later_forall_2`,
  `later_exist_false`, `later_sep_1/2`, `later_false_em`,
  `later_persistently_1/2`, `later_plainly_1/2`, `later_eq`;
- internal equality: `internal_eq_refl`, `internal_eq_rewrite`, `fun_ext`,
  `sig_eq`, `later_eq_1/2`, `discrete_eq_1`, `internal_eq_entails`;
- update: `bupd_intro`, `bupd_mono`, `bupd_trans`, `bupd_frame_r`,
  `bupd_plainly`;
- ownership: `ownM_op`, `persistently_ownM_core`, `ownM_unit`, `later_ownM`,
  `ownM_valid`, `bupd_ownM_update`, and three lemmas that deliberately break
  the abstraction (with a comment saying this is unavoidable unless the
  simulation relation itself lives inside the logic):
  `bupd_ownM_update_2` (an update from a valid resource yields a valid one),
  `bupd_ownM_update_3` (a `bupd` to a separating conjunction can be *split
  into two concrete resources*), `ownM_pure_soundness`,
  `ownM_general_soundness`;
- soundness: `pure_soundness`, `internal_eq_soundness`, `later_soundness`.

## `bi.v` — the `bi` instance

`uPred_emp := uPred_pure True`; `uPred_bi_mixin`,
`uPred_bi_persistently_mixin` (the four admissible laws are derived, not
primitive), `uPred_bi_later_mixin` (via `bi_later_mixin_id`), and the canonical
structure `uPredI (M : ucmra) : bi`.

Additional instances: `uPred_plainly_mixin` / `uPred_plainly : BiPlainly`,
`uPred_bupd_mixin` / `uPred_bi_bupd : BiBUpd`, `uPred_affine : BiAffine`
(with a `Hint Immediate`), `uPred_persistently_forall`, `uPred_pure_forall`,
`uPred_persistently_impl_plainly`, `uPred_plainly_exist_1`,
`uPred_bi_bupd_plainly`. `BiInternalEq`, `BiPropExt` and
`BiLaterContractive` are commented out (the former because internal equality
is fundamentally step-indexed).

`Module uPred` then restates, at the BI level, the `own`-specific lemmas
(`ownM_ne`, `ownM_proper`, `ownM_op`, `persistently_ownM_core`, `ownM_unit`,
`bupd_ownM_update`, `bupd_ownM_update_2`, `bupd_ownM_update_3`,
`ownM_pure_soundness`, `ownM_general_soundness`, `ownM_valid`,
`pure_soundness`, `later_soundness`, `later_eq`) and provides the unsealing
tactics `unseal`, `unseal_in`, `unseal_once`, `unseal_once_in`.

## `derived.v` — derived laws (does not unseal)

`ownM_proper`, `intuitionistically_ownM`, `ownM_invalid`, `ownM_mono`,
`ownM_unit'`, `upred_timeless` (*every* proposition is timeless — a direct
consequence of `▷ = id`), `ownM_persistent`,
`uPred_ownM_sep_homomorphism` (for `big_op`), `bupd_soundness`,
`laterN_soundness`. Then, as a demonstration: the `modality` inductive
(`MBUpd | MLater | MPersistently | MPlainly`), `denote_modality`,
`denote_modalities`, `modal_soundness` (soundness under an arbitrary nesting
of modalities, for plain propositions) and `consistency`
(`¬ ⊢@{uPredI M} False`).

## `proofmode.v` — proof-mode class instances

`from_sep_ownM`, `combine_sep_as_ownM` (cost 60, to keep
`combine_sep_as_fractional` ahead of it), `combine_sep_gives_ownM` (combining
two `ownM`s yields `⌜✓ (b1 ⋅ b2)⌝`), `from_sep_ownM_core_id`,
`into_and_ownM`, `into_sep_ownM`, and `uPred_except_0` (every proposition is
`IsExcept0`, again because `▷ = id`).

## `base_logic.v` — the umbrella module

Exports `derived` and `proofmode`, and uses the "multiple `uPred` modules"
trick (attributed in a comment to Jason Gross) to re-export
`base_logic.bi.uPred`, `derived.uPred` and `bi.bi` under one name.