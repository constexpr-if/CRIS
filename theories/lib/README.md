# `theories/lib` — General-purpose Coq/Rocq support library

Logical path: `CRIS.lib`.

This directory is the foundation layer of CRIS. It contains no CRIS-specific
semantics; everything here is generic infrastructure: classical axioms, tactic
libraries, list/association-list utilities, a universal (`Any`) type, generic
coinductive containers, a stratified syntax framework, ITree helpers, and a
proof mode for `PROP`-enriched preorders.

Dependency order (roughly): `sflib` → `StdAxioms` → `Coqlib` → {`AList`, `Any`,
`SubPerm`, `LAuto`, `ITreelib`, …}; `SAT`, `exco`, `exco_stream`, `Red`,
`ltac2_lib`, `BiEnrichedProset` are largely independent.

---

## `sflib.v` — Software Foundations Laboratory tactic library

The base tactic library (ported from Viktor Vafeiadis / Gil Hur's `sflib`).
Internal symbols are prefixed `sflib__`. Contents:

**Bounded repetition combinators.** `hrepeat_or_fail tac` is a 49-deep
`tryif`-nesting that replaces Ltac's `repeat` (it fails if the tactic can be
applied more than 49 times, which catches runaway loops); `hrepeat tac` is its
`try`-wrapped variant. `tryany tac1 tac2` runs `tac2` after an optional `tac1`.
All the `repeat`-like tactics below are built on `hrepeat`.

**Congruence/rewriting scaffolding.** `eq_ind_1` … `eq_ind_20` (rewrite the
first of up to 20 arguments of a predicate) with the corresponding
`evar_at_last_N` tactics; `f_equal6`, `f_equal7`, `f_equal8`; `rpapply_raw`,
`rpapply`, `leftest_rpapply` (apply a lemma up to congruence of the leftmost
head function), plus the helper predicates `is_applied_function`,
`has_inside_strict`, `is_inside_others_body`, `on_leftest_function`,
`is_type`, `is_term_applied_function`, `on_leftest_function_with_type`.
`under_binder tac` runs a tactic beneath a binder via functional extensionality.

**Boolean coercion.** `Coercion is_true : bool >-> Sortclass` together with
`sflib__true_is_true`, `sflib__not_false_is_true`, `sflib__negb_rewrite`,
`sflib__andb_split`.

**Closing goals.** The `HintDb sflib`, `sflib__basic_done`, `done`, `edone`,
`sfby tac`, `esfby tac`.

**Clarification / simplification.** `sflib__complaining_inj`,
`sflib__clarify1`, `clarify` (injections + discriminations over all
hypotheses), `inv`, `hinv`/`hinvc` (1–5 arguments), `simpls`, `ins`,
`sflib__clarsimp1`, `clarsimp`, `autos`, `clarassoc`, `sflib__hacksimp1`,
`hacksimp`, `clean` (drops `True` and trivial equalities, with an evar guard),
`simpl_proj`, `simpl_bool`, the `simpl_bool` rewrite hint database
(`andb_true_iff`, `orb_*`, `negb_*`, …).

**Named conjuncts (`NW`).** `NW A (P : () -> A)` plus the `<< x : t >>` /
`<< t >>` notations let a conjunct carry the name its hypothesis should get.
`unnw`, `rednw`. The destructors `des1`, `des`, `desc`, `nbdes1`, `nbdes`,
`rrnbdes`, `rdes`, `rrdes` (1–4 args), `desf`, `isd`, `des_safe`, and the
`hdes` family (`hdesHi`, `hdesHP`, `hdesH`, `hdesF`, `rhdes`, `rrhdes`) which
splits conjunctions/iffs *under* leading `forall`s (up to 20 binders).
`all_conj_dist`. `forall_split`, `_HID_`.

**Case analysis on `if`/`match`.** `des_if`, `des_ifH`, `des_ifs`,
`des_ifs_safe_aux` / `des_ifs_safe`.

**Case delineation.** `assert_eq`, `Case_aux`, `Case`, `SCase`, `SSCase`,
`SSSCase`, `SSSSCase`, plus the lightweight `-`, `+`, `*`, `:` case markers.

**Hypothesis exploitation.** `exploit` (up to 34 underscores), `mp`, `mp'`,
`hexploit`, `hexploit'`, `special`, `set_prop`, `eappleft`, `eappright`,
`dup`.

**Induction / destruction.** `induction [ys] x [z]`, `induct`, `ginduction`,
`greflgen`, `gen X1..X10`, `depgen`, `destructs`/`edestructs`/`depdes`
(1–10 arguments), `revert_until`, `on_last_hyp`, `revert1`, `clear_upto`.

**Guards and marks.** `__guard__`, `__GUARD__`, `guard`, `guardH`, `sguard`,
`unguard`, `unguardH`, `unsguard`, `desH`; `__mark__` with `M`, `Mdo`,
`Mskip`, `Mfirst … ;; …`.

**Splitting and misc.** `splits`, `esplits` (also handles `sig`, `sigT`,
`prod`), `replace_all`, `extensionalities` (0–6 names), `ex`, `inst_pairs`,
`abstr`, `lhs`/`rhs`/`lhs3`/`rhs3`, `safe`, `ren`, `econsby`, `econs`,
short aliases `i`, `ii`, `s`, `ss`, `r`, `rr`, `uf`, `patout`, `fold_in`,
`fold_all`, `clears`, `all`, `rev_all`, `negate`, `check_hyp`, `check_equal`,
`get_concl`, `beq_str`, `eqimpl`, `_Evar_sflib_` / `show_evars`.

**Hypothesis hygiene.** `hide_goal`, `unhide_goal`, `is_local_definition`,
`clear_unused`, `clear_tautology`, `clear_reducible_truth`,
`clear_universal_truth`, `clear_tac`; equality saturation via `exists_prop`,
`propagate_eq`, `eq_closure_tac`.

**Ltac2 section.** `has_prefix`, `rename1`, `renames_prefix` and the notation
`renames <prefix> into <n1>, <n2>, …`, which bulk-renames all hypotheses
sharing a name prefix.

## `StdAxioms.v` — the classical axioms CRIS assumes

Re-exports four consequences of the stdlib's classical modules:
`func_ext_dep` (dependent functional extensionality), `func_ext`,
`dependent_functional_choice` (derived from `functional_choice` through
`non_dep_dep_functional_choice`), and `proof_irr : proof_irrelevance`.

## `Coqlib.v` — global prelude

Re-exports `sflib`, Paco, `StdAxioms`, and the classical/list/arith parts of the
standard library, then adds:

- Settings: `Set Implicit Arguments`, `Generalizable All Variables`, search
  blacklist for `_obligation_`.
- `incl_PreOrder`, the `topN` notations (`top1` … `top6`), the `p -N q`
  difference notations, `sumbool_to_bool` (as a coercion), `Notation "f ∘ g"`,
  `(∘)`, `map_fst`, `map_snd`, `fst_map_snd`, `or_else`.
- Tactics: `is_prop`, `clear_until`, `sp H` (specialize a hypothesis with the
  unique matching hypothesis in context, failing with a candidate list if
  ambiguous), `refl`, `etrans`, `congr`, `et`, `sym`, `rp`, `simpl_bool`,
  `bsimpl`, `econsr` (`econstructor 30` down to `1`), `Psimpl_` / `Psimpl`
  (classical propositional normalisation: double negation, De Morgan,
  quantifier negation), `ii as`.
- List lemmas: `map_ext_strong`, `find_map`, `rev_nil`, `cons_app`,
  `list_map_injective`, `app_eq_inv`, `firstn_S`, `nodup_length`,
  `nodup_app_l`, `nodup_app_r`, `nodup_comm`, `NoDup_snoc`, `NoDup_rev`,
  `NoDup_app_disjoint`, `NoDup_inj_aux`, `flat_map_map`, `map_flat_map`,
  `flat_map_single`, `list_max_in`.
- Logic lemmas: `not_ex_all_not`, `not_and_or_strong`, `NNPP_rev`,
  `func_ext_rev`, `pos_elim_succ`.
- **Sealing.** The `SEAL` module type and opaque `Seal` implementation with
  `Seal.sealing : string -> forall X, X -> X` and `Seal.sealing_eq`; tactics
  `seal_with`, `seal`, `unseal`; printing notation `☃ y`. Used to stop `simpl`
  from unfolding chosen subterms.
- **Fresh names.** `string_length_app`, `strings_maxlen`, `string_repeat`,
  `string_repeat_length`, `strings_maxlen_app`, `strings_maxlen_notin`,
  `string_ex_not_in` (there is always a string outside any finite list), and
  the stdpp-flavoured `maxlen`, `mname_long`, `mname_long_length`,
  `elem_of_maxlen`, `maxlen_app`. These support fresh module/function-name
  generation elsewhere in CRIS.

## `AList.v` — decidable equality and association lists

- `Class Dec A := dec : forall a0 a1, {a0 = a1} + {a0 <> a1}` with instances for
  `positive`, `string`, `nat`, `Z`, `option A`. `update` for point-updating a
  function. `function_Map` (an ExtLib `Map` instance for `K -> option V`),
  `Dec_RelDec` and `Dec_RelDec_Correct` bridging `Dec` to ExtLib's `RelDec`.
- Association-list operations on ExtLib's `alist`: `alist_pop`, `alist_pops`,
  `alist_replace`, `alist_filter`, `_alist_upd` / `alist_upd` (in-place update
  that preserves position and key order; declared `simpl never`), plus
  `Arguments` declarations making `alist_find`/`alist_add`/`alist_remove`
  implicit-friendly.
- `eq_rel_dec_correct` relating `?[eq]` to `Dec`.
- A large lemma section: `alist_find_some`, `alist_find_some_iff`,
  `alist_find_none`, `alist_find_app`, `alist_find_app_o`, `alist_find_map`,
  `alist_find_map_snd`, `alist_find_find_some`, `alist_find_find_none`,
  `alist_add_find_eq`/`_neq`, `alist_remove_find_eq`/`_neq`,
  `alist_find_filter`, `alist_add_nodup`, `alist_remove_filter`,
  `alist_add_filter`, `alist_add_other_filter`, `alist_permutation_find`.
- Key/`NoDup` lemmas: `alist_find_fst_some`/`_none`/`_notin`/`_in`,
  `nodup_eqlen_in_rev`, `in_eqlen_nodup_rev`, `alist_add_incl`,
  `alist_find_with_nodup`, `List_filter_none`, `existsb_incl`.
- `alist_upd` theory: `alist_upd_in_or`, `alist_upd_fst`, `alist_upd_keys`,
  `alist_upd_nodup`, `alist_upd_nodup_inv`, `alist_upd_with_nodup`,
  `alist_upd_head`, `alist_upd_tail`, `alist_upd_not_tail`,
  `alist_upd_not_in`, `alist_find_upd`, `alist_upd_find`, `alist_shadow`,
  `alist_find_incl`.
- `alist_replace`/`alist_remove` corollaries: `alist_replace_find_None`,
  `alist_replace_find_eq_Some`, `alist_replace_find_eq_None`,
  `alist_replace_find_neq_Some`, `alist_remove_find_None`.
- The `asimpl` tactic notation (unfold `alist_remove`/`alist_add`, then
  `simpl`), in goal / hypothesis / `*` forms.

## `Any.v` — universal type

Two structurally identical but *distinct* universal types, so that a value can
be boxed twice without collision (`SAny.t` values are themselves injected into
`Any.t` in CRIS).

Each is a sealed module (`Any : ANY`, `SAny : SANY`) over the internal
inductive `_t ::= _upcast (b : box) | _upfun {T} (f : T -> _t)`, where
`box := box_intro { ty : Type; val : ty }`. The exported interface is:
`t`, `upcast`, `downcast`, `upf`, `downf`, `pair`, `split`, with the laws
`upcast_downcast`, `downcast_upcast`, `upcast_inj` (injectivity up to `JMeq`),
`upf_downf`, `downf_upf`, `pair_split`, `split_pair`, `upcast_split`,
`pair_downcast` (and, inside the implementation, `pair_inj`). `pair` is defined
as `upf` over `bool`. `downcast` uses `excluded_middle_informative` on type
equality plus proof irrelevance/UIP.

Notations: `a↑` / `a↓` for `Any`, `a↑↑` / `a↓↓` for `SAny`.

## `SubPerm.v` — sub-permutation ordering on lists

`sub_perm l1 l2 := exists l0, Permutation (l0 ++ l1) l2` ("`l1` is `l2` minus
some elements"). Lemmas: `sub_perm_incl`, `sub_perm_comm`, `sub_perm_nodup`,
`sub_perm_cancel`, `sub_perm_cancel_head`, `sub_perm_cancel_tail`,
`sub_perm_remove`, `sub_perm_remove_head`, `sub_perm_remove_tail`,
`sub_perm_refl`, `sub_perm_trans`, `sub_perm_nil`, and the `PreOrder` instance
`incl_PreOrder`.

## `LAuto.v` — list-rewriting automation

Tactics for moving a chosen element to a canonical position inside a list built
from `::` and `++`, so that a lemma stated as `P (l ++ [x] ++ l')` can be
applied to an arbitrarily nested list expression: `Lauto_normalize` (turn every
`x :: l` into `[x] ++ l` and right-associate), `Lauto_prepare`, `Lauto_find x`
(re-associate so `x` sits as `(l1 ++ l2) ++ [x] ++ …`), `Lauto_finish`.
Includes a `TEST` section demonstrating the pattern and a large commented-out
`Permutation`-based predecessor (`perm_normalize`, `perm_move_forward`,
`perm_move_back`, …).

## `Red.v` — positional rewriting (`prw`)

A tactic framework for rewriting at a *positional path* in the goal instead of
by pattern. The control flag `_flag ::= _break | _continue | _fail` tells the
driver whether to keep reducing. Internals: `_equal_f`, `_einit`, `_ctx`,
`__prw`, `_prw`, `_rwb`, `_rwc`, `_rwa`. User-facing: `prw red_tac n1 n2 … 0`
(descend to the `n1`-th subterm, then the `n2`-th, …, then run `red_tac`), and
the strategy builders `rwbl` (all rules break), `rwcl` (all continue),
`rwal` (per-rule flags), `rrw`. The `TUTORIAL` module contains a fully worked
example.

## `exco.v` — generic coinductive containers ("extensional coinductives")

Two parallel developments of final coalgebras for polynomial functors.

- **Indexed** (`SPF.t = { I; shp : I -> Type; deg : forall i, shp i -> I -> Type }`,
  module `ExCo`): `_co` (one layer), the coinductive `co : I -> Type` with
  constructor `cfold`, the corecursor `cfix`, unfolding lemmas `cunfold` and
  `cfix_unfold`, the Paco relation `_cclos` / `cclos` relating a step relation
  to the container it generates, monotonicity `cclos_mon`, and the constructive
  coinduction principle `clos_fix` / `clos_coind` which turns a choice function
  `forall i x, {ux | ur i x ux}` into an element of `co` together with its
  `cclos` proof.
- **Non-indexed** (`SPFU.t = { shp; deg }`, module `ExCoU`): the same
  development without the index.

Paco hint databases are populated for both.

## `exco_stream.v` — streams by the same construction

A hand-instantiated version of `exco` for streams over a fixed element type
`T`: `_stream`, `scons`, the coinductive `stream` with `sfold`, `sfix`,
`stream_unfold`, `sfix_unfold`, the Paco relation `_sclos` / `sclos` with
`sclos_mon`, and `sclos_fix` / `sclos_coind`.

## `SAT.v` — stratified algebraic theories (the syntax framework)

The generic machinery behind CRIS's *syntactic* propositions (`sProp`), i.e.
a universe-stratified term language with a semantics that may itself mention
the semantic domain.

- `level := nat`.
- `SAT.t = { ops : Type; arity : ops -> Type -> Type }` — one algebraic
  signature, whose arities may depend on the type of *previous-level* terms.
  `SAT.emp` is the empty signature.
- `GAT.t := nat -> SAT.t` — a family of signatures indexed by "group" ids;
  `GAT.inG F GF` records that `F` occurs in the family at index `inG_id`;
  `GAT.emp`.
- `GTerm`: `term` (either `_lift` of a previous-level term, or `_cur i op args`
  applying an operation of group `i`), the level-indexed `_t`, `t_prev n`,
  `t n := t_prev (S n)`, `lift`, `liftn`, and the `inG`-based smart constructor
  `cur`.
- `SATIntp.t` — an interpretation of one signature into a semantic domain `Δ`
  (it receives both the syntactic arguments and their already-interpreted
  values). `GATIntp.t` — interpretations for every group, with `GATIntp.inG`
  linking a single interpretation to the global one.
- `GTermSem` — the semantics `_t`, `t_prev`, `t : GTerm.t n -> Δ` by recursion
  on the level and then on the term.
- `SATRed` — reduction lemmas `cur`, `lift`, `lift_0` used to compute with the
  semantics; `GTerm.cur`, `GTermSem.t`, `GTerm.t`, `GTerm.t_prev` are then made
  `Opaque`.
- Notations `⟦ F , n ⟧`, `⟦ F ⟧`, `⟨ op , args ⟩`, `⤉ P` in `SAT_scope`, and
  the `SAT_red` reduction tactic.

## `ITreelib.v` — interaction-tree utilities

Builds on `ITreeS.ITree` (the vendored ITree copy in [itreeS/](../../itreeS/)).

- `ITreeNotations` (`>>=`, `x <- t1 ;; t2`, `t1 ;;; t2`, `' p : T <- t1 ;; t2`,
  `tau;; t`, `f <$> x`), exported by default.
- Tactics: `ides` (case on `observe` and rewrite by `simpobs`/`bisim_is_eq`),
  `csc`, `resub` (re-fold `subevent` applications), `irw`, `ired1`, `ired`
  (monad-law normalisation for `bind`/`interp`/`interp_state`),
  `grind_simplify`, `grind`, `grind_ret`, `grind_ret_gen`, `itree_clarify`,
  and the argument-shape enumerators `iby1`, `iby3`.
- Lemmas: `bind_ret_l_forall`, `bind_ret_r_rev`, `map_vis`, `map_trigger`,
  `interp_trigger`, `subst_bind`, `observe_eta`, `bind_ret_l_eta`,
  `trigger_vis`, `vis_trigger`, `vis_bind`, `idK_spec`; the `itree_axiom`
  rewrite database.
- `taus` (an inductive counting leading `Tau`s), `tauK`, `idK`,
  `trivial_Handler`.
- **`itreeV`** — a "productive" tree: either a non-`Vis` tree
  (`itreeV_nvis`) or an explicit `Vis` (`itreeV_vis`); `itreeV_itree` embeds it
  back. **`interpV`** is `interp` for productive handlers, which therefore does
  *not* insert an extra `Tau`; lemmas `interpV_ret`, `interpV_tau`,
  `interpV_vis`, `interpV_trigger`, `interpV_bind`.
- **`iterV`** — the analogous tau-free iteration: `_iterV`, `iterV`, with
  `_iterV_ret_l`, `_iterV_ret_r`, `_iterV_tau`, `_iterV_vis`, `unfold_iterV`.
- **`iterC`** — `ITree.iter` with a leading `Tau`, and `unfold_iterC`.

## `ltac2_lib.v` — Ltac2 helpers

⚠️ The file warns that opening it with VsCoq 2 crashes the language server.

`or` (a `match!`-based disjunction of tactics), the exception extension
`exn ::= TCSearchSuccess (constr) | TCSearchFail`, `evar`, `unshelve_evar`,
`unshelve_evar1`, `multiverse_execute` (run a tactic for its *value*, then
backtrack the goal state), `tcsearch` and `tcsearch_alt` (run typeclass
resolution and return the resulting instance as a term), a `TEST` module, and
the Ltac1 wrappers `message` and `tcsearch`.

## `BiEnrichedProset.v` — `PROP`-enriched preorders and their proof mode

The abstract structure used by CRIS to reason about simulation-style relations
that live *inside* a separation logic, together with a full IPM-style proof
mode for them. (See the `Unreleased` entry in
[`CHANGELOG.md`](../../CHANGELOG.md) that introduced it.)

**Structure.** `BiProsetMixin` (enriched reflexivity `emp ⊢ hom x x` and
composition `hom x y ∗ hom y z ⊢ hom x z`), `BiMonProsetMixin` (functoriality
of `tensor`, associators, unitors — each with its inverse), and
`BiSymMonProsetMixin` (the braiding). `BiProset PROP` bundles a carrier
`proset_ob`, `proset_hom`, `proset_unit`, `proset_tensor` and the three
mixins: a `(PROP, ∗, emp)`-enriched preorder with symmetric monoidal
structure.

**Framing.** `BiProsetFrame X R P Q` ("removing `R` from `P` leaves `Q`") with
instances `biproset_frame_unit`, `_here`, `_tensor_l`, `_tensor_r`,
`_tensor_l_rec`, `_tensor_r_rec` (priorities 0–10) and mode
`+ + + ! -`.

**Derived laws.** `biproset_refl`, `biproset_trans`, `biproset_tensor_hom`,
`biproset_tensor_assoc(_inv)`, `biproset_tensor_left_unit(_inv)`,
`biproset_tensor_right_unit`, `biproset_tensor_braid`,
`biproset_tensor_move_right`.

**Proof-state representation.** Reuses IPM's `env`/`ident` machinery:
`bpenv_replace`, `bpenv_split`, `bpenv_remove_ident`, `bpenv_partition`,
`bpenv_interp` (fold the context with `tensor`), `bpenv_interp_stripped_go` /
`bpenv_interp_stripped` (a unit-free reading), and
`bpenv_entails X Γ Q := proset_hom (bpenv_interp X Γ) Q`.

**Soundness lemmas** for each tactic: `bpenv_replace_hom`, `bpenv_split_hom`,
`bpenv_partition_hom`, `bpenv_start`, `bpenv_apply`, `bpenv_partition_entails`,
`bpenv_partition_entails_right`, `bpenv_assert`,
`bpenv_interp_stripped_go_hom`, `bpenv_interp_stripped_hom`, `bpenv_stop`,
`bpenv_delete_unit`, `bpenv_drop_unit`, `bpenv_singleton_refl`, `bpenv_frame`,
`bpenv_rename`, `bpenv_destruct`, `bpenv_pose`, `bpenv_pose_selected`.

**Notation.** Printing notations rendering the three-context goal
(intuitionistic `□`, spatial `∗`, BiProset `⊗`) in all eight
empty/non-empty combinations.

**Tactics** (the `j` family; the file contains a user guide in a comment):
`jStartProof` / `jStartProof (X)` / `jStopProof`, `jEval`, `jUnitIntro`,
`jLookup`, `jAsIdent`, `jRename`, `jDestructHyp`, `jDestruct … as …`,
`jIntros` (one pattern, IPM+BiProset patterns, or with an explicit `X`),
`jClassifySplitHyps`, `jSplitIPM`, `jSplitCoreIds`, `jSplitCore`,
`jSplitL` / `jSplitR`, `jFrameHyp`, `jFrameHyps`, `jFrameCore`, `jFrameAny`,
`jFrame`, `jFresh`, `jParseSpatialGoal`, `jAssertCore`,
`jAssert … with … as …`, `jFind`, `jWithMorphism`, `jApplyBpenv`,
`jApplyMorphismCore`, `jApplyMorphism`, `jApplyCore`, `jApply`,
`jClearPersistent`, `jPoseMorphismCore`, `jPoseMorphism`, `jAddIdent`,
`jSpatialHypIds`, `jMorphismHypIds`, `jPoseProofAt`, `jPoseProofMany`,
`jPoseProofAuto`, `jPoseProofWith`, and the three `jPoseProof` notations.