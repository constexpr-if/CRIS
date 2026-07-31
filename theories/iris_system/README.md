# `theories/iris_system` — CRIS's separation logic

Logical path: `CRIS.iris_system`.

A self-contained, **step-index-free** re-implementation of the Iris program
logic infrastructure. Everything Iris gets from step-indexing (guarded
recursion for higher-order ghost state, impredicative invariants) is recovered
here by a *stratified syntax*: propositions that may be stored in invariants
are not `iProp`s but terms of an explicitly level-indexed term language
(`GTerm.t n`, from [`../lib/SAT.v`](../lib/SAT.v)), and an invariant at level
`n` may only mention propositions of level `< n`.

## Layout

| Path | Contents |
| --- | --- |
| [`base_logic/`](base_logic/) | The `uPred` model, its `bi` instance, derived laws, and proof-mode instances |
| [`algebra/`](algebra/) | CMRA lemmas beyond `iris.algebra` (currently one: `discrete_fun_delete`) |
| [`lib/`](lib/) | Ghost-state libraries (`allocs`, `ghost_var`, `token`, `ghost_map`, `mono_list`, `saved_prop`) |
| `iprop.v`, `own.v` | The global resource algebra `GRA` and ghost-location ownership |
| `sProp.v` | The stratified syntax of separation-logic propositions and its reduction machinery |
| `precise.v` | The `precise` predicate (a proposition is exactly one resource) |
| `invariants.v` | World satisfaction, fancy updates, invariants |
| `syn_invariants.v` | Syntactic mirror of the above, plus the concrete instantiation `inv_instances` |
| `atomic.v` | Relational atomic updates (`AU`/`AACC`) |
| `IrisTactics.v` | Ad-hoc CMRA-reasoning tactics |

Rough dependency order:
`base_logic` → `algebra` + `lib/allocs` → `iprop` → `own` → `precise` →
`sProp` → `invariants` → `syn_invariants` → (`lib/*`, `atomic`, `IrisTactics`).

---

## `iprop.v` — the global resource algebra

Where Iris has `gFunctors`, CRIS has `GRA`, with the extra requirement that
every component be **discrete** (no step-indexing).

- `Record DRA := DRA_mk { DRA_RA :> cmra; DRA_discrete : CmraDiscrete DRA_RA }`.
- `Class GRA := GRA_mk { GRA_len : nat; GRA_lookup : fin GRA_len → DRA }` —
  a finite vector of discrete CMRAs.
- `gname := positive`, `gnameO`, the distinguished `base_γ := 1`, `gid Σ`.
- **`GRAUR Σ := discrete_funUR (λ i, allocsUR positive (GRA_lookup i))`**,
  coerced from `GRA` to `ucmra`: for each component, an `allocs` map from
  ghost names to values. `initial` (everything reserved), `initial_valid`,
  `GRA_discrete`.
- `Class inG (RA : cmra) (Σ : GRA) := { inG_id : gid Σ; inG_prf : RA = GRA_lookup inG_id }`,
  with `Hint Mode inG ! -`.
- `Module GRAs` with `nil`, `singleton`, `app`, the coercion
  `GRAs.singleton : DRA >-> GRA`, and the notations `#[]`, `#[Σ1; …; Σn]`
  (elements are `DRA`s) and `##[Σ1; …; Σn]` (elements are `GRA`s).
- `Class subG Σ1 Σ2` (every component of `Σ1` occurs in `Σ2`), the `GRA_index`
  hint database, `subG_inv`, `subG_refl`, `subG_app_l`, `subG_app_r` with the
  computation lemmas `subG_app_l_inG_id` / `subG_app_r_inG_id`, `subG_inG`,
  `inG_id_subG_inG`, and the `solve_inG` tactic (CRIS's analogue of Iris's).
- Notations `iProp Σ`, `iPropO Σ`, `iPropI Σ` — all *without* step indices.

## `own.v` — ghost-location ownership

- `iRes_singleton γ a := discrete_fun_singleton (inG_id i) (allocs_frag γ (cmra_transport inG_prf a))`
  and the sealed `own γ a := uPred_ownM (iRes_singleton γ a)`.
- **`own_admin`** — the allocation authority: `∃ X : coPset, ⌜set_infinite X⌝ ∗ uPred_ownM (λ i, allocs_auth _ (.∈ X))`,
  i.e. ownership of an infinite reservation of unused ghost names in every
  component. `ir_own_admin`, `make_own_admin`.
  `own_admin_alloc_gen` picks a fresh name out of `X` and produces `own γ a`;
  `own_admin_split` halves the reservation (`coPset_split_infinite`).
- **`Own a : iProp Σ := uPred_ownM a`** — raw ownership of a whole global
  resource, "for metatheoretical uses only": the simulation relations outside
  the logic talk about concrete resources, so they need this.
- **`own_bupd P := own_admin ==∗ own_admin ∗ P`**, with `own_bupd_intro`,
  `_mono`, `_trans`, `_frame_r`, the mixin `uPred_bupd_mixin_own_bupd` and the
  *non-instance* `uPred_bi_bupd_own` (deliberately not registered, so that
  typeclass search for the ordinary `bupd` is not polluted). Notations
  **`o=> P`** and **`P o==∗ Q`**. `elim_modal_base_own` lets `iMod` eliminate a
  plain `|==>` inside an `o=>`. `own_admin_soundness_gen`,
  `own_admin_soundness`, `own_admin_alloc`.
- Properties of `own`: `iRes_singleton_ne/_proper/_op/_valid`, `own_ne`,
  `own_proper`, `own_op`, `own_mono`, `own_mono'`, `own_valid`, `own_valid_2`,
  `own_valid_3`, `own_valid_l`, `own_valid_r`, `own_timeless`,
  `own_core_persistent`, `own_alloc` (via `o=>`), `own_update`,
  `own_update_2`, `own_update_3`.
- Big-op support: `own_cmra_sep_homomorphism`, `big_opL_own`, `big_opM_own`,
  `big_opS_own`, `big_opMS_own`, `own_cmra_sep_entails_homomorphism` and the
  one-directional `big_op*_own_1`.
- Proof-mode instances: `into_sep_own`, `into_and_own`, `from_sep_own`,
  `combine_sep_as_own` (cost 60), `combine_sep_gives_own`,
  `from_and_own_persistent`.
- `Section Own` — the metatheoretic lemmas about `Own`: `Own_ne`,
  `Own_proper`, `Own_core_persistent`, `Own_unit`, `Own_Upd`, `Own_extends`,
  `Own_op`, `Own_valid`, `Own_wand_valid`, **`Own_bupd_split`** and
  **`Own_split`** (turn an entailment into a *concrete* decomposition of the
  resource — these are the lemmas that break the logic's abstraction on
  purpose), `Own_bupd_update` (the converse of `Own_Upd`),
  `Own_pure_soundness`, `Own_general_soundness`, `Own_general_completeness`,
  `own_core_completeness`, **`entails_pointwise`** (prove `P ⊢ Q` by reasoning
  resource-by-resource), and the corresponding proof-mode instances
  (`into_sep_Own`, `into_and_Own`, `from_sep_Own`, `combine_sep_as_Own`,
  `combine_sep_gives_Own`, `from_and_Own_persistent`).
- `Section own_forall` — a projection `iRes_project γ x` recovering the `A`
  stored at `γ`, with `iRes_project_ne`, `_singleton`, `_below`,
  `iRes_singleton_included_project`; and the resulting *conjunction* rules
  **`own_forall`** (`(∀ b, own γ (f b)) ⊢ ∃ c, own γ c ∗ ⌜∀ b, Some (f b) ≼ Some c⌝`),
  `own_forall_total`, `own_and`, `own_and_total`, `own_forall_pred`,
  `own_forall_pred_total`, `own_and_discrete_total`,
  `own_and_discrete_total_False`.

## `sProp.v` — the stratified syntax of propositions

The core of the step-index-free design. Built on the `SAT`/`GAT`/`GTerm`
framework of [`../lib/SAT.v`](../lib/SAT.v).

**Reduction relation.** `Class SLRed n (f : GTerm.t n) (P : PROP) := ⟦f⟧ ⊣⊢ P`
— "the interpretation of the syntactic `f` is the semantic `P`". Instances
`sl_red_base` (cost 200, the identity fallback) and `lift_red` (cost 2, for
`⤉`), plus `lift_red_base`, the two `Hint Extern 100` rules that make progress
under `match`, and the tactic `solve_base_sl_red`.

**Types.** `TypG.t := GAT.t`. `ST.type ::= baseT | sPropT | funT | prodT | sumT | listT | gmapT | qp_gmapT | metaT`
with the interpretation `ST.interp` and the `SAT.t` instance `ST.t`;
`STτ.t τ` registers `ST.t` in a type family. Notations `⇣ T`, `Φ`, `->`, `*`,
`+`, `τ{t, n}`, `τ{t}`.

**`Module SPropBi`** — the BI connectives as syntax. `ops ::= _emp | _pure | _and | _or | _impl | _forall i ty | _exist i ty | _sep | _wand | _persistently`
with arities; the interpretation `interp` into any `bi`; the classes `synG`
and `semG`; the smart constructors `syn_emp`, `syn_pure`, `syn_and`, `syn_or`,
`syn_impl`, `syn_forall`, `syn_exist`, `syn_sep`, `syn_wand`,
`syn_persistently`, and the matching notation module (`emp`, `⌜P⌝`, `∧`, `∨`,
`→`, `∀`, `∃`, `∗`, `-∗`, `<pers>` in `SAT_scope`).
Derived forms: `syn_affinely`, `syn_big_sepL`, `syn_big_sepM`, `syn_big_sepS`,
`syn_big_sepMS`, `syn_big_sepL2`, `syn_big_sepM2`, with the `<affine>`, `□`
and `[∗ list]`/`[∗ map]`/`[∗ set]`/`[∗ mset]` notations.
A `reduction` section supplies one `SLRed` instance per connective
(`empty_red`, `pure_red`, `and_red`, `or_red`, `impl_red`, `forall_red`,
`exist_red`, the `ST`-specialised `forall_red_ST` / `exist_red_ST` at cost 2,
`sep_red`, `wand_red`, `persistently_red`, `affinely_red`,
`intuitionistically_red`, `sepL_red`, `sepM_red`, `sepS_red`, `sepMS_red`,
`sepL2_red`, `sepM2_red`) together with the corresponding `*_red_base`
equations. All constructors are then made `Opaque`.

**`Module SPropBiPlainly`** — the same for `■` (`_plainly`, `syn_plainly`,
`plainly_red`, `plainly_red_base`).

**`Module SPropBiBUpd`** — the same for `|==>` (`_bupd`, `syn_bupd`,
notations `|==>` and `==∗`, `bupd_red`, `bupd_red_base`). A comment notes that
`BiFUpd` cannot get such a simple treatment because its interpretation depends
on `SATIntp.t` itself.

**`HRA` and `subHG`.** `Class HRA := GRA` — a *small* collection of RAs that
may appear inside the syntax — and `subHG Γ Σ := subG Γ Σ`. A dozen
`subG_app_l*` / `subG_app_r*` instances cover every `HRA`/`GRA` combination
(reversible coercions do not work, per the comment in `iprop.v`), plus
`subG_reflHH`, `subG_reflHG`, `subG_subHG`, `index_in_subG`, and **`in_subG`**
(transport an `inG` along a `subHG`).

**`Module SPropiProp`** — syntactic ghost ownership: `ops ::= _own {i} γ r | _own_bupd`,
interpreted as `own γ r` and `o=> …`; `synG`, `semG`, `syn_own` (notation
`sown`), `syn_own_bupd` (notations `o=>` and `o==∗` in `SAT_scope`),
`own_red`, `own_bupd_red`, `own_bupd_red_base`.

**`Module SL`** bundles all four: `SL.synG Γ τ α` and `SL.semG Γ τ α Σ β`.

**`solve_sl_red`** — the workhorse tactic that discharges `SLRed` goals. It
first tries a direct `SPropiProp.own_red` (a fast path added to avoid
rewriting through large dependent resource terms — see the `Unreleased`
entry in [`CHANGELOG.md`](../../CHANGELOG.md)), then unfolds the syntactic and
semantic heads (up to 20 arguments each), then recurses structurally through
every connective.

## `precise.v` — precise propositions

`precise P := □ ∃ pr, (Own pr ==∗ P) ∗ (P ==∗ Own pr)` — `P` is
interconvertible with ownership of one *concrete* resource. Used by the
prophecy library to extract a resource from a precondition.

Lemmas: `precise_sep`, `precise_or_ex_sep_l`, `ex_sep_comm`,
`precise_or_ex_sep_r`, `precise_or_l`, `precise_or_r`, `precise_emp`,
`precise_Own`, `precise_own`. (`precise_pure` is proved later, in
`invariants.v`, since it needs `pure_res`.)

## `invariants.v` — world satisfaction, fancy updates, invariants

**Resource algebra.** `SynO n := leibnizO (GTerm.t n)`;
`InvSetRA n := allocsUR positive (prodR (optionUR (exclR unitO)) (agreeR (SynO n)))`
— per level, a map from invariant names to (a disabled-token, the stored
syntactic proposition); `ownIRA := discrete_funUR InvSetRA`;
`ownERA := coPset_disjUR`. Classes `invGpreS` (needs `inG ownERA Γ` and
`inG ownIRA Σ`) and `invGS` (adds `enabled_name`, `invariant_name`);
`invΓ`, `invΣ`, `subG_invGpreS`.

**Predicates.** `ownIR` / `ownI i p` (persistent knowledge that `i` stores
`p`), `ownI_reserveR` / `ownI_reserve n X` (names in `X` are still free at
level `n`), `ownD i p` (the invariant is *open*), `wsat_authR` /
`wsat_auth b X` (levels `≥ b` are still unopened), `ownE E` (the enabled
mask). Laws: `ownE_exploit` (disjointness), `ownE_op`, `ownE_subset`,
`ownD_ownI`, `ownI_reserve_pick` (allocate a fresh name in an infinite
subset), `ownI_reserve_split`, `wsat_auth_split`, `wsat_auth_merge`.

**World satisfaction, one level.** `inv_satall I := [∗ map] i↦p ∈ I, ownI i p ∗ ((⟦p⟧ ∗ ownD i p) ∨ ownE {[i]})`
and `wsat n X := ∃ I, ⌜dom I ⊆ X⌝ ∗ inv_satall I ∗ ownI_reserve n (X ∖ dom I)`
— note the mask parameter `X`, which allows *splitting* world satisfaction by
namespace. Helpers `gset_to_coPset_union/_empty/_singleton`,
`inv_satall_split`; and the main lemmas `wsat_split`, `wsat_merge`,
`wsat_ownI_alloc_gen`, `wsat_ownI_alloc`, `wsat_ownI_open`,
`wsat_ownI_close`, `wsat_init`.

**All levels.** `wsat_authR_valid`, `wsat_authR_S`, `wsat_authR_alloc`;
`wsatl n X := [∗ list] x ∈ seq 0 n, wsat x X` with `wsatl_S`, `wsatl_acc`,
`wsatl_split`, `wsatl_merge`, `wsatl_mon`;
`wsats n E := wsat_auth n E ∗ wsatl n E` with `wsats_mon`, `wsats_split`,
`wsats_merge`, `wsats_exploit`.

**Fancy update.**
`uPred_fupd b E E1 E2 P := wsatl b E ∗ ownE E1 o==∗ (wsatl b E ∗ ownE E2 ∗ P)`
(sealed), the mixin `uPred_fupd_mixin`, the instances `uPred_bi_fupd`,
`uPred_bi_bupd_fupd`, `uPred_bi_own_bupd_fupd`. Note the two extra parameters
compared with Iris: the *level* `n` and the *world mask* `Ew`. Notation:
`=|n, Ew|={E1,E2}=> P` (and the `=∗`, single-mask, and `bi_scope`/
`stdpp_scope` variants), abbreviated through `fupd_ex`.
Monotonicity: `fupd_mon` (in the level) and `fupd_mon_namespace` (in the world
mask).

**Invariants.** The sealed `inv n N p := ∃ i, ⌜i ∈ ↑N⌝ ∧ ownI i p`,
`inv_persistent`, `inv_alloc` (needs `n < m` — an invariant at level `n` can
only be allocated under a fancy update at a strictly higher level, which is
what replaces the `▷` guard of Iris), `inv_acc`, the `IntoAcc` instance
`into_acc_inv` (so `iInv` works), and the `ElimModal` instances
`elim_modal_fupd_fupd_gen` (cost 10) and `elim_modal_fupd_fupd_simple`.

**Misc.** `pure_res P` (a resource that is `ε` if `P` holds and an invalid
resource otherwise) with `pure_res_spec : Own (pure_res P) ⊣⊢ ⌜P⌝`, and
`precise_pure`.

**`winv`** — the packaged world: `winv (Ew, E) := own_admin ∗ ownE E ∗ ∃ n, wsats n Ew`.
This is the invariant bundle threaded through the simulation relations.
`winv_merge`, `winv_split`, `winv_split_empty`, **`winv_fupd`** (turn a fancy
update into a plain `==∗` on `winv`), and the `ElimModal` instance
`elim_winv_simple`. `winv` is `simpl never`.

## `syn_invariants.v` — syntactic invariants and the concrete instantiation

**`Module SInv`** mirrors the invariant resources in the syntax:
`ops ::= _ownI i | _ownI_reserve X | _ownD i | _wsat_auth X` with `interp`,
`synG`, `semG`, the constructors `syn_ownI`, `syn_ownI_reserve`, `syn_ownD`,
`syn_wsat_auth`, and the reductions `ownI_red`, `ownI_reserve_red`,
`ownD_red`, `wsat_auth_red`.

**Derived syntax** (`Section derived`): `syn_ownE`, `syn_inv_satall`,
`syn_wsat n X : GTerm.t (S n)` (note the level shift — world satisfaction *at*
level `n` is a proposition of level `n+1`), the recursive `syn_wsatl`,
`syn_wsats`, and the user-facing `syn_inv N p` and `syn_fupd Ew E1 E2 P`.

**Bundles.** `Module Cris` with `Cris.synG Γ τ α` (= `STτ.t` + `SL.synG` +
`SInv.synG`) and `Cris.semG`; then
`Class cris_coreG Γ Σ α β τ _S _I` bundling both — this is the class every
CRIS development is parameterised by (extended to `crisG` in
[`../common/ConcRA.v`](../common/ConcRA.v)).

**Reductions** (`Section reduction`): `ownE_red`, `inv_satall_red`,
`wsat_red`, `wsatl_red`, `wsats_red`, and the exported `inv_red`, `fupd_red`.
`syn_inv` and `syn_fupd` are then `Opaque`.

**`Module inv_instances`** — a *concrete* choice of `τ`, `α`, `β`:
`τ` is constantly `ST.t`; `α` maps index 0 ↦ `SPropBi.syntax`, 1 ↦
`SPropBiPlainly.syntax`, 2 ↦ `SPropBiBUpd.syntax`, 3 ↦ `SPropiProp.syntax`,
and everything else ↦ `SInv.syntax`; `β` gives the matching interpretations.
The corresponding `GAT.inG` / `GATIntp.inG` instances are all discharged, then
`Cris_synG`, `Cris_semG`, `Cris_G : cris_coreG`, and finally
**`winv_alloc`** — allocate `own_admin`, the enabled mask `⊤`, and the
invariant authority, producing `winv (⊤, ⊤)`. This is what
`cris_alloc` in `ConcRA.v` builds on.

## `atomic.v` — relational atomic updates

A **relational** generalisation of Iris's logically-atomic triples: since CRIS
relates a target (implementation) to a source (specification), every
atomic pre/post-condition comes in a source and a target flavour, over
possibly *different* public-state types `X_pub_s` and `X_pub_t`.

```coq
Definition atomic_acc n Ew Eo Ei αP_s αP_t P αQ_t αQ_s Q : iProp Σ :=
  =|n, Ew|={Eo, Ei}=>
    ∀ x_s, αP_s x_s o==∗ ∃ x_t, αP_t x_t ∗
      ((αP_t x_t =|n, Ew|={Ei, Eo}=∗ αP_s x_s ∗ P) ∧          (* abort *)
       (∀ ret_t, αQ_t x_t ret_t o==∗ ∃ ret_s, αQ_s x_s ret_s ∗
        =|n, Ew|={Ei, Eo}=> Q x_s x_t ret_s ret_t)).           (* commit *)
```

- Accessor lemmas: `atomic_acc_wand`, `atomic_acc_mask`,
  `atomic_acc_mask_weaken`.
- `atomic_update` as the greatest fixed point of
  `atomic_update_pre Ψ () := atomic_acc … (Ψ ()) …`, with
  `atomic_update_pre_mono : BiMonoPred`; sealed, and both `atomic_acc` and
  `atomic_update` are `simpl never` and `Typeclasses Opaque`.
- **Notation.** 16 `AU <{ … }> @ n, Ew, Eo, Ei <{ … COMM Q }>` forms and
  12 `AACC <{ … ABORT P }> @ … <{ … COMM Q }>` forms, covering every
  combination of present/absent `∀∀ x_s`, `∃∃ x_t`, `∀∀ ret_t`, `∃∃ ret_s`
  binders (absent binders default to `unit`/`emp`).
- Lemmas: `atomic_update_mask_weaken`, `aupd_unfold`, `aupd_aacc` (the
  elimination form), `elim_mod_aupd` (so `iMod` works on an `AU`),
  `aupd_intro`, `aacc_intro`, `elim_acc_aacc` (so `iInv` works when the goal
  is an accessor), `elim_modal_acc` (forwarding instance needed because
  `atomic_acc` is opaque). A comment notes that Iris's `aacc_aupd_*` lemmas
  are unnecessary here because the relational `AU` already accounts for
  atomic updates on both sides.
- Proof-mode support: `tac_aupd_intro` and the tactics `iAuIntro`,
  `iAaccIntro … with …` (plus the `iAaccIntro with …` shorthand).

## `IrisTactics.v` — CMRA-reasoning tactics

Goal/hypothesis-directed rewriting tactics for the algebraic side conditions
that show up in CRIS proofs:

- CMRA generic: `simple_rewrite_id` (unit laws for `ε`/`None`),
  `substitute_setoid_rewrite`, `pair_des`, `option_des_hypothsis`,
  `some_included`, `option_pair_des`, `discrete_fun_tac`, combined as
  `cmra_tac`.
- `excl`: `excl_inv`, `excl_valid`, `excl_included`, combined as `excl_tac`.
- `auth`: `auth_des`, `auth_included`, combined as `auth_tac`.
- `frac`: `frac_des`.
- The top-level `iris_tac` iterating all of the above, plus two demonstration
  sections (`example_excl` with `excl_eq`, `example_auth` with `tmp`).
