# `itreeS` — a stripped-down, extensional copy of the Interaction Trees library

Logical path: `ITreeS`.

This is a vendored and heavily reduced fork of the
[InteractionTrees](https://github.com/DeepSpec/InteractionTrees) library. Two
design decisions distinguish it from upstream and shape everything else in
CRIS:

1. **Only strong bisimulation.** `eqit` here is *just* structural bisimulation
   (`eqitF` has exactly three constructors: `EqRet`, `EqTau`, `EqVis`). There is
   no `Tau`-stripping, no `b1`/`b2` inequality flags, no `eutt`/`euttge`. `Tau`
   steps are therefore observable, which CRIS needs because it counts steps.
2. **Bisimulation *is* equality.** `EqAxiom.v` postulates
   `bisim_is_eq : t1 ≅ t2 -> t1 = t2`. Consequently all the monad laws below are
   stated as plain Leibniz equalities (`bind_bind : (s >>= k) >>= h = s >>= …`)
   rather than as setoid rewrites, and there is no `Proper`/setoid infrastructure
   to carry around.

Only the fragment CRIS uses is kept: no `Basics.CategoryTheory`, no `KTree`,
no recursion combinators (`rec`, `mrec`), no `Events.*`, no `Props`.

`ITree.v` is the single entry point; everything else is reachable through it.

---

## `ITree.v`

The umbrella module. Re-exports, in dependency order: `CategoryOps`, `Basics`,
`Sum`, `ITreeDefinition`, `Subevent`, `Eqit`, `EqAxiom`, `EqitFacts`, `Interp`,
`State`, `TranslateFacts`, `InterpFacts`, `StateFacts`.

## `Basics.v` — general definitions, not specific to itrees

- `Module Monads`: `identity`, `stateT S M A := S -> M (S * A)`, with
  `Functor_stateT` and `Monad_stateT` instances.
- `Class MonadIter M := iter : forall {I R}, (I -> M (I + R)) -> I -> M R`,
  the primitive for general recursion, with `Hint Mode MonadIter !` and the
  lifting `MonadIter_stateT` (which needs no `Monad` assumption on the base).
- `Notation iEvent := (Type -> Type)` — the type of event signatures, used
  pervasively across CRIS instead of writing `Type -> Type`.
- `Notation "E ~> F" := (forall T, E T -> F T)` and the identity `idM`.

## `CategoryOps.v` — typeclass interface for categories

Object-indexed hom-families `C : obj -> obj -> Type`. Contains only the
*operations* (the laws live in upstream's `CategoryTheory`, which is not
vendored):

- `Carrier` module with `Notation binop obj := obj -> obj -> obj`.
- `cat_scope` / `%cat`.
- Classes `Id_` (`id_ a : C a a`), `Cat` (`cat : C a b -> C b c -> C a c`),
  `Initial i` (`empty : C i a`).
- Cocartesian classes `Case` (`case_`), `Inl` (`inl_`), `Inr` (`inr_`).
- `CatNotations` with `Infix ">>>" := cat`.
- **`ReSum`** — the automatic solver for reassociating sums:
  `Class ReSum a b := resum : C a b`, with instances `ReSum_id`, `ReSum_sum`,
  `ReSum_inl` (priority 8), `ReSum_inr` (priority 9), `ReSum_empty`, and
  `Hint Mode ReSum ! ! ! !`. The priorities make `E -< E +' E +' F` resolve to
  the *first* occurrence.

## `Sum.v` — sums of indexed types

`Variant sum1 (E1 E2 : iEvent) X := inl1 | inr1` with the infix notation
`E1 +' E2` (level 59, right associative), the eliminator
`case_sum1 : (A ~> C) -> (B ~> C) -> A +' B ~> C`, the empty signature
`void1` and its eliminator `elim_void1`.

## `ITreeDefinition.v` — the core coinductive type

- `Variant itreeF itree := RetF (r : R) | TauF (t) | VisF {X} (e : E X) (k : X -> itree)`
  and the final coalgebra `CoInductive itree := go { _observe : itreeF itree }`,
  declared with `Set Primitive Projections`.
- `itree' E R` (a "forced" tree), `observe` (the wrapped projection), and the
  constructor notations `Ret x`, `Tau t`, `Vis e k` (notations rather than
  definitions, so that extraction works).
- `Module ITree`: `subst` (the `cofix`, with the continuation kept outside so
  the definition can be nested in other cofixpoints), `bind t k := subst k t`,
  the `on_left` notation, `iter` (with the `Tau` guard that prevents an eager
  loop when `step i = Ret (inl _)`), `map`, `trigger`, and the tactics
  `fold_subst`, `fold_monad`.
- `ktree E A B := A -> itree E B`.
- `ITreeNotations` (`>>=`, `x <- t1 ;; t2`, `t1 ;; t2`, `' p <- t1 ;; t2`).
- Instances `Functor_itree`, `Applicative_itree`, `Monad_itree`,
  `MonadIter_itree`.
- Tactics: `hexploit_mp`/`hexploit`, `hinduction … before …`,
  `rewrite_everywhere`, `rewrite_everywhere_except`, `genobs`, `genobs_clear`,
  `simpobs`, `desobs`.

## `Subevent.v` — extensible effects

- `IFun E F := E ~> F` as a category: `Id_IFun`, `Cat_IFun`, `Initial_void1`,
  `Case_sum1`, `Inl_sum1`, `Inr_sum1`.
- `Notation Subevent E F := ReSum IFun E F` with the infix `E -< F`, the
  coercion `subevent := resum IFun`, and `Subevent_refl`.
- `SumNotations`: `( x |)`, `(| x )`, `(| x |)`, `(|| x )`, … up to seven
  levels of nesting, in `sum_scope`.
- The polymorphic constructors `vis e k := Vis (subevent _ e) k` and
  `trigger e := ITree.trigger (subevent _ e)`.
- Reshaping lemmas: `resum_to_subevent`, `subevent_subevent'`,
  `subevent_subevent`, `subevent_void1`, `subevent_left`, `subevent_right`.
- Warning in the header: `ReSum` resolution can loop; bound it with
  `Typeclasses eauto := 5`.

## `Eqit.v` — strong bisimulation

The heterogeneous relation transformer
`eqitF (RR : R1 -> R2 -> Prop) sim : itree' E R1 -> itree' E R2 -> Prop` with
constructors `EqRet`, `EqTau`, `EqVis`; its composition with `observe`
(`eqit_`); monotonicity (`eqitF_mono`, `eqit__mono`); the Paco greatest fixed
point `eqit RR := paco2 (eqit_ RR) bot2`; the companion compatibility lemma
`id_wcompat`. Hint databases `itree` and `paco` are populated. Notation:
`Infix "≅" := (eqit eq)`.

## `EqAxiom.v` — the extensionality axiom

`Axiom bisim_is_eq : t1 ≅ t2 -> t1 = t2`, plus the trivial `eq_univ_up`.
This is the axiom that lets the rest of CRIS treat itrees extensionally.

## `EqitFacts.v` — consequences of `≅` and the monad laws

- Inversion: `eqitF_inv_VisF_r`, `eqitF_inv_VisF`.
- `Reflexive_eqitF`, `eq_is_bisim` (the converse of `bisim_is_eq`, provable).
- Eta: `itree_eta_`, `itree_eta`, `simpobs`.
- Structural computation: `bind_ret_l`, `bind_tau`, `bind_vis`,
  `unfold_bind` (via the `bind_ t k` notation), `bind_trigger`,
  `unfold_aloop`, `unfold_iter`.
- The up-to-bind closure `eqit_bind_clo` with
  `eqit_clo_bind : eqit_bind_clo <3= gupaco2 (eqit_ RR) id`.
- Monad laws as *equalities*: `bind_ret_r`, `bind_bind`; and for `map`:
  `map_map`, `bind_map`, `map_bind`, `map_ret`, `map_tau`.
- The `itree` rewrite hint database (`bind_ret_l`, `bind_ret_r`, `bind_tau`,
  `bind_vis`, `bind_map`, `map_ret`, `map_tau`, `bind_bind`).
- Bind inversion: `eqit_inv_bind_ret`, `eqit_inv_bind_vis`,
  `eqit_inv_bind_tau` — given the shape of `t >>= k`, determine the shape of
  `t`.

## `Interp.v` — translation and interpretation

- `translateF` / `translate (h : E ~> F) : itree E ~> itree F`: relabel every
  visible event; unlike `interp` it introduces no `Tau`, so
  `translate (id_ E) t ≅ t`.
- `interp (h : E ~> M) : itree E ~> M` for any `Functor`+`Monad`+`MonadIter`
  `M`, defined via `iter`. Note the loop body returns `inl t` on `TauF`, so
  interpretation of a `Vis` inserts one `Tau` (see `interp_vis` below).

## `TranslateFacts.v`

`unfold_translate`, `translate_ret`, `translate_tau`, `translate_vis`,
`translate_bind`, the inversion principle `translate_Vis_inv`, and
`translate_trigger`.

## `InterpFacts.v`

`_interp` and the unfolding lemma `unfold_interp`; the specialisations
`interp_ret`, `interp_tau`, `interp_vis` (which shows the inserted
`Tau`: `interp f (Vis e k) = f _ e >>= fun x => Tau (interp f (k x))`);
`interp_bind` (interp is a monad morphism); composition `interp_interp` and
`interp_translate`; and `interp_iter'` / `interp_iter`. `interp_ret`,
`interp_vis`, `interp_bind` are added to the `itree` rewrite database.

## `State.v`

`interp_state (h : E ~> stateT S M) : itree E ~> stateT S M := interp h` —
i.e. state passing is just interpretation into the state monad transformer.

## `StateFacts.v`

`_interp_state` and `unfold_interp_state`; `interp_state_ret`,
`interp_state_vis`, `interp_state_tau`, `interp_state_trigger`, and
`interp_state_bind`. These are the rewrite rules driving CRIS's `ired`
normalisation tactic (see [`theories/lib/ITreelib.v`](../theories/lib/ITreelib.v)).