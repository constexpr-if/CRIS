# `theories/iris_system/lib` — ghost-state libraries

Logical path: `CRIS.iris_system.lib`.

Ports of the standard `iris.base_logic.lib` ghost-state libraries to CRIS's
`GRA`/`own` layer, plus one library (`allocs`) that has no Iris counterpart.

Two things are systematically different from upstream Iris:

- **Allocation uses `o=>` instead of `|==>`.** Because CRIS's `bupd` is a
  *strong* (frame-independent) update, allocating a fresh ghost name needs the
  `own_admin` authority. Every `*_alloc` lemma below therefore has the shape
  `⊢ o=> ∃ γ, …` (see [`../own.v`](../own.v)). The `*_alloc_strong` variants of
  Iris, which pick a name satisfying an arbitrary infinite predicate, are
  commented out — a comment in `own.v` explains that no model is known that
  supports both `own_alloc_strong_dep` and splitting `own_admin`.
- **Each library has a "syntactic mirror".** Below the ordinary semantic
  section, each file adds a `syn_*` section defining the same assertion as a
  `GTerm.t n` (a term of the stratified syntax from
  [`../sProp.v`](../sProp.v)), together with an `SLRed` instance proving that
  interpreting the syntax gives back the semantic assertion. This is what lets
  these resources appear inside *invariants*. The boilerplate
  `subG_*Γ` / `subHG_*` / `inGΓ_*` instances bridge `HRA` and `GRA`; the
  `inGΓ_*` ones carry a `FIXME` noting that the `HRA`/`GRA` unification should
  ideally be automatic.

---

## `allocs.v` — pointwise allocation RA (CRIS-specific)

The header explains the purpose: *"A resource algebra for pointwise lifting.
Designed as a workaround for CRIS's weak-update problems by reserving every
index upfront."* Because the update modality is frame-independent, one cannot
simply invent a fresh ghost name; instead an *authority* owns a decidable set
of not-yet-allocated names, and allocation carves one out.

```coq
Definition allocsUR (K : Type) (A : cmra) : ucmra :=
  K -d> optionUR (csumR (exclR unitO) A).
```

`Cinl (Excl tt)` marks "reserved but unallocated", `Cinr a` an allocated cell
holding `a`.

- `allocsUR_lookup_op`, `allocs_auth (P : K → Prop)` (the reservation for every
  `k` with `P k`), `allocs_frag k a` (a singleton allocated cell), with
  `Params`/`Arguments` declarations.
- `allocs_frag_ne`, `allocs_frag_proper`, `allocs_frag_op`.
- Validity: `allocs_auth_valid`, `allocs_frag_valid`, `allocs_both_valid` (auth
  and frag at `γ` can only compose if `¬ P γ`).
- Updates: `allocs_frag_update` (lift any update on `A`), **`allocs_alloc`**
  (shrink the reservation from `P` to `Q` and get `allocs_frag γ a`, provided
  `Q ⊆ P` and `γ ∈ P ∖ Q`), `allocs_auth_split` (split a reservation into two
  disjoint ones), and the equational versions `allocs_auth_split_2` /
  `allocs_auth_split_2_L`.

## `ghost_var.v` — fractional ghost variable

`ghost_varG Σ A` wraps `inG (dfrac_agreeR (leibnizO A)) Σ`; `ghost_varΣ A`;
`subG_ghost_varΣ`. The sealed `ghost_var γ q a := own γ (to_frac_agree q a)`.

Lemmas/instances: `ghost_var_timeless`, `ghost_var_fractional`,
`ghost_var_as_fractional`, `ghost_var_alloc`, `ghost_var_valid_2`
(fractions add up to ≤ 1 and the values agree), `ghost_var_agree`,
`ghost_var_combine_gives`, `ghost_var_combine_as` (cost 60),
`ghost_var_split`, `ghost_var_update` (needs full ownership),
`ghost_var_update_2`, `ghost_var_update_halves`, `frame_ghost_var`.

Syntactic mirror: `syn_ghost_var γ q a := sown γ (to_frac_agree q a)` with
`ghost_var_red`.

## `token.v` — unique tokens

`tokenG Σ` wraps `inG (exclR unitO) Σ`; `tokenΣ`; `subG_tokenΣ`. The sealed
`token γ := own γ (Excl ())`.

`token_timeless`, `token_alloc`, **`token_exclusive`** (`token γ -∗ token γ -∗ False`,
the whole point of the library), `token_combine_gives`.

Syntactic mirror: `syn_token γ := sown γ (Excl ())` with `token_red`.

## `ghost_map.v` — ghost map / ghost heap

`ghost_mapG Σ K V` wraps `inG (gmap_viewR K (agreeR (leibnizO V))) Σ`;
`ghost_mapΣ`; `subG_ghost_mapΣ`. Two sealed assertions: `ghost_map_auth γ q m`
(authoritative view of the whole map) and `ghost_map_elem γ k dq v`, written
`k ↪[γ]{dq} v` (with `□` for the persistent/discarded case).

*Element lemmas.* `ghost_map_elem_timeless`, `_persistent`, `_fractional`,
`_as_fractional`, `ghost_map_elem_valid`, `_valid_2`, `_agree`,
`ghost_map_elem_combine_gives`, `ghost_map_elem_combine`,
`ghost_map_elem_combine_as` (cost 60), `ghost_map_elem_frac_ne`,
`ghost_map_elem_ne`, `ghost_map_elem_persist` (make read-only;
`_unpersist` is commented out).

*Authority lemmas.* `ghost_map_alloc`, `ghost_map_alloc_empty`,
`ghost_map_auth_fractional`, `_as_fractional`, `ghost_map_auth_valid`,
`_valid_2`, `_agree`.

*Interaction.* `ghost_map_lookup` with the two `CombineSepGives` orientations,
`ghost_map_insert`, `ghost_map_insert_persist`, `ghost_map_delete`,
`ghost_map_update`; big-op versions `ghost_map_lookup_big`,
`ghost_map_insert_big`, `ghost_map_insert_persist_big`
(`ghost_map_delete_big` / `ghost_map_update_big` are commented out, as is the
helper `ghost_map_elems_unseal` they need).

Syntactic mirror: `syn_ghost_map_auth`, `syn_ghost_map_elem` with
`ghost_map_auth_red`, `ghost_map_elem_red`, and the `k ↪[γ]{dq} v` notation
re-declared in `SAT_scope`.

## `mono_list.v` — append-only list

Marked experimental (tracking Iris issue #439). Wraps
`inG (mono_listR (leibnizO A)) Σ`; `mono_listΣ` (declared `Opaque`);
`subG_mono_listΣ`.

Three assertions: the fractional authoritative `mono_list_auth_own γ q l`, the
persistent lower bound `mono_list_lb_own γ l`, and the derived persistent
`mono_list_idx_own γ i a := ∃ l, ⌜l !! i = Some a⌝ ∗ mono_list_lb_own γ l`.

`mono_list_lb_own_persistent`, `mono_list_idx_own_persistent`,
`mono_list_auth_own_fractional`, `_as_fractional`,
`mono_list_auth_own_agree`, `mono_list_auth_own_exclusive`,
**`mono_list_auth_lb_valid`** (`l2 `prefix_of` l1`), `mono_list_lb_valid`
(any two lower bounds are comparable), `mono_list_idx_agree`,
`mono_list_auth_idx_lookup`, `mono_list_lb_own_get` (snapshot),
`mono_list_lb_own_le`, `mono_list_idx_own_get`, `mono_list_own_alloc`,
**`mono_list_auth_own_update`** (grow by a prefix extension),
`mono_list_auth_own_update_app`.

Syntactic mirror: `syn_mono_list_auth_own`, `syn_mono_list_lb_own`,
`syn_mono_list_idx_own` with the three corresponding `*_red` instances.

## `saved_prop.v` — saved propositions and predicates

Unlike the other files, this one *is* the point of contact between ghost state
and the syntax: what is saved is a `GTerm.t n`, i.e. a stratified syntactic
proposition, so the resource is indexed by the level.

**Saved propositions.**
`savedPropR := discrete_funR (λ n, optionUR (dfrac_agreeR (leibnizO (GTerm.t n))))`,
`savedPropG Σ α`, `savedPropΣ`, `subG_savedPropΓ`;
`saved_prop_own γ dq x := own γ (discrete_fun_singleton n (Some (to_dfrac_agree dq x)))`
(declared `Typeclasses Opaque`), `saved_prop_own_persistent` (at
`DfracDiscarded`), `saved_prop_alloc`, `saved_prop_valid_2` (agreement),
`saved_prop_update`, `saved_prop_persist`.

Then the *syntax extension*: `saved_prop_ops ::= _saved_prop_own γ dq` with
arity `fin 1` (one `GTerm.t` argument), the `SAT.t` instance
`saved_prop_syntax`, the interpretation `saved_prop_interp`, the class
`syn_saved_propG` (registering the syntax in `α` and the interpretation in
`β`), the smart constructor `syn_saved_prop_own γ dq p := ⟨ _saved_prop_own γ dq, λ _, p ⟩`
and `saved_prop_own_red`. `syn_saved_prop_own` is then `Opaque`.

**Saved predicates.** The same development one level up, where the saved
object is a function `A → GTerm.t n`:
`savedPredR A`, `savedPredG`, `savedPredΣ`, `subG_savedPredΣ`,
`saved_pred_own`, `saved_pred_own_persistent`, `saved_pred_alloc`,
`saved_pred_valid_2`, `saved_pred_update`, `saved_pred_persist`; and the
syntax `saved_pred_ops ::= _saved_pred_own γ dq` whose arity is `A` itself,
`saved_pred_syntax`, `saved_pred_interp`, `syn_saved_predG`,
`syn_saved_pred_own`, `saved_pred_own_red`, then `Opaque`.