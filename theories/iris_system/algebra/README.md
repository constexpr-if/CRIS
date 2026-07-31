# `theories/iris_system/algebra` — CMRA additions

Logical path: `CRIS.iris_system.algebra`.

A single-file directory holding the CMRA lemmas CRIS needs beyond what
`iris.algebra` provides.

## `functions.v`

Re-exports `iris.algebra.functions` and `iris.algebra.stepindex_finite`, and
adds one lemma about the discrete-function unital CMRA
`discrete_funUR B` (for `B : A → ucmra` with `EqDecision A`):

```coq
Lemma discrete_fun_delete i f :
  f ≡ (λ x, if decide (x = i) then ε else f x) ⋅ discrete_fun_singleton i (f i).
```

That is, any discrete function splits into "everything but index `i`" composed
with the singleton at `i`. This is the pointwise-deletion counterpart of
`discrete_fun_insert`/`discrete_fun_singleton`, and is used when carving an
individual ghost location out of the global resource
(see [`../own.v`](../own.v) and [`../../common/ConcRA.v`](../../common/ConcRA.v),
whose yield tokens live in `nat -d> optionUR (exclR unitO)`).