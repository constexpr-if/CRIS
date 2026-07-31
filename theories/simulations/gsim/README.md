# `theories/simulations/gsim` — the global simulation on closed programs

Logical path: `CRIS.simulations.gsim`.

`gsim` is the bottom of the simulation tower

```
wsim → isim → msim → lsim → gsim
```

and relates two *closed* programs — plain `itree coreE R` — with nothing left
but `Ret`, `Tau`, `Choose`, `Take` and `IO`. Its whole purpose is
[`GSimAdequacy.v`](GSimAdequacy.v): `gsim` implies behaviour inclusion, i.e.
`Beh.of_itree itr_tgt <1= Beh.of_itree itr_src`.

Unlike `msim`/`lsim`, which use boolean progress flags, `gsim` uses a
**three-valued measure** `smj` (`smj_bot < smj_mid < smj_top`). The extra
level is what makes the adequacy proof for silent divergence go through: it
allows "two steps of slack" before a contradiction can be derived (see
`smj_ltb_not_three`).

---

## `GSim.v` — the relation

- `Variant smj := smj_top | smj_mid | smj_bot` with `smj_ltb`, `smj_leb`,
  `smj_le`, `smj_ltb_trans`, `smj_lt_mid_top`, `smj_le_bot`.
- **`gsim_def`** — the step relation: `gsim_ret`, `gsim_io` (the two sides must
  perform the same interaction and receive equal results), `gsim_tauL` /
  `gsim_tauR`, `gsim_chooseL` (∃) / `gsim_chooseR` (∀), `gsim_takeL` (∀) /
  `gsim_takeR` (∃), and `gsim_progress` (which requires a *strict* decrease
  `smj_ltb ps0 ps` and `smj_ltb pt0 pt`).
- `_gsim` ties the inner inductive knot; `gsim := paco7 _gsim bot7`.
- Metatheory: `gsim_def_mon`, `gsim_tarski`, `gsim_mon`, `gsim_ind`,
  `gsim_indC` / `gsim_indC_mon` / `gsim_indC_spec`, `gsim_flag`.
- Up-to closures: `flagC` (weaken the measures along `smj_le`) with
  `flagC_mon`, `flagC_wrespectful`, `flagC_spec`; `bindR` / `bindC` with
  `bindR_mon`, `bindC_wrespectful`, `bindC_spec`.
- Paco hint databases for all of the above.

## `GSimAdequacy.v` — behaviour inclusion

Facts about silent divergence: `spin_nofinal`, `spin_novis`,
`behave_spin_spins`, `spin_take`, `spin_choose`, `spin_tau`,
`gsim_adequacy_spin_aux`, `smj_ltb_not_three` (three strict `smj` decreases
are impossible — this is where the three-valued measure pays off),
`gsim_adequacy_spin`.

Then one `_aux` lemma plus its packaged form per behaviour constructor —
`gsim_adequacy_ret`, `_tau`, `_hang`, `_interact`, `_choose`, `_take` — with
the local driver tactic `auto_gsim`, and finally

```coq
Theorem gsim_adequacy ps pt itr_src itr_tgt :
  gsim eq ps pt itr_src itr_tgt → Beh.of_itree itr_tgt <1= Beh.of_itree itr_src.
```
proved by coinduction on the behaviour together with `Beh.of_itree_ind`.

## `GSimMod.v`

The `Mod.t`-level, in-logic packaging, exactly parallel to `lsim_mod`:

```coq
gsim_mod Ms Mt : iProp Σ    (* sealed *)
  := "if Mt is well-formed then so is Ms, and for every valid rs splitting as
      Own rt ∗ Own r ∗ winv (∅,∅),
      gsim eq smj_bot smj_bot (LMod.compile (Mod.to_lmod Ms rs) ()↑)
                              (LMod.compile (Mod.to_lmod Mt rt) ()↑)"
```
with `gsim_mod_unseal` and `gsim_mod_intro`. Added together with
`gsim_closed_adequacy` in the `Unreleased` CHANGELOG entry.

## `GSimAux.v` — derived `gsim` rules for scheduled programs

Notations `⇓cris` (`interpV ModTr.handle_crisE`), `⇓sb( m )`, `⇓smod( sp )`,
and the helper tactics `ghnorm_itr`, `lookup_tac`, `ghcNormS`, `ghcNormT`.

`Section props` then proves, for *interpreted, scheduled* programs (i.e. terms
of the form `interp_stateE (iterV (handle_callE prog) (tid, tp)) st` with the
`ModTr`/sandbox/`SModTr` layers in place), one lemma per event, so that the
`lsim → gsim` proof can take a step without re-deriving the interpretation
each time:

`gsim_flag`; `gsim_tau_src` / `_tgt`; `gsim_Choose_src` / `_tgt`;
`gsim_Take_src` / `_tgt`; `gsim_IO`; `gsim_Call_src` / `_tgt`;
`gsim_Spawn_src` / `_tgt`; `gsim_GetTid_src` / `_tgt`;
`gsim_Yield_src` / `_tgt`; `gsim_SGet_src` / `_tgt`;
`gsim_SPut_src` / `_tgt`; `gsim_Assume_src` / `_tgt`;
`gsim_AssumeRes_src` / `_tgt`; `gsim_Guarantee_src` / `_tgt`.

## `GSimTactics.v` — tactics

- `Section auxilliary` with the goal-rewriting helpers, then `greplace_s` /
  `greplace_t`.
- Layer-pushing tactics `red_LModTr`, `red_ModTr`, `red_LModTr_state`, and the
  recursive normalisers `_gnorm_itr` / `gnorm_itr` with the user-level
  `gcNormS` / `gcNormT` and the loop unfolders `giter_s` / `giter_t`.
- Basic stepping: `gstep_s` / `gstep_t` (apply `gsim_indC_spec` instantiating
  the measure at `smj_top`), `gsteps_s` / `gsteps_t`.
- The **`z*` family** — a second, faster tactic layer used by
  [`../lsim/LSimAdequacy.v`](../lsim/LSimAdequacy.v), which works on one side
  of the goal at a time: `ztac_id`, `zss`, `zonly_s` / `zonly_t`, `zshow`,
  `zsimpl_len`, `zsimpl_ths`, `zsimpl_lookup`, `zlookup_insert`,
  `zlookup_insert_ne`, `ziter`, `zstep`, `zinst`, `ziter_s` / `ziter_t`,
  `zostep_s` / `zostep_t`, `zstep_s` / `zstep_t`, and `zprogress`
  (also in a four-argument `with ps0 pt0 ps pt` form).
