# NSG-premised oriented adapter for the conditional-Bayes vs ordinary-ML separation (#271)

_Status: research comparison note. This closes the oriented-adapter open item
of #271: the conditional recovery guarantee (A) is now derived **through the
external Not-So-Greedy (NSG) guarantee** — the `decode_correct` field of
`AssemblyP1.ConditionalIdentifiability.ReadModel` — rather than through the
direct finite-pmf support collapse of
`AssemblyP1/ConditionalVsMLGenomeAdapter271.lean`. The ordinary-ML failure (B)
is unchanged: it is a prior-free, `E`-free fact about the same read model._

> **Kernel-check status.** The module
> `AssemblyP1/ConditionalVsMLNsgAdapter271.lean` is Lean kernel-checked;
> `lake build AssemblyP1.ConditionalVsMLNsgAdapter271` exits 0,
> `lake env leanchecker AssemblyP1.ConditionalVsMLNsgAdapter271` exits 0, and
> every `#print axioms` endpoint depends only on `propext`,
> `Classical.choice`, `Quot.sound` (see `AxiomAudit271.lean`).

## 1. What is instantiated, exactly

The abstract separation of
`AssemblyP1/ConditionalVsOrdinaryMLSeparation.lean` (#271) and the conditional
identifiability inference of `AssemblyP1/ConditionalIdentifiability.lean`
(#266) are composed here on the concrete finite circular read model of
`AssemblyP1/GenomeOrbitAdapter.lean` (#269):

| axis | choice in this adapter |
| --- | --- |
| alphabet | `Sym = Fin 2` (binary) |
| genome length | `G = 4`; circular genome `ZMod 4 → Sym` |
| read length | `L = 2`; oriented read string `Read = Fin 2 → Sym` |
| candidate universe | three rotation-**orbit classes**: `0001`, `0011`, `0101` up to rotation |
| orbit | `nsgOrbit := (=)` on `Fin 3` (each candidate is a distinct orbit class, `orbit_injective`) |
| observation model | `p i w = orbitReadPmf (G:=4) (L:=2) (orbit i) w` (the adapter's exact normalized read pmf) |
| prior | uniform `1/3` over the three orbit classes |
| joint mass | `nsgJ := jointMassRead`, the ordinary read-model joint `π i · p_i(r)` |
| feasibility event | `nsgFeasible := E`, the adapter's candidate-specific latent-start `I_s` predicate (`SourceFaithfulIs.InformationFeasible`) |
| decoder | `nsgDecode`, a deterministic read-only finite lookup (stand-in for the external NSG algorithm) |

The `ReadModel` is `nsgModelOf hNSG`, whose `decode_correct` field is the
**external NSG premise** `hNSG : ∀ g r, E g r → nsgDecode r = g`. It is taken
as the explicit hypothesis of every (A)-side theorem and is never proved,
never axiomatized, and never claimed.

## 2. The two kernel-checked findings

### (A ∧ ¬B) — separation, NSG-premised

Truth orbit `1` (`0011`), observed read string `00`.

* **(A) conditional recovery is certain, attributed to the NSG guarantee.**
  Given `hNSG`, the conditional posterior on the truth orbit is exactly `1`
  (`nsg_conditional_posterior_eq_one`), via the merged #266 theorem
  `ReadModel.conditional_posterior_eq_one`: the conditional mass of the
  decoder's orbit equals the total conditional mass. The decoder returns the
  truth orbit `1` at read `00` (`nsgDecode_r00`), and the orbit-sum in the
  numerator reduces to the single `g = 1` term (`nsg_num_eq`).
* **(B) ordinary ML prefers the wrong orbit.** `p 1 (r2 0 0) = 1/4 < 1/2 =
  p 0 (r2 0 0)` (`nsg_ml_strict`, reusing the adapter's `sep_ml_strict`), so
  the truth orbit `1` is not an ML maximizer (`nsg_truth_not_ml`).
* **the ordinary posterior is not certain.** The wrong orbit `0` retains
  positive prior and positive likelihood
  (`nsg_ordinary_not_certain`, reusing `sep_ordinary_not_certain`).

Packaged as `separation_nsg`.

### Precise boundary — the full uniform NSG premise fails in this model

At read `01` the two distinct orbits `1` (`0001`→`0011`) and `2` (`0101`) are
*both* information-feasible (`E_one_01`, `E_two_01`), but the decoder returns
`2`. So `E 1 (r2 0 1) → nsgDecode (r2 0 1) = 1` is false, and the full uniform
premise `∀ g r, E g r → nsgDecode r = g` fails (`nsg_full_premise_fails`).
The feasible-fibre uniqueness corollary of the NSG guarantee does not hold in
this finite model, so the NSG attribution is necessarily **instance-level** (at
the separation observation `00`, where the only feasible candidate is the truth
orbit `1`). This is a representation/saturation boundary, not a contradiction.

## 3. Trust boundary and open items

* The NSG guarantee `hNSG` is an **external attributed premise** (Shomorony et
  al. 2016, Theorem 1); the algorithm is not formalized and the guarantee is not
  proved here. The decoder `nsgDecode` is a finite lookup stand-in.
* The model is the bounded finite three-candidate witness of the merged adapter,
  not the general source-level theorem; the observation is a single oriented
  read string.
* `E → B` (conditional recovery implies ordinary ML recovery) remains **OPEN**
  and is not claimed; this module only exhibits the separation `A ∧ ¬B` and
  attributes (A) to the external NSG guarantee.
* The general (A)-boundary (`posteriorMass_eq_one_iff`, #272) and the
  ML-soundness refinement (`condCertain_imp_MLMax_of_MLsound`, #271) are
  reused by name; this module re-proves no generic posterior or ML lemma.
