module

import Mathlib.Data.Rat.Cast.OfScientific
public import New.Reduction.PrimeSums
import New.Determinant.Twist.LongForms
import New.Reduction.ShortAndEnough

/-!
# The main inequality

One covolume, corrected by an index, is bounded from both sides. Write `dim` for the dimension of
the target (`targetDim`), `mainAmount` for the main amount and `rem` for the total remainder
(`totalRemainder`), weighted sums over primes less their expected values. Theorems A and B give a
family of `n ≤ dim` target forms, a bound `V` for the logarithm of the squared covolume of its lifts
(`TwistedLattice.CovolumeLe`) and a bound `δ` for its index (`TwistedLattice.IndexLe`). Up to
errors,

    mainAmount ≤ (V + 2 δ) / dim ≤ mainAmount - (n / dim) m rem,

where the lower bound is Theorem C. The main amount cancels. The proof first keeps the cost of
the missing dimensions in `mul_remainder_le_of_covolume_index_comparison`, then bounds it using
the near-full rank from Theorem B.

Notions from other files:

* `Data P`: the data for the parameters `P` (a modulus `q₀` and a prime `d`). They bundle
  scales `x`, `x₁`, `b` in prescribed ranges (`D.logB = log b`), the number `D.m` of lifts, a set
  of places of the CM field `D.E`, the `b`-places, which carry the weight `b`, and primes for the
  levels. `D.a = x b`, and `D.f` is the number of infinite places of `D.E`.
* `D.normalizedPoincare g`: the translate `g 𝔭` by `g : D.chosenGL` of a fixed linear map `𝔭` from
  the source `D.ramifiedSourceForms` to the target `D.targetForms`.
* `D.integralRamified`: the source forms that are integral at every `ι : PrimePadicIso`.
* `D.errorUnit`: the unit of loss `f a log³ b`.

## The inputs

* Theorem A: (a) `span_short_integralRamified_eq_top` (size) and (b) `indexLe_normalizedPoincare`
  (index), both in `New.Reduction.ShortAndEnough`.
* Theorem B: `enough_forms` in `New.Reduction.ShortAndEnough`.
* Theorem C: `integral_forms_long` in `New.Determinant.Twist.LongForms`, from a twist for each prime
  (`TwistedLattice.covolume_add_index_nonneg`) and the height of `Z(1) / Z(ξ_ι)`
  (`heightLe_chainDeterminant_one_div`).
* Hadamard's bound for the covolume: `TwistedLattice.covolumeLe_of_normSqAt_le`.
* The sign of the main amount: `mainAmount_nonneg`.

## What cancels, and where

* The main amount, between the upper and the lower bound: the comparison step of
  `star_inequality`.
* The gains `∑ gain_l log l` in the size of the chain, against `log c_B`:
  `span_short_integralRamified_eq_top`.
* The constant `c₁ = (logDerivMean d 1 1).re`, between the period and the expected value
  `a (log (a / κ̄) + c₁)` of the prime sums:
  `jetSize_sub_mainPrimeSum_le`.
* The excesses `a log (κ̄ M rd_E / 2π)` of the `m` lifts, against `a log N`, up to `O(a log b)`.
  Here `κ̄` is the geometric mean of the weights `κ` over the `f` places and `rd_E` is the root
  discriminant of `E`:
  `mul_jetSize_sub_mainPrimeSum_sub_le`.
* The main terms `log x`, `log x₁` and `c₁` of the prime sums, against their expected value:
  `totalRemainder_eq`.
* A constant that depends on `q₀`, between the two cut-offs: `sum_aPlaces_primeSum`.

## The errors per dimension

| source   | where             | amount                              |
|----------|-------------------|-------------------------------------|
| size     | Theorem A (a)     | `f a log⁴ b`                        |
| index    | Theorems A (b), B | `20 log (1 + 2 b²) · f a log³ b`    |
| covolume | Theorem C         | `3 f a log⁴ b`                      |

The index enters twice, and the table shows the doubled amount. The family has `n ≥ dim / 2`
members, so `m rem` is at most twice the sum, and twice the sum is at most `f a log⁵ b`. The scales
are listed in `New.Reduction.Data.Sizes`.

## Relation to the literature

Earlier bounds for sums over primes by size against divisibility: Pritsker, The Gelfond–Schnirelman
method in prime number theory, 2005; Granville–Stark, ABC implies no Siegel zeros for L-functions of
characters with negative discriminant, 2000; Bombieri, Counting points on curves over finite fields,
Sém. Bourbaki 430, 1973; van Frankenhuijsen, The Riemann hypothesis for function fields over a
finite field, 2008.
-/

@[expose] public section

namespace New

open Real Finset Data Module Submodule

/-- Cancelling the main amount in the covolume comparison bounds the remainder with the
completion cost still explicit. Each of the `dim - n` missing dimensions contributes
`completionCost - mainAmount`; the index bound contributes twice. -/
theorem mul_remainder_le_of_covolume_index_comparison
    {dim n mainAmount remainder sizeError scalarLoss indexBound completionCost : ℝ}
    (h : dim * (mainAmount - sizeError - scalarLoss) ≤
      n * (mainAmount - remainder + sizeError) + 2 * indexBound + (dim - n) * completionCost) :
    n * remainder ≤ (dim + n) * sizeError + dim * scalarLoss + 2 * indexBound +
      (dim - n) * (completionCost - mainAmount) := by
  nlinarith only [h]

/-- **Main inequality.** For the data `D` we have `m rem ≤ f a log⁵ b`.

The parameters `P` are a multiple `q₀` of `18480` and a prime `d ≡ q₀/2 - 1 mod q₀`. The scales are
integers with `(log b) ^ 100 ≤ x`, `x ^ 10⁶ ≤ x₁`, `x₁ ^ 10⁶ ≤ b` and
`log log b ≥ 10¹² P.constantBound`. -/
theorem star_inequality {P : Parameters} (D : Data P) :
    D.m * D.totalRemainder ≤ D.f * D.a * D.logB ^ 5 := by
  -- Choose many independent images of short integral forms, bound their covolume and index from
  -- above, and compare with the lower bound `integral_forms_long_with_completion_cost`.
  obtain ⟨h_dim_pos, t, h_translate_budget, h_span_dimension⟩ :
      0 < D.targetDim ∧ ∃ t : Finset D.chosenGL,
      #t * finrank ℂ D.ramifiedSourceForms ≤ 5 * D.targetDim * log (1 + 2 * D.b ^ 2) ∧
      (1 - 4 / D.b ^ 2) * D.targetDim ≤ finrank ℂ ↥(⨆ g ∈ t, (D.normalizedPoincare g).range) :=
    D.enough_forms
  let sizeError : ℝ := D.f * D.a * D.logB ^ 4
  let logNormBound : ℝ := D.mainAmount - D.m * D.totalRemainder + sizeError
  let indexBudgetPerDim : ℝ := 10 * log (1 + 2 * D.b ^ 2) * D.errorUnit
  let short : Set D.ramifiedSourceForms :=
    {φ ∈ D.integralRamified | ∀ (g : D.chosenGL) (σ : ℂ ≃+* ℂ),
      (D.Θ 1 (D.normalizedPoincare g φ)).normSqAt σ ≤ exp logNormBound}
  have h_short_span : span ℂ short = ⊤ := D.span_short_integralRamified_eq_top
  -- A + B: take a basis from the images of short source forms under the chosen translates.
  obtain ⟨n, y, h_indep, h_near_full_rank, h_image_short⟩ : ∃ (n : ℕ) (y : Fin n → D.targetForms),
      LinearIndependent ℂ y ∧ (1 - 4 / D.b ^ 2) * D.targetDim ≤ n ∧
      ∀ i : Fin n, ∃ g ∈ t, y i ∈ D.normalizedPoincare g '' short := by
    let images : Set D.targetForms := ⋃ g ∈ t, D.normalizedPoincare g '' short
    have span_eq : span ℂ images = ⨆ g ∈ t, (D.normalizedPoincare g).range := by
      simp only [images, span_iUnion₂, span_image, h_short_span, Submodule.map_top]
    obtain ⟨y, hy_mem, -, h_indep⟩ := exists_fun_fin_finrank_span_eq ℂ images
    refine ⟨finrank ℂ (span ℂ images), y, h_indep, by rwa [span_eq], fun i ↦ ?_⟩
    simpa only [images, Set.mem_iUnion, exists_prop] using hy_mem i
  have h_rank : n ≤ D.targetDim := by simpa using h_indep.fintype_card_le_finrank
  have hn_le : (n : ℝ) ≤ D.targetDim := by exact_mod_cast h_rank
  -- Covolume: each form has squared length at most `exp logNormBound`.
  have h_covolume_upper : D.targetLattice.CovolumeLe y (n * logNormBound) := by
    refine TwistedLattice.covolumeLe_of_normSqAt_le fun i σ ↦ ?_
    obtain ⟨g, -, φ, ⟨-, hφ_short⟩, hφ_eq⟩ := h_image_short i
    rw [normSqAt_targetLattice, ← hφ_eq]
    exact hφ_short g σ
  -- Index: each translate in `t` contributes `2 · errorUnit` per dimension of the source.
  have h_index_upper : D.targetLattice.IndexLe y (D.targetDim * indexBudgetPerDim) := by
    have h_errorUnit_nonneg : 0 ≤ D.errorUnit := (HasLogBound.pos D).le
    have hy_int (i : Fin n) : ∃ g ∈ t, y i ∈ D.normalizedPoincare g '' D.integralRamified := by
      obtain ⟨g, hg, φ, ⟨hφ_int, -⟩, hφ_eq⟩ := h_image_short i
      exact ⟨g, hg, φ, hφ_int, hφ_eq⟩
    refine (D.indexLe_normalizedPoincare t hy_int).mono ?_
    calc #t * finrank ℂ D.ramifiedSourceForms * (2 * D.errorUnit)
        ≤ 5 * D.targetDim * log (1 + 2 * D.b ^ 2) * (2 * D.errorUnit) := by grw [h_translate_budget]
      _ = D.targetDim * indexBudgetPerDim := by ring
  -- C: retain the cost of completing the chosen family before estimating its codimension.
  let completionCost : ℝ := 2 * D.x₁ ^ 2 * D.b ^ 2 + D.b
  have h_volume_index_lower :
      D.targetDim * (D.mainAmount - sizeError - D.b) ≤
        n * (D.mainAmount - D.m * D.totalRemainder + sizeError) +
          2 * (D.targetDim * indexBudgetPerDim) + ((D.targetDim : ℝ) - n) * completionCost :=
    integral_forms_long_with_completion_cost h_indep h_index_upper h_covolume_upper
  have h_explicit := mul_remainder_le_of_covolume_index_comparison h_volume_index_lower
  have h_completion : ((D.targetDim : ℝ) - n) * completionCost ≤ D.targetDim * D.b := by
    have h_card : D.targetDim = n + (D.targetDim - n) := by omega
    have h_cost := mul_completion_cost_le h_near_full_rank h_card
    rwa [Nat.cast_sub h_rank] at h_cost
  -- Absorb the completion and scalar costs into the existing per-dimension budget.
  have h_loss_pos : 0 < sizeError := HasLogBound.pos D
  have h_missing_main_nonneg : 0 ≤ ((D.targetDim : ℝ) - n) * D.mainAmount :=
    mul_nonneg (sub_nonneg.mpr hn_le) D.mainAmount_nonneg
  have h_b_le_error : D.targetDim * D.b ≤ D.targetDim * sizeError :=
    mul_le_mul_of_nonneg_left D.le_of_hasLogBound D.targetDim.cast_nonneg
  have h_short_error : n * sizeError ≤ D.targetDim * sizeError :=
    mul_le_mul_of_nonneg_right hn_le h_loss_pos.le
  let totalErrorPerDim : ℝ := 4 * sizeError + 2 * indexBudgetPerDim
  have h_main_cancelled : n * (D.m * D.totalRemainder) ≤ D.targetDim * totalErrorPerDim := by
    dsimp only [totalErrorPerDim]
    nlinarith only [h_explicit, h_completion, h_missing_main_nonneg, h_b_le_error, h_short_error]
  -- Divide by `n ≥ targetDim / 2 > 0`.
  have h_half_dimension : (D.targetDim : ℝ) ≤ n * 2 := by
    have h_share : 4 / D.b ^ 2 ≤ 2⁻¹ := D.le_of_hasLogBound
    calc (D.targetDim : ℝ) = (1 - 2⁻¹) * D.targetDim * 2 := by ring
      _ ≤ (1 - 4 / D.b ^ 2) * D.targetDim * 2 := by grw [h_share]
      _ ≤ n * 2 := by grw [h_near_full_rank]
  have hn_pos : (0 : ℝ) < n :=
    pos_of_mul_pos_left ((Nat.cast_pos.2 h_dim_pos).trans_le h_half_dimension) zero_le_two
  -- The errors are of smaller order than `f a log⁵ b`.
  have h_error_budget : |2 * totalErrorPerDim| ≤ D.f * D.a * D.logB ^ 5 := D.le_of_hasLogBound
  refine le_of_mul_le_mul_left ?_ hn_pos
  calc n * (D.m * D.totalRemainder) ≤ D.targetDim * |totalErrorPerDim| := by
        grw [h_main_cancelled, ← le_abs_self]
    _ ≤ n * 2 * |totalErrorPerDim| := by grw [h_half_dimension]
    _ = n * |2 * totalErrorPerDim| := by rw [abs_mul, Nat.abs_ofNat, mul_assoc]
    _ ≤ n * (D.f * D.a * D.logB ^ 5) := by grw [h_error_budget]

end New
