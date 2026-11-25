import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace SharedBuffer.Ratio
open Real Set Filter MeasureTheory
open scoped Topology



theorem privateCoins {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {online : Ω → ℝ} {U : ℝ}
    (hi : Integrable online μ) (h : ∀ s, online s ≤ U) :
    ∫ s, online s ∂μ ≤ U := by
  simpa using integral_mono hi (integrable_const U) h


theorem removeAdditive (O A R c : ℝ)
    (copies : ∀ N : ℕ, (N : ℝ) * O ≤ R * ((N : ℝ) * A) + c) :
    O ≤ R * A := by
  by_contra! h
  have hd : 0 < O - R * A := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (c / (O - R * A))
  have hn := (div_lt_iff₀ hd).mp hN
  nlinarith [copies N]




theorem fixedSpacing (W x0 x1 E R k h alpha beta : ℝ)
    (hp : 0 < W + x1) (ha : 0 ≤ alpha) (ha' : alpha < 1)
    (hb : 0 ≤ beta) (hb' : beta < 1)
    (finiteRows : ∀ᶠ j : ℕ in atTop,
      W + (1-k*alpha^j)*x0 - h*beta^j ≤
        R * (W+x1+(E+1) * (1 / ((j : ℝ)+1)))) :
    (W+x0)/(W+x1) ≤ R := by
  have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one ha ha'
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hb hb'
  have h3 := tendsto_one_div_add_atTop_nhds_zero_nat
  apply (div_le_iff₀ hp).mpr
  have l := ((tendsto_const_nhds (x := W)).add
    (((tendsto_const_nhds (x := (1 : ℝ))).sub ((tendsto_const_nhds (x := k)).mul h1)).mul
      (tendsto_const_nhds (x := x0)))).sub ((tendsto_const_nhds (x := h)).mul h2)
  have r := (tendsto_const_nhds (x := R)).mul ((tendsto_const_nhds (x := W+x1)).add
    ((tendsto_const_nhds (x := E+1)).mul h3))
  simpa using (le_of_tendsto_of_tendsto l r finiteRows)

noncomputable def entropy (x : ℝ) := x*log x - (x-1)*log (x-1)

theorem entropyStrict : StrictMonoOn entropy (Ioi 1) := by
  have hc : Continuous entropy := continuous_mul_log.sub
    (continuous_mul_log.comp (continuous_id.sub continuous_const))
  apply strictMonoOn_of_deriv_pos (convex_Ioi 1) hc.continuousOn
  intro x hx
  rw [interior_Ioi] at hx
  have hx1 : 1 < x := hx
  have h0 : 0 < x-1 := by linarith
  have hD := (hasDerivAt_mul_log (show x ≠ 0 by linarith)).sub
    ((hasDerivAt_mul_log h0.ne').comp x ((hasDerivAt_id x).sub_const 1))
  have d : deriv entropy x = (log x + 1) - (log (x-1) + 1) := by
    simpa [entropy, Function.comp_def] using hD.deriv
  rw [d]
  linarith [Real.log_lt_log h0 (show x-1 < x by linarith)]

theorem entropyThreeHalves : entropy (3/2) < 1 := by
  have hx : (27/4 : ℝ) < exp 2 := by
    rw [show (2:ℝ) = 1+1 by norm_num, exp_add]
    nlinarith [exp_one_gt_d9]
  have hl : log (27/4:ℝ) < 2 := by
    rwa [Real.log_lt_iff_lt_exp (by norm_num)]
  have iden : log (27/4 : ℝ) = 3*log (3/2:ℝ)-log (1/2:ℝ) := by
    rw [show (27/4:ℝ) = (3/2:ℝ)^3 / (1/2:ℝ) by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [iden] at hl
  unfold entropy
  norm_num1
  linarith

theorem uniqueSharpRoot :
    ∃ r : ℝ, 3/2 < r ∧ r < 2 ∧ entropy r = 1 ∧
      ∀ t, 1 < t → entropy t = 1 → t = r := by
  have hc : Continuous entropy := continuous_mul_log.sub
    (continuous_mul_log.comp (continuous_id.sub continuous_const))
  have h2 : 1 < entropy 2 := by
    norm_num [entropy]
    linarith [Real.log_two_gt_d9]
  obtain ⟨r, hr, hval⟩ := intermediate_value_Ioo (show (3/2:ℝ) ≤ 2 by norm_num)
    hc.continuousOn (show 1 ∈ Ioo (entropy (3/2)) (entropy 2) from ⟨entropyThreeHalves, h2⟩)
  refine ⟨r, hr.1, hr.2, hval, ?_⟩
  intro t ht he
  exact entropyStrict.injOn ht (show 1 < r by linarith [hr.1]) (he.trans hval.symm)


theorem spacingAtRoot {r : ℝ} (hr : 1 < r) (hr2 : r < 2) (eqr : entropy r = 1) :
    ∃ C z0 z1 : ℝ, 0 < C ∧ C < z1 ∧ C < z0 ∧
      z0*log (z0/C)-z0+C=1 ∧ z1*log (z1/C)=1 ∧ z0/z1=r := by
  let s := -log (r-1)
  have hp : 0 < r-1 := by linarith
  have hs : 0 < s := neg_pos.mpr (Real.log_neg hp (by linarith))
  have hr0 : 0 < r := by linarith
  refine ⟨(r-1)/s, r/s, 1/s, div_pos hp hs,
    (div_lt_div_iff_of_pos_right hs).mpr (by linarith),
    (div_lt_div_iff_of_pos_right hs).mpr (by linarith), ?_, ?_, ?_⟩
  · rw [div_div_div_cancel_right₀ hs.ne', Real.log_div hr0.ne' hp.ne']
    field_simp [hs.ne']
    dsimp [s]
    unfold entropy at eqr
    linarith only [eqr]
  · rw [div_div_div_cancel_right₀ hs.ne', Real.log_div one_ne_zero hp.ne', Real.log_one]
    dsimp [s]
    field_simp [show log (r-1) ≠ 0 by simpa [s] using hs.ne']
  · field_simp
end SharedBuffer.Ratio
