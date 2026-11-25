import Repeat
import finiteGeneral
import Assemble

namespace SharedBuffer.Cohorts
open MeasureTheory Finset Filter BufferLimit
open scoped BigOperators





theorem repeatedCohorts
    {α Ω : Type*} [Fintype α] [Nonempty α] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (g : Ω → List α → α → ℝ) (X : Ω → List α → ℕ → ℝ) (T : ℕ → ℝ)
    (n m : ℕ) (v x B S q R h : ℝ) (hv : 0 < v) (hm : m ≤ n)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (ht : ∀ k, 0 ≤ T k)
    (rows : ∀ seed past i, i<n → v*X seed past i+
      (∑ j ∈ range i, Averaging.residual (X seed past) T i (j+1)) ≤ 1)
    (level : (v+m)*x = 1 + ∑ j ∈ range m, T (j+1))
    (split : ∀ seed past, (∑ a, g seed past a) / Fintype.card α ≤
      S+B*((∑ i ∈ range n, X seed past i)+1))
    (hi : ∀ l, Integrable (fun s => Repeat.play (g s) [] l) μ)
    (competitive : ∀ l, (l.length : ℝ)*(S+n*q) ≤
      R*(∫ s, Repeat.play (g s) [] l ∂μ)+h) :
    S+n*q ≤ R*(S+B*(n*x + m*(m+1)/(2*v*(v+m))+1)) := by
  apply Repeat.obliviousRepetition g _ _ R h hR hi _ competitive
  intro seed past
  have bound := Averaging.stationary_bound _ _ n m v x hv hm ht (rows seed past) level
  exact (split seed past).trans (add_le_add_left (mul_le_mul_of_nonneg_left
    (add_le_add_right bound 1) hB) S)



theorem normalize {n W B K x₀ x₁ E R : ℝ} (hn : 0<n) (hB : 0<B)
    (bound : n*B*W+n*(⌊(B-K)*x₀⌋ : ℤ) ≤ R*(n*B*W+B*(n*x₁+E+1))) :
    W+(⌊(B-K)*x₀⌋ : ℤ)/B ≤ R*(W+x₁+(E+1)/n) := by
  apply (mul_le_mul_iff_of_pos_right (mul_pos hn hB)).mp
  calc
    _ = n*B*W+n*(⌊(B-K)*x₀⌋ : ℤ) := by field_simp; ring
    _ ≤ _ := bound
    _ = _ := by field_simp; ring





structure Experiment (n : ℕ) (v W B K x₀ R : ℝ) where
  outcomes : ℕ
  Seed : Type
  [meas : MeasurableSpace Seed]
  mu : Measure Seed
  [prob : IsProbabilityMeasure mu]
  gain : Seed → List (Fin (outcomes+1)) → Fin (outcomes+1) → ℝ
  inventory : Seed → List (Fin (outcomes+1)) → ℕ → ℝ
  allowance : ℝ
  rows : ∀ seed past i, i<n → v*inventory seed past i +
    (∑ j ∈ range i, Averaging.residual (inventory seed past)
      (fun k => W*((v/(v-1))^k-1)) i (j+1)) ≤ 1
  split : ∀ seed past, (∑ a, gain seed past a) / Fintype.card (Fin (outcomes+1)) ≤
    n*B*W+B*((∑ i ∈ range n, inventory seed past i)+1)
  integrable : ∀ l, Integrable (fun s => Repeat.play (gain s) [] l) mu
  compare_payoffs : ∀ l, (l.length : ℝ)*(n*B*W+n*(⌊(B-K)*x₀⌋ : ℤ)) ≤
    R*(∫ s, Repeat.play (gain s) [] l ∂mu)+allowance



theorem sharpFromCohorts {R : ℝ} (hR : 0 ≤ R)
    (experiments : ∀ (v : ℕ), 3 ≤ v → ∀ (W : ℚ), 0 < W → ∀ x₀ : ℝ, 0<x₀ →
      Level 1 (v/((v:ℝ)-1)) W x₀ →
      ∃ c : ℕ, 0<c ∧ ∀ᶠ j : ℕ in atTop,
        Nonempty (Experiment (j+1) v W (c*((v:ℝ)*(v-1))^j) ((v:ℝ)^(j+1)) x₀ R)) :
    ∃ r : ℝ, 3/2 < r ∧ r<2 ∧ Ratio.entropy r=1 ∧
      (∀ t, 1<t → Ratio.entropy t=1 → t=r) ∧ r≤R := by
  apply Assemble.sharpFromFinite
  intro v hv W hW x₀ x₁ hx₀ L0 hx₁ L1
  have hv3 : (3:ℝ) ≤ v := by exact_mod_cast hv
  have hv0 : (0:ℝ)<v := by linarith
  have hw : 0<(v:ℝ)-1 := by linarith
  have hb : 1<(v:ℝ)/(v-1) := (lt_div_iff₀ hw).mpr (by linarith)
  have hW' : (0:ℝ)<W := by exact_mod_cast hW
  obtain ⟨m,level,_,_⟩ := active_level hb hW' hx₁ L1
  obtain ⟨c,hc,exp⟩ := experiments v hv W hW x₀ hx₀ L0
  refine ⟨c,(m:ℝ)*(m+1)/(2*v*(v+m)),hc,?_⟩
  filter_upwards [exp,eventually_ge_atTop m] with j hj hm
  obtain ⟨ex⟩ := hj
  letI := ex.meas
  letI := ex.prob
  have hB : 0 < (c:ℝ)*((v:ℝ)*(v-1))^j := by positivity
  have bound := repeatedCohorts ex.gain ex.inventory _ (j+1) m v x₁ _ _ _ R ex.allowance hv0
    (show m≤j+1 by omega) hB.le hR (fun k =>
      mul_nonneg hW'.le (sub_nonneg.mpr (one_le_pow₀ hb.le))) ex.rows level ex.split ex.integrable
      ex.compare_payoffs
  push_cast at bound
  exact normalize (by positivity) hB bound

#print axioms sharpFromCohorts
#print axioms repeatedCohorts
#print axioms normalize
end SharedBuffer.Cohorts
