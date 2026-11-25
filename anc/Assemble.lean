import Ratio
import limit_bridge

namespace SharedBuffer.Assemble
open Filter BufferLimit




def FiniteLowerBounds (R : ℝ) : Prop :=
  ∀ (v : ℕ), 3 ≤ v → ∀ (W : ℚ), 0 < W → ∀ x₀ x₁ : ℝ,
    0 < x₀ → Level 1 (v/((v:ℝ)-1)) W x₀ → 0 < x₁ → Level v (v/((v:ℝ)-1)) W x₁ →
    ∃ (bcap : ℕ) (E : ℝ), 0 < bcap ∧ ∀ᶠ j : ℕ in atTop,
      let B : ℝ := bcap*((v:ℝ)*(v-1))^j
      let K : ℝ := (v:ℝ)^(j+1)
      (W:ℝ) + (⌊(B-K)*x₀⌋ : ℤ)/B ≤ R*((W:ℝ)+x₁+(E+1)/(j+1))

theorem fixedArity {R : ℝ} (finite : FiniteLowerBounds R) : FixedArityBound R := by
  intro v hv W hW
  have hv' : (3:ℝ) ≤ v := by exact_mod_cast hv
  have hv0 : (0:ℝ)<v := by linarith
  have hw : 0 < (v:ℝ)-1 := by linarith
  have hw1 : 1<(v:ℝ)-1 := by linarith
  have hW' : (0:ℝ)<W := by exact_mod_cast hW
  let b : ℝ := v/((v:ℝ)-1)
  have hb : 1 < b := (lt_div_iff₀ hw).mpr (by linarith)
  obtain ⟨x₀,⟨h0,L0⟩,_⟩ := exists_unique_level (a:=1) (le_refl _) hb hW'
  obtain ⟨x₁,⟨h1,L1⟩,_⟩ := exists_unique_level (a:=(v:ℝ)) (by linarith) hb hW'
  obtain ⟨c,E,hc,he⟩ := finite v hv W hW x₀ x₁ h0 L0 h1 L1
  refine ⟨x₀,x₁,fun x _ hx => level_greatest (by norm_num) L0 hx,L1.1,h1.le,?_⟩
  have hc' : (0:ℝ) < c := by exact_mod_cast hc
  have hvw : 1 < (v:ℝ)*(v-1) := by nlinarith
  apply SharedBuffer.Ratio.fixedSpacing (W:ℝ) x₀ x₁ E R ((v:ℝ)/c) (1/(c:ℝ))
    (1/((v:ℝ)-1)) (1/((v:ℝ)*(v-1))) (by linarith) (by positivity)
    ((div_lt_one hw).mpr hw1) (by positivity) ((div_lt_one (by positivity)).mpr hvw)
  filter_upwards [he] with j hj
  let B : ℝ := c*((v:ℝ)*(v-1))^j
  let K : ℝ := (v:ℝ)^(j+1)
  have hB : 0 < B := by dsimp [B]; positivity
  change (W:ℝ) + (⌊(B-K)*x₀⌋ : ℤ)/B ≤ _ at hj
  have hratio : K/B = (v:ℝ)/c*(1/((v:ℝ)-1))^j := by
    dsimp [K,B]
    rw [mul_pow, pow_succ, div_pow, one_pow]
    field_simp; ring
  have hinv : 1/B = (1/(c:ℝ))*(1/((v:ℝ)*(v-1)))^j := by
    dsimp [B]
    rw [div_pow, one_pow]
    ring
  rw [← hratio, ← hinv]
  have low := div_le_div_of_nonneg_right (Int.sub_one_lt_floor ((B-K)*x₀)).le hB.le
  calc
    _ = (W:ℝ) + ((B-K)*x₀-1)/B := by field_simp; ring
    _ ≤ _ := add_le_add_left low _
    _ ≤ _ := by simpa [div_eq_mul_inv] using hj



theorem sharpFromFinite {R : ℝ} (finite : FiniteLowerBounds R) :
    ∃ r : ℝ, 3/2 < r ∧ r < 2 ∧ SharedBuffer.Ratio.entropy r = 1 ∧
      (∀ t, 1<t → SharedBuffer.Ratio.entropy t=1 → t=r) ∧ r ≤ R := by
  obtain ⟨r,hlo,hhi,eqr,unique⟩ := SharedBuffer.Ratio.uniqueSharpRoot
  refine ⟨r,hlo,hhi,eqr,unique,?_⟩
  by_contra! h
  let q := (max R 1 + r)/2
  have h1 : 1<r := by linarith
  have hmax : max R 1 < r := max_lt h h1
  have hq1 : 1<q := by dsimp [q]; linarith [le_max_right R (1:ℝ)]
  have hqr : q<r := by dsimp [q]; linarith
  have hRq : R<q := by dsimp [q]; linarith [le_max_left R (1:ℝ)]
  have hg : g q < 1 := by
    rw [←eqr]
    exact SharedBuffer.Ratio.entropyStrict hq1 h1 hqr
  have bound := sharp_from_stationary_ratio (fixedArity finite) hq1 (hqr.trans hhi) hg
  exact (not_le_of_gt hRq) bound

#print axioms sharpFromFinite
end SharedBuffer.Assemble
