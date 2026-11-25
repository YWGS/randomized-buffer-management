import finiteGeneral
import Mathlib.Data.Real.Archimedean

namespace SharedBuffer.Referee
open Finset SharedBuffer.Averaging
open scoped BigOperators



theorem rowTransfer {X T : ℕ → ℝ} {i : ℕ} {v z : ℝ}
    (hz : z ≤ 1) (hT : ∀ k, 0 ≤ T k)
    (realRow : v*X i + (∑ j ∈ range i, residual X (fun k => z*T k) i (j+1)) ≤ 1) :
    v*X i + (∑ j ∈ range i, residual X T i (j+1)) ≤ 1 := by
  apply le_trans _ realRow
  apply add_le_add_left
  apply sum_le_sum
  intro j _
  unfold residual
  split
  · have price : z*T (j+1) ≤ T (j+1) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hz (hT (j+1))
    exact max_le_max le_rfl (sub_le_sub_left price _)
  · rfl

theorem scaleAge (h B₀ s : ℕ) (hB : 0<h*B₀+s) :
    ((h*B₀ : ℕ):ℝ)/(h*B₀+s:ℕ) ≤ 1 := by
  have hpos : (0:ℝ) < ((h*B₀+s : ℕ):ℝ) := by exact_mod_cast hB
  apply (div_le_one hpos).mpr
  exact_mod_cast Nat.le_add_right (h*B₀) s



theorem scaledResidual (h q d age : ℕ) : h*q - d*(h*age) = h*(q-d*age) := by
  rw [Nat.mul_sub]
  congr 1
  ring

theorem offlinePeak (h B₀ K s : ℕ) (hh : 1 ≤ h) (hk : K ≤ B₀) :
    h*(B₀-K)+K ≤ h*B₀+s := by
  have he : h*B₀ = h*(B₀-K)+h*K := by
    rw [←Nat.mul_add, Nat.sub_add_cancel hk]
  have hc : K ≤ h*K := by simpa using Nat.mul_le_mul_right K hh
  omega



theorem onlineScaled {X T : ℕ → ℝ} (n m : ℕ) {v h B₀ s B z x S A : ℝ}
    (hv : 0 < v) (hB : 0 ≤ B) (hm : m ≤ n) (hz : z ≤ 1)
    (decomp : B=h*B₀+s) (hT : ∀ k, 0 ≤ T k)
    (rows : ∀ i<n, v*X i + (∑ j ∈ range i, residual X (fun k => z*T k) i (j+1)) ≤ 1)
    (level : (v+m)*x=1+∑ j ∈ range m, T (j+1))
    (pay : A ≤ h*S+B*((∑ i ∈ range n, X i)+1)) :
    let C := n*x+m*(m+1)/(2*v*(v+m))+1
    A ≤ h*(S+B₀*C)+s*C := by
  dsimp only
  have u := stationary_bound X T n m v x hv hm hT
    (fun i hi => rowTransfer hz hT (rows i hi)) level
  apply pay.trans
  rw [show h*(S+B₀*(n*x+↑m*(↑m+1)/(2*v*(v+↑m))+1))+
    s*(n*x+↑m*(↑m+1)/(2*v*(v+↑m))+1) =
    h*S+B*(n*x+↑m*(↑m+1)/(2*v*(v+↑m))+1) by rw [decomp]; ring]
  exact add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right u 1) hB) _



theorem everyLargeCapacity (B₀ : ℕ) (hbase : 0 < B₀)
    {O U C rho : ℝ} (strict : 0 < O-rho*U) (hc : 0 ≤ rho*C) :
    ∃ threshold : ℕ, ∀ B : ℕ, threshold ≤ B →
      ∃ h s : ℕ, 0<h ∧ s<B₀ ∧ B=h*B₀+s ∧
        rho*((h:ℝ)*U+(s:ℝ)*C)<(h:ℝ)*O := by
  obtain ⟨H,hH⟩ := exists_nat_gt ((B₀:ℝ)*(rho*C)/(O-rho*U))
  refine ⟨(H+1)*B₀, ?_⟩
  intro B hB
  let h := B/B₀
  let s := B%B₀
  have hquot : H+1 ≤ h := (Nat.le_div_iff_mul_le hbase).mpr hB
  have hpos : 0<h := by omega
  have hs : s<B₀ := Nat.mod_lt B hbase
  have decomp : B=h*B₀+s := by
    simpa [h,s,Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div B B₀).symm
  refine ⟨h,s,hpos,hs,decomp,?_⟩
  have Hh : (H:ℝ) ≤ h := by exact_mod_cast (show H≤h by omega)
  have sh : (s:ℝ) ≤ B₀ := by exact_mod_cast hs.le
  have lb := (div_lt_iff₀ strict).mp (lt_of_lt_of_le hH Hh)
  nlinarith [mul_le_mul_of_nonneg_right sh hc]






theorem fractionalStep (p F a m y L : ℝ)
    (hf : 0≤F) (ha : 0≤a) (hm : 0≤m)
    (adm : m≤p+a) (ym : y≤m) (y1 : y≤1)
    (prior : 0≤p-F ∧ p-F≤L) :
    let f := min m (F+a)
    let z := min 1 f
    0≤f ∧ f≤m ∧ f≤F+a ∧
    0≤(m-y)-(f-z) ∧ (m-y)-(f-z) ≤ L+z-y ∧ 0≤L+z-y := by
  dsimp only
  obtain ⟨p₁,p₂⟩ := prior
  rcases le_total m (F+a) with h|h
  · rw [min_eq_left h]
    rcases le_total 1 m with h'|h'
    · rw [min_eq_left h']
      exact ⟨hm,le_rfl,h,by linarith,by linarith,by linarith⟩
    · rw [min_eq_right h']
      exact ⟨hm,le_rfl,h,by linarith,by linarith,by linarith⟩
  · rw [min_eq_right h]
    rcases le_total 1 (F+a) with h'|h'
    · rw [min_eq_left h']
      exact ⟨by linarith,h,le_rfl,by linarith,by linarith,by linarith⟩
    · rw [min_eq_right h']
      exact ⟨by linarith,h,le_rfl,by linarith,by linarith,by linarith⟩

#print axioms everyLargeCapacity
#print axioms onlineScaled
#print axioms fractionalStep
end SharedBuffer.Referee
