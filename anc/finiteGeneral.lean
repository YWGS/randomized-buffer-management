import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp




namespace SharedBuffer.Averaging
open Finset
open scoped BigOperators

def residual (X T : ℕ → ℝ) (i k : ℕ) : ℝ :=
  if k ≤ i then max 0 (X (i-k) - T k) else 0

private theorem residual_nonneg (X T : ℕ → ℝ) (i k : ℕ) :
    0 ≤ residual X T i k := by
  unfold residual
  split <;> simp

private theorem shifted_total (X : ℕ → ℝ) (n k : ℕ) (hkn : k ≤ n) :
    (∑ i ∈ range n, if k ≤ i then X (i-k) else 0) = ∑ i ∈ range (n-k), X i := by
  let f (i : ℕ) : ℝ := if k ≤ i then X (i-k) else 0
  have early : ∑ i ∈ range k, f i = 0 := by
    apply sum_eq_zero
    intro i hi
    simp [f, if_neg (Nat.not_le_of_gt (mem_range.mp hi))]
  calc
    _ = ∑ i ∈ range (k + (n-k)), f i := by simp [f, Nat.add_sub_of_le hkn]
    _ = _ := by
      rw [sum_range_add, early, zero_add]
      apply sum_congr rfl
      intro j hj
      simp [f]


private theorem one_lag (X T : ℕ → ℝ) (n k : ℕ) (v : ℝ)
    (hkn : k ≤ n) (ht : 0 ≤ T k) (cap : ∀ i < n, X i ≤ 1/v) :
    (∑ i ∈ range n, X i) ≤ (∑ i ∈ range n, residual X T i k) +
      n * T k + k * (1/v) := by
  have prefixBound : (∑ i ∈ range (n-k), X i) ≤
      (∑ i ∈ range n, residual X T i k) + n * T k := by
    rw [← shifted_total X n k hkn]
    calc
      _ ≤ ∑ i ∈ range n, (residual X T i k + T k) := by
        apply sum_le_sum
        intro i hi
        by_cases h : k ≤ i
        · simp only [residual, if_pos h]
          linarith [le_max_right (0:ℝ) (X (i-k) - T k)]
        · simpa [residual,h] using ht
      _ = _ := by simp [sum_add_distrib]
  have tail : (∑ j ∈ range k, X ((n-k)+j)) ≤ (k:ℝ)*(1/v) := by
    calc
      _ ≤ ∑ j ∈ range k, (1/v) := by
        apply sum_le_sum
        intro j hj
        apply cap
        have hj' := mem_range.mp hj
        omega
      _ = _ := by simp
  have splitSum := sum_range_add X (n-k) k
  rw [Nat.sub_add_cancel hkn] at splitSum
  linarith

private theorem triangle (m : ℕ) :
    (∑ j ∈ range m, ((j+1:ℕ):ℝ)) = (m:ℝ)*(m+1)/2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring


theorem sum_lag_rows (X T : ℕ → ℝ) (n m : ℕ) (v : ℝ)
    (hv : 0 < v) (hm : m ≤ n) (ht : ∀ k, 0 ≤ T k)
    (rows : ∀ i < n, v * X i + (∑ j ∈ range i, residual X T i (j+1)) ≤ 1) :
    (v+m) * (∑ i ∈ range n, X i) ≤
      n * (1 + ∑ j ∈ range m, T (j+1)) + m*(m+1)/(2*v) := by
  have cap (i : ℕ) (hi : i < n) : X i ≤ 1/v := by
    apply (le_div_iff₀ hv).mpr
    rw [mul_comm]
    have hl := rows i hi
    have hn : 0 ≤ ∑ j ∈ range i, residual X T i (j+1) :=
      sum_nonneg fun j hj => residual_nonneg X T i (j+1)
    linarith
  have truncated (i : ℕ) (hi : i < n) :
      v * X i + (∑ j ∈ range m, residual X T i (j+1)) ≤ 1 := by
    apply le_trans _ (rows i hi)
    apply add_le_add_left
    by_cases h : m ≤ i
    · apply sum_le_sum_of_subset_of_nonneg (range_mono h)
      intro j hj hnj
      exact residual_nonneg X T i (j+1)
    · have eqn : m = i + (m-i) := by omega
      conv_lhs => rw [eqn, sum_range_add]
      have zero : (∑ j ∈ range (m-i), residual X T i (i+j+1)) = 0 := by
        apply sum_eq_zero
        intro j hj
        simp [residual, show ¬ i+j+1 ≤ i by omega]
      rw [zero, add_zero]
  have totalRows := sum_le_sum (s := range n) (fun i hi => truncated i (mem_range.mp hi))
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul, mul_one] at totalRows
  rw [sum_comm] at totalRows
  have averaged := sum_le_sum (s := range m)
    (fun j hj => one_lag X T n (j+1) v (by have : j < m := mem_range.mp hj; omega) (ht _) cap)
  simp only [sum_add_distrib, ← mul_sum, ← sum_mul, sum_const, card_range, nsmul_eq_mul] at averaged
  rw [triangle] at averaged
  have edge : (m:ℝ)*(m+1)/2 * (1/v) = m*(m+1)/(2*v) := by
    field_simp
  linarith only [totalRows, averaged, edge]


theorem stationary_bound (X T : ℕ → ℝ) (n m : ℕ) (v x : ℝ)
    (hv : 0 < v) (hm : m ≤ n) (ht : ∀ k, 0 ≤ T k)
    (rows : ∀ i < n, v * X i + (∑ j ∈ range i, residual X T i (j+1)) ≤ 1)
    (level : (v+m)*x = 1 + ∑ j ∈ range m, T (j+1)) :
    (∑ i ∈ range n, X i) ≤ n*x + m*(m+1)/(2*v*(v+m)) := by
  have main := sum_lag_rows X T n m v hv hm ht rows
  rw [←level] at main
  have pos : 0 < v+(m:ℝ) := add_pos_of_pos_of_nonneg hv (Nat.cast_nonneg _)
  have cmp := (le_div_iff₀ pos).mpr (by simpa [mul_comm] using main)
  calc
    _ ≤ _ := cmp
    _ = _ := by field_simp; ring


theorem stationary_test (X T : ℕ → ℝ) (n m : ℕ) (v x : ℝ)
    (hv : 0 < v) (hm : m ≤ n) (ht : ∀ k, 0 ≤ T k)
    (rows : ∀ i < n, v * X i + (∑ j ∈ range i, residual X T i (j+1)) ≤ 1)
    (level : 1 + ∑ j ∈ range m, T (j+1) ≤ (v+m)*x) :
    (∑ i ∈ range n, X i) ≤ n*x + m*(m+1)/(2*v*(v+m)) := by
  have main := sum_lag_rows X T n m v hv hm ht rows
  have rhs := mul_le_mul_of_nonneg_left level (Nat.cast_nonneg n)
  have main2 := le_trans main (add_le_add_right rhs _)
  have pos : 0 < v+(m:ℝ) := add_pos_of_pos_of_nonneg hv (Nat.cast_nonneg _)
  have cmp := (le_div_iff₀ pos).mpr (by simpa [mul_comm] using main2)
  calc
    _ ≤ _ := cmp
    _ = _ := by field_simp; ring



theorem finite_ratio (X T : ℕ → ℝ) (n m : ℕ) (v x B S q A O R : ℝ)
    (hv : 0 < v) (hB : 0 ≤ B) (hR : 0 ≤ R) (hm : m ≤ n) (ht : ∀ k, 0 ≤ T k)
    (rows : ∀ i < n, v * X i + (∑ j ∈ range i, residual X T i (j+1)) ≤ 1)
    (level : 1 + ∑ j ∈ range m, T (j+1) ≤ (v+m)*x)
    (split : A ≤ S+B*((∑ i ∈ range n, X i)+1))
    (feasible : S+n*q ≤ O) (competitive : O ≤ R*A)
    (den : 0 < S + B*(n*x + m*(m+1)/(2*v*(v+m)) + 1)) :
    (S+n*q)/(S + B*(n*x + m*(m+1)/(2*v*(v+m)) + 1)) ≤ R := by
  have h := stationary_test X T n m v x hv hm ht rows level
  have hA := le_trans split (add_le_add_left (mul_le_mul_of_nonneg_left
    (add_le_add_right h 1) hB) S)
  exact (div_le_iff₀ den).mpr (le_trans feasible
    (le_trans competitive (mul_le_mul_of_nonneg_left hA hR)))

end SharedBuffer.Averaging

#print axioms SharedBuffer.Averaging.sum_lag_rows
#print axioms SharedBuffer.Averaging.stationary_bound

#print axioms SharedBuffer.Averaging.finite_ratio
