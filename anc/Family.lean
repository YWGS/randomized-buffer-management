import Mathlib.Algebra.GeomSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace SharedBuffer.Family
open Finset
open scoped BigOperators

def active (v w n i : ℕ) := v^(n-i)*w^i
def deaths (v w n i : ℕ) := v^(n-1-i)*w^i
def gap (v w b n i : ℕ) := b*v^i*w^(n-1-i)

theorem populations {v w n i : ℕ} (hi : i<n) (hv : v=w+1) :
    active v w n i = v*deaths v w n i ∧
    active v w n (i+1) = w*deaths v w n i ∧
    active v w n i = deaths v w n i + active v w n (i+1) := by
  have he : n-i = (n-1-i)+1 := by omega
  have he' : n-(i+1) = n-1-i := by omega
  simp only [active, deaths, he, he', pow_succ]
  subst v
  constructor
  · ring
  constructor <;> ring

theorem budget {v w b n i : ℕ} (hi : i<n) :
    deaths v w n i * gap v w b n i = b*(v*w)^(n-1) := by
  have he : n-1-i+i = n-1 := by omega
  calc
    _ = b*(v*w)^(n-1-i+i) := by simp only [deaths, gap, mul_pow, pow_add]; ring
    _ = _ := by rw [he]



theorem delayedGap {v w b n j k : ℕ} (hjk : j+k < n) :
    deaths v w n j * gap v w b n (j+k) * w^k = (b*(v*w)^(n-1))*v^k := by
  have he : n-1-j = n-1-(j+k)+k := by omega
  have he' : (n-1-(j+k)) + (j+k) = n-1 := by omega
  let p := n-1-(j+k)
  change v^(n-1-j)*w^j * (b*v^(j+k)*w^p) * w^k = (b*(v*w)^(n-1))*v^k
  change n-1-j = p+k at he
  change p+(j+k) = n-1 at he'
  rw [he, ← he']
  simp only [pow_add, mul_pow]
  ring


theorem age {v w b n j k : ℕ} (hw : 0<w) (hv : v=w+1) (hjk : j+k ≤ n) :
    (deaths v w n j : ℝ) * (∑ l ∈ range k, (gap v w b n (j+l) : ℝ)) =
     (b*(v*w)^(n-1) : ℕ) * (w : ℝ) * (((v:ℝ)/w)^k-1) := by
  let C : ℝ := (b*(v*w)^(n-1) : ℕ)
  have hw' : (w:ℝ) ≠ 0 := by exact_mod_cast hw.ne'
  have hv' : (v:ℝ) = w+1 := by exact_mod_cast hv
  have row (l : ℕ) (hl : l<k) :
      (deaths v w n j : ℝ) * (gap v w b n (j+l) : ℝ) = C * ((v:ℝ)/w)^l := by
    have h := delayedGap (v:=v) (w:=w) (b:=b) (n:=n) (j:=j) (k:=l) (by omega)
    have hc : (deaths v w n j : ℝ) * (gap v w b n (j+l) : ℝ) * (w:ℝ)^l = C*(v:ℝ)^l := by
      dsimp [C]
      exact_mod_cast h
    rw [div_pow, ← mul_div_assoc, eq_div_iff (pow_ne_zero _ hw')]
    exact hc
  change _ = C*(w:ℝ)*_
  rw [mul_sum]
  calc
    _ = ∑ l ∈ range k, C*((v:ℝ)/w)^l := by
      apply sum_congr rfl
      exact fun l hl => row l (mem_range.mp hl)
    _ = C*(∑ l ∈ range k, ((v:ℝ)/w)^l) := (mul_sum ..).symm
    _ = _ := by
      have hg := geom_sum_mul ((v:ℝ)/w) k
      have he : (v:ℝ)/w-1=1/w := by rw [hv']; field_simp
      rw [he] at hg
      rw [← hg]
      field_simp
      ring



theorem offlineCapacity {B K q x : ℝ} {T : ℕ → ℝ} (n : ℕ)
    (hK : 0 ≤ K) (hBK : K ≤ B) (hq : q ≤ (B-K)*x)
    (hT : ∀ k, 0 ≤ T k) (stationary : ∑ k ∈ range n, max (x-T k) 0 ≤ 1) :
    K + ∑ k ∈ range n, max (q-B*T k) 0 ≤ B := by
  have c : 0 ≤ B-K := sub_nonneg.mpr hBK
  have pt (k : ℕ) : max (q-B*T k) 0 ≤ (B-K)*max (x-T k) 0 := by
    have ht := mul_nonneg hK (hT k)
    have hp := mul_le_mul_of_nonneg_left (le_max_left (x-T k) 0) c
    exact max_le (by nlinarith) (mul_nonneg c (le_max_right _ _))
  have hsum := Finset.sum_le_sum (s := range n) (fun k _ => pt k)
  rw [← mul_sum] at hsum
  nlinarith [mul_le_mul_of_nonneg_left stationary c]

#print axioms age
#print axioms offlineCapacity
end SharedBuffer.Family
