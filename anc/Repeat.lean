import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace SharedBuffer.Repeat
open MeasureTheory Finset
open scoped BigOperators

variable {α Ω : Type*} [Fintype α] [Nonempty α] [MeasurableSpace Ω]

private noncomputable def mean (f : α → ℝ) : ℝ := (∑ a, f a) / Fintype.card α

private theorem mean_const (c : ℝ) : mean (fun _ : α => c) = c := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, nsmul_eq_mul, hc]

private theorem mean_affine (f : α → ℝ) (a b : ℝ) :
    mean (fun i => a*f i+b) = a*mean f + b := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, sum_add_distrib, ← mul_sum, nsmul_eq_mul, hc, add_div,
        mul_div_assoc]

private theorem mean_mono {f g : α → ℝ} (h : ∀ i, f i ≤ g i) : mean f ≤ mean g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun i _ => h i)) (by positivity)

noncomputable def traceMean (f : List α → ℝ) : ℕ → ℝ
  | 0 => f []
  | n+1 => mean (fun i => traceMean (fun rest => f (i::rest)) n)

private theorem trace_affine (f : List α → ℝ) (a b : ℝ) (n : ℕ) :
    traceMean (fun l => a*f l+b) n = a*traceMean f n+b := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [traceMean]
    conv_lhs => arg 1; ext i; rw [ih (fun l => f (i::l))]
    exact mean_affine _ _ _

private theorem trace_lower (f : List α → ℝ) (n : ℕ) (c : ℝ)
    (h : ∀ l, l.length=n → c ≤ f l) : c ≤ traceMean f n := by
  induction n generalizing f with
  | zero => exact h [] rfl
  | succ n ih =>
    rw [traceMean, ← mean_const (α:=α) c]
    apply mean_mono
    intro i
    exact ih _ (fun l hl => h (i::l) (by simp [hl]))


def play (g : List α → α → ℝ) (past : List α) : List α → ℝ
  | [] => 0
  | i::rest => g past i + play g (i::past) rest

private theorem trace_upper (g : List α → α → ℝ) (A : ℝ)
    (h : ∀ past, mean (g past) ≤ A) (past : List α) (n : ℕ) :
    traceMean (play g past) n ≤ n*A := by
  induction n generalizing past with
  | zero => simp [traceMean, play]
  | succ n ih =>
    rw [traceMean]
    have point (i : α) : traceMean (fun l => play g past (i::l)) n ≤ (n:ℝ)*A+g past i := by
      have eq := trace_affine (play g (i::past)) 1 (g past i) n
      have er : traceMean (fun l => play g past (i::l)) n =
          traceMean (play g (i::past)) n + g past i := by
        simpa only [one_mul, play, add_comm (g past i)] using eq
      rw [er]
      exact add_le_add_right (ih (i::past)) _
    refine (mean_mono point).trans ?_
    have eq := mean_affine (g past) 1 ((n:ℝ)*A)
    rw [Nat.cast_succ]
    simp only [one_mul] at eq
    rw [show (fun i => (n:ℝ)*A+g past i) = (fun i => g past i + (n:ℝ)*A) by funext; ring, eq]
    linarith [h past]

omit [Nonempty α] in
private theorem trace_integrable {μ : Measure Ω} {f : List α → Ω → ℝ}
    (hf : ∀ l, Integrable (f l) μ) (n : ℕ) :
    Integrable (fun s => traceMean (fun l => f l s) n) μ := by
  induction n generalizing f with
  | zero => exact hf []
  | succ n ih =>
    exact (integrable_finset_sum _ (fun i _ => ih (fun l => hf (i::l)))).div_const _

omit [Nonempty α] in
private theorem trace_integral {μ : Measure Ω} {f : List α → Ω → ℝ}
    (hf : ∀ l, Integrable (f l) μ) (n : ℕ) :
    traceMean (fun l => ∫ s, f l s ∂μ) n =
      ∫ s, traceMean (fun l => f l s) n ∂μ := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [traceMean, mean]
    rw [integral_div, integral_finset_sum]
    · congr 1
      apply sum_congr rfl
      exact fun i _ => ih (fun l => hf (i::l))
    · exact fun i _ => trace_integrable (fun l => hf (i::l)) n




theorem obliviousRepetition {μ : Measure Ω} [IsProbabilityMeasure μ]
    (g : Ω → List α → α → ℝ) (O A R c : ℝ) (hR : 0 ≤ R)
    (integrability : ∀ l, Integrable (fun s => play (g s) [] l) μ)
    (oneCopy : ∀ s past, (∑ a, g s past a) / Fintype.card α ≤ A)
    (competitive : ∀ l, (l.length : ℝ)*O ≤ R*(∫ s, play (g s) [] l ∂μ)+c) :
    O ≤ R*A := by
  have bound (n : ℕ) : (n:ℝ)*O ≤ R*((n:ℝ)*A)+c := by
    have h := trace_lower (fun l => R*(∫ s, play (g s) [] l ∂μ)+c) n ((n:ℝ)*O)
      (fun l hl => hl ▸ competitive l)
    rw [trace_affine, trace_integral integrability] at h
    have hI : (∫ s, traceMean (play (g s) []) n ∂μ) ≤ (n:ℝ)*A := by
      simpa using integral_mono (trace_integrable integrability n) (integrable_const ((n:ℝ)*A))
        (fun s => trace_upper (g s) A (oneCopy s) [] n)
    linarith [mul_le_mul_of_nonneg_left hI hR]
  by_contra! h
  have hp : 0 < O-R*A := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (c/(O-R*A))
  nlinarith [bound n, (div_lt_iff₀ hp).mp hn]

#print axioms obliviousRepetition
end SharedBuffer.Repeat
