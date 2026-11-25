import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic


namespace SharedBuffer.OutcomeTable
open scoped BigOperators

def indexEquiv (xs : List α) (h : 0<xs.length) :
    Fin (xs.length-1+1) ≃ Fin xs.length := finCongr (by omega)

def read (xs : List α) (h : 0<xs.length) (i : Fin (xs.length-1+1)) : α :=
  xs.get (indexEquiv xs h i)

theorem read_mem (xs : List α) (h : 0<xs.length) (i : Fin (xs.length-1+1)) :
    read xs h i ∈ xs := xs.get_mem _

theorem mean_eq (xs : List α) (h : 0<xs.length) (f : α → ℝ) :
    (∑ i : Fin (xs.length-1+1), f (read xs h i)) / Fintype.card (Fin (xs.length-1+1)) =
      (∑ j : Fin xs.length, f (xs.get j)) / xs.length := by
  have num := (indexEquiv xs h).sum_comp (fun j => f (xs.get j))
  change (∑ i, f (xs.get (indexEquiv xs h i))) / _ = _
  rw [num,Fintype.card_fin,show xs.length-1+1=xs.length by omega]

#print axioms mean_eq
end SharedBuffer.OutcomeTable
