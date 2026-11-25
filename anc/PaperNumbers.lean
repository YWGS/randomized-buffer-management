import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace SharedBuffer.PaperNumbers
def T : Nat → Rat
  | 0 => 0
  | k+1 => 20/19 * T k + 1/400

def lagSum : Nat → Rat
  | 0 => 0
  | k+1 => lagSum k + T (k+1)

def x (a m : Nat) : Rat := (1 + lagSum m) / ((a : Rat) + m)

theorem table :
    7837/100000 < T 19 ∧ T 19 < 7838/100000 ∧
    8325/100000 < x 1 19 ∧ x 1 19 < 8326/100000 ∧
    8500/100000 < T 20 ∧ T 20 < 8501/100000 ∧
    3600/100000 < T 11 ∧ T 11 < 3602/100000 ∧
    3863/100000 < x 20 11 ∧ x 20 11 < 3864/100000 ∧
    4040/100000 < T 12 ∧ T 12 < 4041/100000 := by norm_num [x, lagSum, T]

theorem printedFraction :
    (19/400 + (1-1/100000)*(8325/100000)-1/100000 : Rat) /
    (19/400+3864/100000+(1+33/310)/1600) = 1621165677/1076711000 ∧
    (3/2 : Rat) < 1621165677/1076711000 := by norm_num [x, lagSum, T]

#print axioms table
#print axioms printedFraction
end SharedBuffer.PaperNumbers
