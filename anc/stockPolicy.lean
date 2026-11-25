import finiteSwitch
import stockRun

set_option maxRecDepth 20000

namespace HiddenStock



theorem terminal_expiry [DecidableEq α] (date : Nat → Nat)
    (a : List (List α)) (i : Nat) (l : α) (h : l ∉ a.flatten) :
    expiry date a i l = date (i+a.length) := by
  induction a generalizing i with
  | nil => simp [expiry]
  | cons g a ih =>
    have hg : l ∉ g := fun hl => h (by simp [hl])
    have ha : l ∉ a.flatten := fun hl => h (by simp [hl])
    simp only [expiry, if_neg hg, List.length_cons]
    rw [ih (i+1) ha]
    congr 1 <;> omega

end HiddenStock

namespace BufferWitness.Physical
open HiddenStock







theorem finite_from_policy [DecidableEq α] (labels : List α) (hk : labels.length = K)
    (distinct : labels.Nodup) (policy : Policy α)
    (admit : ∀ a s l, run B eventTime policy a (s+1) l ≤
      run B eventTime policy a s l - tx (run B eventTime policy a s l) +
      offered B (s+1) (expiry eventTime a 0 l))
    (cap : ∀ a s, HiddenStock.total labels (run B eventTime policy a s) ≤ B)
    (A O : Nat)
    (online : let H := histories labels (schedule 0 1600)
              A ≤ (prior+B)*H.length + BufferWitness.total (fun j =>
                 HiddenStock.total H (fun h =>
                    gainFromRun (run B eventTime policy) eventTime finish h.1 j)) 1600)
    (offline_feasible : offline*(histories labels (schedule 0 1600)).length ≤ O) :
    3*A < 2*O := by
  apply concrete_finite labels hk (gainFromRun (run B eventTime policy) eventTime finish) A O _
    online offline_feasible
  intro i hi
  let past := schedule 0 i
  let after := schedule (i+1) (1599-i)
  have plen : past.length=i := schedule_length 0 i
  have hidx : (old lags i).Sublist (List.range past.length) := plen ▸ old_sublist i
  have before (j : Nat) (hj : j ∈ old lags i) : j<i := List.mem_range.mp ((old_sublist i).subset hj)
  have hsize (j : Nat) (hj : j ∈ old lags i) : past[j]?.getD 0 = groupSize j := by
    have h := schedule_index 0 i j (before j hj)
    simp only [past,h,Nat.zero_add,Option.getD_some]
  have obs := observation_from_policy labels distinct past after (groupSize i-1) B finish (old lags i)
    groupSize eventTime (total_mono duration) policy admit cap hidx hsize
    (by rw [plen]; exact Nat.le_trans (total_mono duration i 1600 (by omega)) (Nat.le_add_right (eventTime 1600) B))
  rw [plen] at obs
  exact ⟨obs⟩

#print axioms HiddenStock.terminal_expiry
#print axioms finite_from_policy
end BufferWitness.Physical
