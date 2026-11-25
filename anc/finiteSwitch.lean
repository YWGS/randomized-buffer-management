import finitePhysical
import stockRun

set_option maxRecDepth 20000

namespace BufferWitness.Physical
open HiddenStock

def finish := eventTime 1600 + B

def atEvent (labels : List α) (i : Nat) :=
  worlds labels (schedule 0 i) ((groupSize i-1)+1) (schedule (i+1) (1599-i))





theorem finite_from_switch (labels : List α) (hk : labels.length = K)
    (queues : List (List α) → Nat → α → Nat) (last : List (List α) → α → Nat)
    (prefixStock : Nat → List (List α) → α → Nat)
    (admit : ∀ a s l, queues a (s+1) l ≤ queues a s l - tx (queues a s l) + offered B (s+1) (last a l))
    (cap : ∀ a s, HiddenStock.total labels (queues a s) ≤ B)
    (causal : ∀ i < 1600, ∀ w ∈ atEvent labels i, ∀ l,
        queues (assignment w) (eventTime i) l = prefixStock i w.past l)
    (expired : ∀ i < 1600, ∀ w ∈ atEvent labels i, ∀ j, ∀ l ∈ cohort (assignment w) j,
        last (assignment w) l = eventTime j)
    (A O : Nat)
    (online : let H := histories labels (schedule 0 1600)
              A ≤ (prior+B)*H.length + BufferWitness.total
                 (fun j => HiddenStock.total H (fun h => gainFromRun queues eventTime finish h.1 j)) 1600)
    (offline_feasible : offline*(histories labels (schedule 0 1600)).length ≤ O) :
    3*A < 2*O := by
  apply concrete_finite labels hk (gainFromRun queues eventTime finish) A O _ online offline_feasible
  intro i hi
  let past := schedule 0 i
  let after := schedule (i+1) (1599-i)
  have plen : past.length=i := schedule_length 0 i
  have hidx : (old lags i).Sublist (List.range past.length) := plen ▸ old_sublist i
  have before (j : Nat) (hj : j ∈ old lags i) : j<i := List.mem_range.mp ((old_sublist i).subset hj)
  have hsize (j : Nat) (hj : j ∈ old lags i) : past[j]?.getD 0 = groupSize j := by
    have h := schedule_index 0 i j (before j hj)
    simp only [past, h, Nat.zero_add, Option.getD_some]
  have obs := observation_from_run labels past after (groupSize i-1) B finish (old lags i)
    groupSize eventTime queues last (prefixStock i) admit cap
    (by simpa only [plen] using causal i hi) hidx hsize
    (by intro j hj; rw [plen]; exact total_mono _ _ _ (Nat.le_of_lt (before j hj)))
    (by rw [plen]; exact Nat.le_trans (total_mono duration i 1600 (Nat.le_of_lt hi)) (Nat.le_add_right (eventTime 1600) B))
    (expired i hi)
  rw [plen] at obs
  exact ⟨obs⟩

#print axioms finite_from_switch
end BufferWitness.Physical
