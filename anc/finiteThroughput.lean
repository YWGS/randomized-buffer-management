import finitePhysical
import stockPolicy

set_option maxRecDepth 20000
set_option exponentiation.threshold 5000

namespace BufferWitness.Physical
open HiddenStock

theorem prefix_budget (n : Nat) (hn : n≤1600) :
    BufferWitness.total (fun j => groupSize j*eventTime j) n + population n*eventTime n =
      n*(19*agingStep 0) := by
  induction n with
  | zero => simp [BufferWitness.total, eventTime]
  | succ n ih =>
    have hp := ih (by omega)
    have hc := current_population n (by omega)
    have hnext := next_population n
    have age := age_step n 0 (by omega)
    simp only [Nat.add_zero] at age
    change BufferWitness.total _ n + groupSize n * eventTime n +
      population (n+1) * (eventTime n + duration n) = (n+1)*(19*agingStep 0)
    rw [hc, Nat.mul_assoc] at hp
    rw [hnext, Nat.mul_add, Nat.mul_assoc, Nat.mul_assoc, age, Nat.add_mul n 1 (19*agingStep 0), Nat.one_mul]
    omega

theorem full_prefix_budget :
    BufferWitness.total (fun j => groupSize j*eventTime j) 1600 +
      population 1600*eventTime 1600=prior :=
  (prefix_budget 1600 (by decide)).trans (by decide)

def serving (q : Nat → α → Nat) (ports : List α) (s n : Nat) :=
  (slots (deliveries q ports) s n).sum

theorem by_label (q : Nat → α → Nat) (ports : List α) (s n : Nat) :
    serving q ports s n =
      HiddenStock.total ports (fun l => (slots (fun t => tx (q t l)) s n).sum) := by
  induction n generalizing s with
  | zero => simp [serving, slots, total_const]
  | succ n ih =>
    change deliveries q ports s + serving q ports (s+1) n = _
    simp only [slots, List.sum_cons]
    rw [HiddenStock.total_add, ih]; rfl

theorem before_service (q : Nat → α → Nat) (ports : List α) (f t : Nat) (ht : t≤f) :
    serving q ports 0 f ≤ ports.length*t+serving q ports t (f-t) := by
  have h := slots_add (deliveries q ports) 0 t (f-t)
  rw [Nat.add_sub_of_le ht, Nat.zero_add] at h
  unfold serving
  rw [h, sum_segments]
  have budget := elapsed_slots _ ports.length (slots_rate _ 0 t ports.length (deliveries_rate q ports))
  rw [slots_length] at budget
  simpa only [Nat.add_le_add_iff_right, Nat.mul_comm] using budget

theorem range_total (g : Nat → Nat) (n : Nat) :
    HiddenStock.total (List.range n) g = BufferWitness.total g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, total_append, ih, HiddenStock.total, BufferWitness.total]

theorem duration_horizon (n : Nat) (hn : n≤1600) : eventTime n ≤ eventTime 1600 + B :=
  Nat.le_trans (total_mono duration n 1600 hn) (Nat.le_add_right _ _)

theorem group_enumeration (a : List (List α)) : (List.range a.length).map (cohort a) = a := by
  apply List.ext_getElem (by simp)
  intro i _ hi
  simp [cohort, List.getElem_map, List.getElem_range, List.getElem?_eq_getElem hi]




theorem one_trace (labels : List α) (hk : labels.length=K)
    (queues : List (List α) → Nat → α → Nat) (last : List (List α) → α → Nat)
    (admit : ∀ a s l, queues a (s+1) l ≤ queues a s l - tx (queues a s l) + offered B (s+1) (last a l))
    (cap : ∀ a s, HiddenStock.total labels (queues a s) ≤ B)
    (h : List (List α) × List α) (hm : h ∈ histories labels (schedule 0 1600))
    (terminal : ∀ l ∈ h.2, last h.1 l ≤ eventTime 1600) :
    let f := eventTime 1600+B
    serving (queues h.1) labels 0 f ≤ prior+B+BufferWitness.total
         (fun j => gainFromRun queues eventTime f h.1 j) 1600 := by
  let f := eventTime 1600+B
  let Q := queues h.1
  let L := fun l => (slots (fun t => tx (Q t l)) 0 f).sum
  let G := gainFromRun queues eventTime f h.1
  have shape := history_shape labels (schedule 0 1600) h hm
  have len := congrArg List.length shape
  simp only [List.length_map, schedule_length] at len
  have part := history_partition labels (schedule 0 1600) h hm
  have hsize (j : Nat) (hj : j<1600) : (cohort h.1 j).length=groupSize j := by
    have hj' : j<h.1.length := by omega
    have h := congrArg (fun l : List Nat => l[j]?) shape
    have idx := schedule_index 0 1600 j hj
    simpa [cohort, List.getElem?_eq_getElem hj', List.getElem?_map, idx] using h
  have rest := history_rest labels (schedule 0 1600) h hm
  have count := counts 0 1600 (by decide)
  rw [starting_population, Nat.zero_add] at count
  have restLen : h.2.length = population 1600 := by omega
  have termGain := no_future_arrivals (closed_from_switch B (eventTime 1600) (f-eventTime 1600)
                h.2 Q (last h.1) (admit h.1) terminal)
  have termStock := total_perm (h.1.flatten++h.2) labels (Q (eventTime 1600)) part
  rw [total_append] at termStock
  have capTerm := cap h.1 (eventTime 1600)
  have boundTerm := before_service Q h.2 f (eventTime 1600) (Nat.le_add_right _ _)
  change serving Q h.2 (eventTime 1600) (f-eventTime 1600) + _ ≤ _ at termGain
  change HiddenStock.total labels (Q (eventTime 1600)) ≤ B at capTerm
  rw [restLen] at boundTerm
  have terminalBound : serving Q h.2 0 f ≤ population 1600*eventTime 1600+B := by omega
  have mains := HiddenStock.total_le (List.range 1600) (fun j => serving Q (cohort h.1 j) 0 f)
      (fun j => groupSize j*eventTime j+G j) (by
        intro j hj
        have js := List.mem_range.mp hj
        have p := before_service Q (cohort h.1 j) f (eventTime j) (duration_horizon _ (by omega))
        rw [hsize j js] at p
        exact p)
  rw [HiddenStock.total_add] at mains
  simp only [range_total] at mains
  have allParts := total_perm (h.1.flatten++h.2) labels L part
  rw [total_append, ← total_flatten] at allParts
  have groups := group_enumeration h.1
  rw [len] at groups
  conv at allParts => lhs; lhs; arg 1; rw [← groups]
  rw [total_map] at allParts
  have into : HiddenStock.total (List.range 1600) (fun j => HiddenStock.total (cohort h.1 j) L)
      = HiddenStock.total (List.range 1600) (fun j => serving Q (cohort h.1 j) 0 f) := by
    apply HiddenStock.total_congr; intro j _; exact (by_label ..).symm
  rw [into, ← by_label Q h.2 0 f, ← by_label Q labels 0 f] at allParts
  change serving Q labels 0 f ≤ prior+B+BufferWitness.total G 1600
  simp only [range_total] at allParts
  have bud := full_prefix_budget
  omega

#print axioms one_trace
end BufferWitness.Physical

namespace BufferWitness.Physical
open HiddenStock

theorem total_commute (xs : List β) (g : β → Nat → Nat) (n : Nat) :
    HiddenStock.total xs (fun x => BufferWitness.total (g x) n) =
     BufferWitness.total (fun j => HiddenStock.total xs (fun x => g x j)) n := by
  induction n with
  | zero => simp [BufferWitness.total, HiddenStock.total_const]
  | succ n ih => simp only [BufferWitness.total, HiddenStock.total_add, ih]

def actual (labels : List α) [DecidableEq α] (policy : Policy α) :=
  HiddenStock.total (histories labels (schedule 0 1600))
    (fun h => serving (run B eventTime policy h.1) labels 0 finish)




theorem actual_policy_bound [DecidableEq α] (labels : List α) (hk : labels.length = K)
    (distinct : labels.Nodup) (policy : Policy α)
    (admit : ∀ a s l, run B eventTime policy a (s+1) l ≤
      run B eventTime policy a s l - tx (run B eventTime policy a s l) +
      offered B (s+1) (expiry eventTime a 0 l))
    (cap : ∀ a s, HiddenStock.total labels (run B eventTime policy a s) ≤ B) :
    3*actual labels policy < 2*(offline*(histories labels (schedule 0 1600)).length) := by
  apply finite_from_policy labels hk distinct policy admit cap (actual labels policy)
    (offline*(histories labels (schedule 0 1600)).length) _ (Nat.le_refl _)
  let H := histories labels (schedule 0 1600)
  let Q := run B eventTime policy
  let G := fun (h : List (List α) × List α) => gainFromRun Q eventTime finish h.1
  have bounds := HiddenStock.total_le H (fun h => serving (Q h.1) labels 0 finish)
      (fun h => (prior+B)+BufferWitness.total (G h) 1600) (by
    intro h hm
    apply one_trace labels hk Q (fun a => expiry eventTime a 0) admit cap h hm
    intro l hl
    have p := history_partition labels (schedule 0 1600) h hm
    have good := (List.pairwise_append.mp (p.nodup_iff.mpr distinct)).2.2
    have away : l ∉ h.1.flatten := fun h' => good l h' l hl rfl
    have len := congrArg List.length (history_shape labels (schedule 0 1600) h hm)
    simp only [List.length_map, schedule_length] at len
    rw [terminal_expiry _ _ _ _ away, Nat.zero_add, len]
    exact Nat.le_refl _)
  rw [HiddenStock.total_add, HiddenStock.total_const, Nat.mul_comm H.length, total_commute] at bounds
  exact bounds

#print axioms actual_policy_bound
end BufferWitness.Physical

namespace BufferWitness.Physical
open HiddenStock




theorem last_empty [DecidableEq α] (labels : List α) (policy : Policy α)
    (admit : ∀ a s l, run B eventTime policy a (s+1) l ≤
      run B eventTime policy a s l - tx (run B eventTime policy a s l) +
      offered B (s+1) (expiry eventTime a 0 l))
    (cap : ∀ a s, HiddenStock.total labels (run B eventTime policy a s) ≤ B)
    (h : List (List α) × List α) (hh : h ∈ histories labels (schedule 0 1600)) :
    serving (run B eventTime policy h.1) labels 0 (finish+1) =
    serving (run B eventTime policy h.1) labels 0 finish := by
  let Q := run B eventTime policy h.1
  have len := congrArg List.length (history_shape labels (schedule 0 1600) h hh)
  simp only [List.length_map, schedule_length] at len
  have zero (l : α) (hl : l∈labels) : Q finish l=0 := by
    have f := assignment_drained B labels eventTime (total_mono duration) h.1 Q
       (admit h.1) (cap h.1) l hl
    rwa [len] at f
  have z := HiddenStock.total_congr labels (fun l => tx (Q finish l)) (fun _ => 0)
    (fun l hl => by simp [zero l hl, tx])
  rw [total_const, Nat.mul_zero] at z
  have split := slots_add (deliveries Q labels) 0 finish 1
  rw [Nat.zero_add] at split
  have one : (slots (deliveries Q labels) finish 1).sum=0 := by
    change HiddenStock.total labels (fun l => tx (Q finish l)) + 0 = 0
    rw [z, Nat.add_zero]
  change (slots (deliveries Q labels) 0 (finish+1)).sum = (slots (deliveries Q labels) 0 finish).sum
  rw [split, sum_segments, one, Nat.add_zero]

theorem exists_below (xs : List β) (s : β → Nat) (target : Nat)
    (bound : 3*HiddenStock.total xs s < 2*(target*xs.length)) :
    ∃ h ∈ xs, 3*s h < 2*target := by
  apply Classical.byContradiction
  intro no
  have h := HiddenStock.total_le xs (fun _ => 2*target) (fun h => 3*s h) (by
    intro h hh
    exact Nat.le_of_not_gt (fun lt => no ⟨h, hh, lt⟩))
  rw [total_scale xs s 3, total_const] at h
  have same : 2*(target*xs.length)=xs.length*(2*target) := by ac_rfl
  rw [same] at bound
  exact (Nat.not_le_of_gt bound) h





theorem hard_trace [DecidableEq α] (labels : List α) (hk : labels.length = K)
    (distinct : labels.Nodup) (policy : Policy α)
    (admit : ∀ a s l, run B eventTime policy a (s+1) l ≤
      run B eventTime policy a s l - tx (run B eventTime policy a s l) +
      offered B (s+1) (expiry eventTime a 0 l))
    (cap : ∀ a s, HiddenStock.total labels (run B eventTime policy a s) ≤ B) :
    ∃ h ∈ histories labels (schedule 0 1600),
      3*serving (run B eventTime policy h.1) labels 0 (finish+1) < 2*offline := by
  obtain ⟨h, hh, bound⟩ := exists_below (histories labels (schedule 0 1600))
    (fun h => serving (run B eventTime policy h.1) labels 0 finish) offline
    (actual_policy_bound labels hk distinct policy admit cap)
  refine ⟨h, hh, ?_⟩
  rw [last_empty labels policy admit cap h hh]
  exact bound

#print axioms hard_trace
end BufferWitness.Physical
