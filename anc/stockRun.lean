import stock




namespace HiddenStock

theorem total_perm (xs ys : List α) (f : α → Nat) (h : xs.Perm ys) :
    total xs f = total ys f := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [total, ih]
  | swap _ _ _ => simp [total, Nat.add_left_comm]
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

theorem split_partition (labels : List α) (d : Nat) (b : List α × List α)
    (hb : b ∈ splits labels d) : (b.1 ++ b.2).Perm labels := by
  induction labels generalizing b d with
  | nil =>
    cases d with
    | zero => simp [splits] at hb; subst b; apply List.Perm.refl
    | succ d => simp [splits] at hb
  | cons x xs ih =>
    cases d with
    | zero => simp [splits] at hb; subst b; apply List.Perm.refl
    | succ d =>
      simp only [splits, List.mem_append, List.mem_map] at hb
      rcases hb with ⟨c,hc,e⟩ | ⟨c,hc,e⟩
      · subst b; exact List.perm_middle.trans ((ih (d+1) c hc).cons x)
      · subst b; exact (ih d c hc).cons x

theorem history_partition (labels : List α) (past : List Nat) (h : List (List α) × List α)
    (hm : h ∈ histories labels past) : (h.1.flatten ++ h.2).Perm labels := by
  induction past generalizing labels h with
  | nil => simp [histories] at hm; subst h; apply List.Perm.refl
  | cons d ds ih =>
    simp only [histories, List.mem_flatMap, List.mem_map] at hm
    rcases hm with ⟨b,hb,s,hs,e⟩
    subst h
    simp only [List.flatten_cons, List.append_assoc]
    exact ((ih b.2 s hs).append_left b.1).trans (split_partition labels d b hb)

theorem history_shape (labels : List α) (past : List Nat) (h : List (List α) × List α)
    (hm : h ∈ histories labels past) : h.1.map List.length = past := by
  induction past generalizing labels h with
  | nil => simp [histories] at hm; subst h; rfl
  | cons d ds ih =>
    simp only [histories, List.mem_flatMap, List.mem_map] at hm
    rcases hm with ⟨b,hb,s,hs,e⟩; subst h
    have hb' : b.1 ∈ blocks labels d := by rw [← split_blocks]; exact List.mem_map.mpr ⟨b,hb,rfl⟩
    simp [selected_length _ _ _ hb', ih _ _ hs]

theorem world_facts (labels : List α) (past future : List Nat) (d : Nat) (w : World α)
    (hw : w ∈ worlds labels past d future) :
    (w.past.flatten ++ w.live).Perm labels ∧ w.past.map List.length = past ∧ w.chosen.length=d := by
  simp only [worlds, List.mem_flatMap] at hw
  rcases hw with ⟨h,hh,hw'⟩
  simp only [layer, List.mem_flatMap, List.mem_map] at hw'
  rcases hw' with ⟨b,hb,s,_,e⟩
  subst w
  have hb' : b.1 ∈ blocks h.2 d := by rw [← split_blocks]; exact List.mem_map.mpr ⟨b,hb,rfl⟩
  exact ⟨history_partition _ _ _ hh, history_shape _ _ _ hh, selected_length _ _ _ hb'⟩

def tx (q : Nat) := if q=0 then 0 else 1

theorem port_rate (q : Nat) : tx q ≤ 1 := by unfold tx; split <;> omega
theorem stock_covers_tx (q : Nat) : tx q ≤ q := by unfold tx; split <;> omega

def slots (f : Nat → Nat) (start : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => f start :: slots f (start+1) n

theorem slots_length (f : Nat → Nat) (t n : Nat) : (slots f t n).length = n := by
  induction n generalizing t <;> simp_all [slots]

theorem slots_add (f : Nat → Nat) (t n m : Nat) :
    slots f t (n+m) = slots f t n ++ slots f (t+n) m := by
  induction n generalizing t with
  | zero => simp [slots]
  | succ n ih =>
    simp only [Nat.succ_add, slots, List.cons_append, List.cons.injEq, true_and]
    rw [ih]
    congr 2 <;> omega

theorem slots_rate (f : Nat → Nat) (t n r : Nat) (hr : ∀ s, f s ≤ r) :
    ∀ a ∈ slots f t n, a ≤ r := by
  induction n generalizing t with
  | zero => simp [slots]
  | succ n ih =>
    intro a ha
    simp only [slots, List.mem_cons] at ha
    rcases ha with h | h
    · subst a; apply hr
    · exact ih _ _ h

def deliveries (q : Nat → α → Nat) (ports : List α) (s : Nat) :=
  total ports (fun l => tx (q s l))

theorem deliveries_rate (q : Nat → α → Nat) (ports : List α) (s : Nat) :
    deliveries q ports s ≤ ports.length := by
  have h := total_le ports (fun l => tx (q s l)) (fun _ => 1)
              (fun l _ => port_rate (q s l))
  simpa [deliveries, total_const] using h




theorem closed_from_switch (B t n : Nat) (ports : List α) (q : Nat → α → Nat) (last : α → Nat)
    (admit : ∀ s l, q (s+1) l ≤ q s l - tx (q s l) + offered B (s+1) (last l))
    (expired : ∀ l ∈ ports, last l ≤ t) :
    Closed ports.length (total ports (q t)) (slots (deliveries q ports) t n)
            (total ports (q (t+n))) := by
  induction n generalizing t with
  | zero => simpa [slots] using Closed.nil (size:=ports.length) (total ports (q t))
  | succ n ih =>
    have step : deliveries q ports t + total ports (q (t+1)) ≤ total ports (q t) := by
      unfold deliveries; rw [← total_add]
      apply total_le; intro l hl
      have h := admit t l
      have hx := expired l hl
      have heq : offered B (t+1) (last l) = 0 := by simp [offered,show ¬t+1≤last l by omega]
      rw [heq] at h
      have hs := stock_covers_tx (q t l)
      omega
    have tail := ih (t+1) (by intro l hl; have ht := expired l hl; omega)
    have hend : (t+1)+n = t+(n+1) := by omega
    rw [hend] at tail
    exact Closed.step (deliveries_rate q ports t) step tail

theorem total_flatten (sets : List (List α)) (f : α → Nat) :
    total sets (fun s => total s f) = total sets.flatten f := by
  induction sets <;> simp_all [total,total_append]

theorem sublist_total (xs ys : List α) (p : α → Nat) (h : xs.Sublist ys) :
    total xs p ≤ total ys p := by
  induction h with
  | slnil => simp [total]
  | cons _ _ ih => simp [total]; omega
  | cons₂ _ _ ih => simp [total]; omega



theorem partial_capacity (labels : List α) (past future : List Nat) (d B : Nat)
    (w : World α) (p : α → Nat) (old : List Nat) (cohort : Nat → List α)
    (hw : w ∈ worlds labels past d future) (sub : (old.map cohort).Sublist w.past)
    (cap : total labels p ≤ B) :
    total w.live p + total old (fun j => total (cohort j) p) ≤ B := by
  have h := sublist_total _ _ (fun l => total l p) sub
  rw [total_map, total_flatten] at h
  have h' := total_perm _ _ p (world_facts labels past future d w hw).1
  rw [total_append] at h'
  omega

def cohort (a : List (List α)) (j : Nat) : List α := a[j]?.getD []
def gainFromRun (q : List (List α) → Nat → α → Nat) (date : Nat → Nat) (finish : Nat)
    (a : List (List α)) (j : Nat) := (slots (deliveries (q a) (cohort a j))
                                         (date j) (finish-date j)).sum

theorem current_cohort (labels : List α) (past future : List Nat) (d : Nat)
    (w : World α) (hw : w ∈ worlds labels past d future) :
    cohort (assignment w) past.length = w.chosen := by
  have hl := congrArg List.length (world_facts labels past future d w hw).2.1
  simp only [List.length_map] at hl
  unfold cohort assignment
  rw [List.getElem?_append_right (by omega)]
  rw [show past.length-w.past.length=0 by omega]
  rfl

theorem earlier_cohorts (w : World α) :
    (List.range w.past.length).map (cohort (assignment w)) = w.past := by
  apply List.ext_getElem (by simp); intro i _ hi
  simp [List.getElem_map, List.getElem_range, cohort, assignment,
        List.getElem?_append_left hi, List.getElem?_eq_getElem hi]

theorem earlier_shape (labels : List α) (past future : List Nat) (d : Nat)
    (w : World α) (hw : w ∈ worlds labels past d future) (j : Nat) (hj : j < past.length) :
    (cohort (assignment w) j).length = past[j] := by
  have h := (world_facts labels past future d w hw).2.1
  have hl := congrArg List.length h
  simp only [List.length_map] at hl
  have hwj : j < w.past.length := by omega
  have e := congrArg (fun a : List Nat => a[j]?) h
  simpa [cohort, assignment, List.getElem?_append_left hwj,
         List.getElem?_eq_getElem hwj, List.getElem?_eq_getElem hj] using e

theorem sum_segments (a b : List Nat) : (a++b).sum = a.sum+b.sum := by
  induction a <;> simp_all [Nat.add_assoc]







def observation_from_run (labels : List α) (past future : List Nat) (k B finish : Nat)
    (old : List Nat) (nPorts date : Nat → Nat)
    (q : List (List α) → Nat → α → Nat) (last : List (List α) → α → Nat)
    (stock : List (List α) → α → Nat)
    (admit : ∀ a s l, q a (s+1) l ≤ q a s l - tx (q a s l) + offered B (s+1) (last a l))
    (cap : ∀ a s, total labels (q a s) ≤ B)
    (causal : ∀ w ∈ worlds labels past (k+1) future, ∀ l,
                q (assignment w) (date past.length) l = stock w.past l)
    (oldIndex : old.Sublist (List.range past.length))
    (sizes : ∀ j ∈ old, past[j]?.getD 0 = nPorts j)
    (pastDates : ∀ j ∈ old, date j ≤ date past.length)
    (endDate : date past.length ≤ finish)
    (expired : ∀ w ∈ worlds labels past (k+1) future, ∀ j, ∀ l ∈ cohort (assignment w) j,
                    last (assignment w) l = date j) :
    Observation labels past future k past.length B old nPorts (fun j => date past.length-date j)
      (gainFromRun q date finish) := by
  let time := date past.length
  let C := fun (w : World α) j => cohort (assignment w) j
  let Q := fun (w : World α) => q (assignment w)
  have oldLen (w : World α) (hw : w ∈ worlds labels past (k+1) future) (j : Nat) (hj : j ∈ old) :
      (C w j).length = nPorts j := by
    have hj' : j < past.length := List.mem_range.mp (oldIndex.subset hj)
    exact (earlier_shape _ _ _ _ w hw j hj').trans (by simpa [List.getElem?_eq_getElem hj'] using sizes j hj)
  refine {
    stock := stock
    kept := fun w j => total (C w j) (Q w time)
    current := fun w => slots (deliveries (Q w) w.chosen) time (finish-time)
    early := fun w j => slots (deliveries (Q w) (C w j)) (date j) (time-date j)
    late := fun w j => slots (deliveries (Q w) (C w j)) time (finish-time)
    currentClosed := ?_, pastRate := ?_, pastClosed := ?_, capacity := ?_,
    sameCurrent := ?_, samePast := ?_ }
  · intro w hw
    have hc := current_cohort labels past future (k+1) w hw
    have hl := (world_facts labels past future (k+1) w hw).2.2
    have e := total_congr w.chosen (Q w time) (stock w.past) (fun l _ => causal w hw l)
    have h := closed_from_switch B time (finish-time) w.chosen (Q w) (last (assignment w))
      (admit (assignment w)) (by
        intro l hl'; have h := expired w hw past.length l (by rwa [hc]); exact Nat.le_of_eq h)
    rw [hl,e] at h
    exact ⟨_,h⟩
  · intro w hw j hj
    exact ⟨slots_length .., slots_rate _ _ _ _ (fun s =>
      Nat.le_trans (deliveries_rate (Q w) (C w j) s) (Nat.le_of_eq (oldLen w hw j hj)))⟩
  · intro w hw j hj
    have h := closed_from_switch B time (finish-time) (C w j) (Q w) (last (assignment w))
      (admit (assignment w)) (by
        intro l hl; exact Nat.le_trans (Nat.le_of_eq (expired w hw j l hl)) (pastDates j hj))
    rw [oldLen w hw j hj] at h
    exact ⟨_,h⟩
  · intro w hw
    have hl := congrArg List.length (world_facts labels past future (k+1) w hw).2.1
    simp only [List.length_map] at hl
    have sub := oldIndex.map (C w)
    rw [← hl, earlier_cohorts] at sub
    have h := partial_capacity labels past future (k+1) B w (Q w time) old
      (C w) hw sub (cap (assignment w) time)
    rw [total_congr w.live (Q w time) (stock w.past) (fun l _ => causal w hw l)] at h
    exact h
  · intro w hw
    simp [gainFromRun, current_cohort labels past future (k+1) w hw, Q, time]
  · intro w hw j hj
    have h₁ : date j ≤ time := pastDates j hj
    have h₂ : time ≤ finish := endDate
    have h := slots_add (deliveries (Q w) (C w j)) (date j) (time-date j) (finish-time)
    rw [show time-date j+(finish-time) = finish-date j by omega,
        show date j+(time-date j)=time by omega] at h
    exact (sum_segments ..).symm.trans (congrArg List.sum h.symm)

#print axioms observation_from_run
end HiddenStock

namespace HiddenStock



def expiry [DecidableEq α] (date : Nat → Nat) : List (List α) → Nat → α → Nat
  | [], i, _ => date i
  | g :: a, i, l => if l ∈ g then date i else expiry date a (i+1) l

theorem expiry_lower [DecidableEq α] (date : Nat → Nat) (mono : ∀ i j, i≤j → date i≤date j)
    (a : List (List α)) (i : Nat) (l : α) : date i ≤ expiry date a i l := by
  induction a generalizing i with
  | nil => exact Nat.le_refl _
  | cons g a ih =>
    unfold expiry; split
    · exact Nat.le_refl _
    · exact Nat.le_trans (mono i (i+1) (by omega)) (ih (i+1))

theorem same_offers_through_event [DecidableEq α] (B t : Nat) (date : Nat → Nat)
    (mono : ∀ i j, i≤j → date i≤date j) (past future : List (List α)) (i : Nat) (l : α)
    (ht : t ≤ date (i+past.length)) :
    offered B t (expiry date (past++future) i l) = offered B t (expiry date past i l) := by
  induction past generalizing i with
  | nil =>
    simp only [List.nil_append, expiry]; simp only [List.length_nil,Nat.add_zero] at ht
    exact same_observed_offer B t (date i) _ (date i) ht
      (expiry_lower date mono future i l) (Nat.le_refl _)
  | cons g gs ih =>
    simp only [List.cons_append, expiry]; split
    · rfl
    · apply ih (i+1)
      rw [show i+1+gs.length = i+(g::gs).length by simp; omega]; exact ht




abbrev Policy (α : Type u) := List (α → Nat) → α → Nat

def run [DecidableEq α] (B : Nat) (date : Nat → Nat) (policy : Policy α)
    (a : List (List α)) (t : Nat) : α → Nat :=
  policy ((List.range (t+1)).map (fun s l => offered B s (expiry date a 0 l)))



theorem run_causal [DecidableEq α] (B : Nat) (date : Nat → Nat)
    (mono : ∀ i j, i≤j → date i≤date j) (policy : Policy α) (w : World α) :
    run B date policy (assignment w) (date w.past.length) =
    run B date policy w.past (date w.past.length) := by
  unfold run; apply congrArg policy
  apply List.map_congr_left; intro t ht
  funext l; exact same_offers_through_event B t date mono w.past (w.chosen::w.future) 0 l
    (by simp only [Nat.zero_add]; have h := List.mem_range.mp ht; omega)

theorem world_full_partition (labels : List α) (past future : List Nat) (d : Nat)
    (w : World α) (hw : w ∈ worlds labels past d future) :
    ∃ left, ((assignment w).flatten ++ left).Perm labels := by
  simp only [worlds,List.mem_flatMap] at hw
  obtain ⟨h,hh,hw'⟩ := hw
  simp only [layer,List.mem_flatMap,List.mem_map] at hw'
  obtain ⟨b,hb,s,hs,rfl⟩ := hw'
  have e₁ := history_partition _ _ _ hh
  have e₂ := split_partition _ _ _ hb
  have e₃ := history_partition _ _ _ hs
  refine ⟨s.2,?_⟩
  simp only [assignment,List.flatten_append,List.flatten_cons,List.append_assoc]
  exact ((e₃.append_left b.1).trans e₂ |>.append_left h.1.flatten).trans e₁

theorem mem_flatten_of_mem_cohort (a : List (List α)) (j : Nat) (l : α) (hl : l ∈ cohort a j) :
    l ∈ a.flatten := by
  by_cases h : j<a.length
  · apply List.mem_flatten.mpr; refine ⟨a[j],List.getElem_mem h,?_⟩
    simpa [cohort,List.getElem?_eq_getElem h] using hl
  · simp [cohort,List.getElem?_eq_none (by omega : a.length≤j)] at hl

theorem expiry_at_cohort [DecidableEq α] (date : Nat → Nat) (a : List (List α))
    (nd : a.flatten.Nodup) (j i : Nat) (l : α) (hl : l ∈ cohort a j) :
    expiry date a i l = date (i+j) := by
  induction a generalizing i j with
  | nil => simp [cohort] at hl
  | cons g a ih =>
    simp only [List.flatten_cons, List.Nodup, List.pairwise_append] at nd
    cases j with
    | zero =>
      have hg : l∈g := by simpa [cohort] using hl
      simp [expiry, hg]
    | succ j =>
      have ha : l∈cohort a j := by simpa [cohort] using hl
      have hg : l∉g := by
        intro hg; exact nd.2.2 l hg l (mem_flatten_of_mem_cohort a j l ha) rfl
      simp only [expiry,if_neg hg]
      rw [ih nd.2.1 j (i+1) ha]
      congr 1 <;> omega




def observation_from_policy [DecidableEq α] (labels : List α) (distinct : labels.Nodup)
    (past future : List Nat) (k B finish : Nat) (old : List Nat) (nPorts date : Nat → Nat)
    (mono : ∀ i j, i≤j → date i≤date j) (policy : Policy α)
    (admit : ∀ a s l, run B date policy a (s+1) l ≤
      run B date policy a s l - tx (run B date policy a s l) + offered B (s+1) (expiry date a 0 l))
    (cap : ∀ a s, total labels (run B date policy a s) ≤ B)
    (oldIndex : old.Sublist (List.range past.length))
    (sizes : ∀ j ∈ old, past[j]?.getD 0 = nPorts j) (endDate : date past.length ≤ finish) :
    Observation labels past future k past.length B old nPorts (fun j => date past.length-date j)
      (gainFromRun (run B date policy) date finish) := by
  refine observation_from_run labels past future k B finish old nPorts date (run B date policy)
    (fun a => expiry date a 0) (fun past => run B date policy past (date past.length)) admit cap
    ?_ oldIndex sizes ?_ endDate ?_
  · intro w hw l
    have hl := congrArg List.length (world_facts labels past future (k+1) w hw).2.1
    simp only [List.length_map] at hl
    rw [← hl]; exact congrFun (run_causal B date mono policy w) l
  · intro j hj; exact mono j _ (Nat.le_of_lt (List.mem_range.mp (oldIndex.subset hj)))
  · intro w hw j l hl
    obtain ⟨left,h⟩ := world_full_partition labels past future (k+1) w hw
    have hd := h.nodup_iff.mpr distinct
    have ha : (assignment w).flatten.Nodup := (List.pairwise_append.mp hd).1
    simpa using expiry_at_cohort date (assignment w) ha j 0 l hl

#print axioms observation_from_policy
end HiddenStock

namespace HiddenStock

theorem tx_remainder (q : Nat) : q - tx q = q - 1 := by
  cases q <;> simp [tx]




theorem port_drain (B t n : Nat) (q : Nat → α → Nat) (last : α → Nat) (l : α)
    (admit : ∀ s a, q (s+1) a ≤ q s a - tx (q s a) + offered B (s+1) (last a))
    (expired : last l ≤ t) : q (t+n) l ≤ q t l - n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := admit (t+n) l
    simp only [offered, if_neg (by omega : ¬t+n+1≤last l), Nat.add_zero,tx_remainder] at h
    rw [show t+(n+1)=t+n+1 by omega]; omega

theorem expiry_upper [DecidableEq α] (date : Nat → Nat) (mono : ∀ i j, i≤j → date i≤date j)
    (a : List (List α)) (i : Nat) (l : α) : expiry date a i l ≤ date (i+a.length) := by
  induction a generalizing i with
  | nil => simp [expiry]
  | cons g a ih =>
    unfold expiry; split
    · apply mono; omega
    · rw [show i+(g::a).length=i+1+a.length by simp; omega]; exact ih (i+1)

theorem member_stock (labels : List α) (f : α → Nat) (l : α) (hl : l ∈ labels) :
    f l ≤ total labels f := by
  induction labels with
  | nil => simp at hl
  | cons x xs ih =>
    rcases List.mem_cons.mp hl with e|h
    · subst l; simp [total]
    · have h' := ih h; simp [total]; omega

theorem assignment_drained [DecidableEq α] (B : Nat) (labels : List α) (date : Nat → Nat)
    (mono : ∀ i j, i≤j → date i≤date j) (a : List (List α)) (q : Nat → α → Nat)
    (admit : ∀ s l, q (s+1) l ≤ q s l - tx (q s l) + offered B (s+1) (expiry date a 0 l))
    (cap : ∀ s, total labels (q s) ≤ B) (l : α) (hl : l∈labels) :
    q (date a.length+B) l = 0 := by
  have expire : expiry date a 0 l ≤ date a.length := by simpa using expiry_upper date mono a 0 l
  have h := port_drain B (date a.length) B q (expiry date a 0) l admit expire
  have h' := Nat.le_trans (member_stock labels (q (date a.length)) l hl) (cap (date a.length))
  omega

#print axioms assignment_drained
end HiddenStock
