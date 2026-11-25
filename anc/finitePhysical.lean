import finite
import stock

set_option exponentiation.threshold 5000




namespace BufferWitness.Physical

def lags : List Nat := [11,10,9,8,7,6,5,4,3,2,1]

def old (ks : List Nat) (i : Nat) : List Nat :=
  ks.filterMap (fun k => if k ≤ i then some (i-k) else none)

def padded (g : Nat → Nat) (j : Nat) : Nat := if 11 ≤ j then g (j-11) else 0

theorem pad_one (g : Nat → Nat) (D i k : Nat) (hk : k ≤ 11) :
    padded g (i+(11-k)) - lagCost k*D =
      if k ≤ i then g (i-k) - D*lagCost k else 0 := by
  by_cases h : k ≤ i
  · have h' : 11 ≤ i+(11-k) := by omega
    have h'' : i+(11-k)-11 = i-k := by omega
    simp only [padded, if_pos h, if_pos h', h'', Nat.mul_comm]
  · have h' : ¬ 11 ≤ i+(11-k) := by omega
    simp [padded, h, h']

theorem real_age (i k : Nat) (hi : i ≤ 1600) (hk : k ≤ i) :
    (eventTime i - eventTime (i-k)) * groupSize (i-k) = lagCost k := by
  have add : i-k+k=i := by omega
  have a := geometric_age (i-k) k (by omega)
  rw [add] at a
  rw [Nat.mul_comm, Nat.mul_sub]
  omega

theorem old_total (ks : List Nat) (g : Nat → Nat) (D i : Nat) (hi : i ≤ 1600) :
    HiddenStock.total (old ks i)
        (fun j => g j - D*((eventTime i - eventTime j)*groupSize j)) =
    HiddenStock.total ks (fun k => if k ≤ i then g (i-k)-D*lagCost k else 0) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    by_cases hk : k ≤ i
    · simp only [old, List.filterMap_cons, if_pos hk, HiddenStock.total] at *
      rw [ih, real_age i k hi hk]
    · simp only [old, List.filterMap_cons, if_neg hk, HiddenStock.total] at *
      simpa only [Nat.zero_add] using ih

theorem true_terms (g : Nat → Nat) (D i : Nat) (hi : i ≤ 1600) :
    residual (terms (padded g) D i) =
       HiddenStock.total (old lags i)
         (fun j => g j - D*((eventTime i - eventTime j)*groupSize j)) := by
  rw [old_total _ _ _ _ hi]
  have eq := HiddenStock.total_congr lags (fun k => padded g (i+(11-k))-lagCost k*D)
     (fun k => if k ≤ i then g (i-k)-D*lagCost k else 0)
     (fun k hk => pad_one g D i k (by simp [lags] at hk; omega))
  rw [← eq]
  simp [residual, terms, lags, HiddenStock.total]

theorem padded_prefix (g : Nat → Nat) {j : Nat} (hj : j ≤ 11) :
    total (padded g) j = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have h : ¬ 11 ≤ j := by omega
    simp [total, padded, ih (by omega), h]

theorem padded_initial (g : Nat → Nat) : potential (total (padded g)) 0 = 0 := by
  simp only [potential, eleven, Nat.zero_add]
  simp only [padded_prefix g (by decide : 11 ≤ 11), padded_prefix g (by decide : 10 ≤ 11),
    padded_prefix g (by decide : 9 ≤ 11), padded_prefix g (by decide : 8 ≤ 11),
    padded_prefix g (by decide : 7 ≤ 11), padded_prefix g (by decide : 6 ≤ 11),
    padded_prefix g (by decide : 5 ≤ 11), padded_prefix g (by decide : 4 ≤ 11),
    padded_prefix g (by decide : 3 ≤ 11), padded_prefix g (by decide : 2 ≤ 11),
    padded_prefix g (by decide : 1 ≤ 11), padded_prefix g (by decide : 0 ≤ 11),
    Nat.mul_zero, Nat.add_zero]

theorem padding_total (g : Nat → Nat) (n : Nat) :
    total (padded g) (n+11) = total g n := by
  induction n with
  | zero => exact padded_prefix g (by decide)
  | succ n ih =>
    change total (padded g) (n+11) + padded g (n+11) = total g n + g n
    simp [padded, ih]

theorem physical_row (labels : List α) (groups past future : List Nat)
    (gain : List (List α) → Nat → Nat) (i k : Nat) (hi : i < 1600)
    (split : past ++ (k+1)::future = groups)
    (active : labels.length-past.sum = 20*(k+1))
    (obs : HiddenStock.Observation labels past future k i B (old lags i) groupSize
             (fun j => eventTime i-eventTime j) gain) :
    let H := HiddenStock.histories labels groups
    let g := fun j => HiddenStock.total H (fun h => gain h.1 j)
    20 * padded g (i+11) + residual (terms (padded g) H.length i) ≤ B*H.length := by
  dsimp only
  have h := HiddenStock.canonical_inventory labels past future k i B 20 (old lags i)
    groupSize (fun j => eventTime i-eventTime j) gain active obs
  dsimp only at h
  rw [split] at h
  rw [true_terms _ _ i (by omega)]
  simpa only [padded, Nat.le_add_left, if_true, Nat.add_sub_cancel, Nat.mul_comm B] using h




theorem finite_from_observations (labels : List α) (groups : List Nat)
    (gain : List (List α) → Nat → Nat) (A O : Nat)
    (enough : groups.sum ≤ labels.length)
    (observed : ∀ i < 1600, ∃ past future k,
      past ++ (k+1)::future = groups ∧
      labels.length-past.sum = 20*(k+1) ∧
      Nonempty (HiddenStock.Observation labels past future k i B (old lags i) groupSize
             (fun j => eventTime i-eventTime j) gain))
    (online : let H := HiddenStock.histories labels groups
              A ≤ (prior+B)*H.length+
                   total (fun j => HiddenStock.total H (fun h => gain h.1 j)) 1600)
    (offline_feasible : offline*(HiddenStock.histories labels groups).length ≤ O) :
    3*A < 2*O := by
  let H := HiddenStock.histories labels groups
  let g := fun j => HiddenStock.total H (fun h => gain h.1 j)
  apply finite_from_inventory (padded g) H.length A O
      (HiddenStock.denominator_positive labels groups enough) (padded_initial _) _ _ offline_feasible
  · intro i hi
    obtain ⟨past, future, k, split, active, ⟨obs⟩⟩ := observed i hi
    exact physical_row labels groups past future gain i k hi split active obs
  · change A ≤ (prior+B)*H.length+total (padded g) (1600+11)
    rw [padding_total]
    exact online

#print axioms finite_from_observations
end BufferWitness.Physical

namespace BufferWitness.Physical


def schedule (j : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => groupSize j :: schedule (j+1) n

def population (i : Nat) := 20^(1600-i) * 19^i

theorem positive_size (i : Nat) : 0 < groupSize i :=
  Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))

theorem current_population (i : Nat) (hi : i<1600) : population i=20*groupSize i := by
  have ex : 1600-i=(1599-i)+1 := by omega
  simp only [population, groupSize, ex, Nat.pow_succ]
  ac_rfl

theorem next_population (i : Nat) : population (i+1)=19*groupSize i := by
  have ex : 1600-(i+1)=1599-i := by omega
  simp only [population, groupSize, ex, Nat.pow_succ]
  ac_rfl

theorem counts (i n : Nat) (hi : i+n≤1600) :
    population i = (schedule i n).sum + population (i+n) := by
  induction n generalizing i with
  | zero => simp [schedule]
  | succ n ih =>
    have prev := ih (i+1) (by omega)
    have now := current_population i (by omega)
    have next := next_population i
    have he : (i+1)+n=i+(n+1) := by omega
    rw [he] at prev
    simp only [schedule, List.sum_cons]
    omega

theorem schedule_append (i a b : Nat) :
    schedule i (a+b) = schedule i a ++ schedule (i+a) b := by
  induction a generalizing i with
  | zero => simp [schedule]
  | succ a ih =>
    have he : (i+1)+a=i+(a+1) := by omega
    rw [Nat.succ_add]
    simp only [schedule, List.cons_append, ih, he]

theorem concrete_split (i : Nat) (hi : i<1600) :
   schedule 0 i ++ ((groupSize i-1)+1)::schedule (i+1) (1599-i) = schedule 0 1600 := by
  have he : i+(1599-i+1)=1600 := by omega
  have hd : groupSize i-1+1=groupSize i := by have := positive_size i; omega
  rw [← he, schedule_append 0 i (1599-i+1)]
  simp only [Nat.zero_add, schedule, hd]

theorem starting_population : population 0 = K := by simp [population, K]




theorem concrete_finite (labels : List α) (hk : labels.length = K)
    (gain : List (List α) → Nat → Nat) (A O : Nat)
    (observed : ∀ i < 1600,
      Nonempty (HiddenStock.Observation labels (schedule 0 i) (schedule (i+1) (1599-i))
         (groupSize i-1) i B (old lags i) groupSize (fun j => eventTime i-eventTime j) gain))
    (online : let H := HiddenStock.histories labels (schedule 0 1600)
              A ≤ (prior+B)*H.length+
                   total (fun j => HiddenStock.total H (fun h => gain h.1 j)) 1600)
    (offline_feasible : offline*(HiddenStock.histories labels (schedule 0 1600)).length ≤ O) :
    3*A < 2*O := by
  have bound := counts 0 1600 (by decide)
  rw [starting_population] at bound
  apply finite_from_observations labels (schedule 0 1600) gain A O (by omega) _ online offline_feasible
  intro i hi
  refine ⟨schedule 0 i, schedule (i+1) (1599-i), groupSize i-1, concrete_split i hi, ?_, observed i hi⟩
  have h := counts 0 i (by omega)
  rw [starting_population, Nat.zero_add, current_population i hi] at h
  have hd : groupSize i-1+1=groupSize i := by have := positive_size i; omega
  rw [hk, hd]
  omega

#print axioms concrete_finite
end BufferWitness.Physical

namespace BufferWitness.Physical

theorem schedule_length (i n : Nat) : (schedule i n).length=n := by
  induction n generalizing i <;> simp_all [schedule]

theorem schedule_index (i n j : Nat) (hj : j<n) :
    (schedule i n)[j]? = some (groupSize (i+j)) := by
  induction n generalizing i j with
  | zero => omega
  | succ n ih =>
    cases j with
    | zero => simp [schedule]
    | succ j =>
      simp only [schedule, List.getElem?_cons_succ]
      have h := ih (i+1) j (by omega)
      rw [show i+1+j=i+(j+1) by omega] at h
      exact h

theorem old_sublist (i : Nat) : (old lags i).Sublist (List.range i) := by
  by_cases hi : i<11
  · have hl : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 := by omega
    rcases hl with h|h|h|h|h|h|h|h|h|h|h <;> subst i <;> decide
  · have suffix (s : Nat) : old lags (s+11) = List.range' s 11 := by
      simp (disch := omega) [old, lags, List.range'_succ, List.filterMap_cons, Nat.add_assoc]
      all_goals omega
    have h : ∀ s : Nat, (List.range' s 11).Sublist (List.range (s+11)) := by
      intro s
      rw [List.range_eq_range', ← List.range'_append_1 (s:=0) (m:=s) (n:=11), Nat.zero_add]
      exact List.sublist_append_right _ _
    have he : i=i-11+11 := by omega
    conv => lhs; rw [he, suffix]
    exact he ▸ h (i-11)

#print axioms old_sublist
end BufferWitness.Physical
