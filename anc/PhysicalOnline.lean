import finiteThroughput
import finiteGeneral
import PhysicalFamily
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin




namespace SharedBuffer.PhysicalOnline
open HiddenStock Finset
open BufferWitness.Physical (serving by_label before_service group_enumeration)
open scoped BigOperators

abbrev Leaf (α : Type*) := List (List α) × List α

def horizon (groups : List ℕ) (B : ℕ) (date : ℕ → ℕ) := date groups.length + B

def gainSum [DecidableEq α] (labels : List α) (groups : List ℕ) (B : ℕ)
    (date : ℕ → ℕ) (p : Policy α) (j : ℕ) : ℕ :=
  total (histories labels groups)
    (fun h => gainFromRun (run B date p) date (horizon groups B date) h.1 j)

noncomputable def inventory [DecidableEq α] (labels : List α) (groups : List ℕ) (B : ℕ)
    (date : ℕ → ℕ) (p : Policy α) (j : ℕ) : ℝ :=
  (gainSum labels groups B date p j : ℝ) / ((histories labels groups).length * (B:ℝ))

noncomputable def payoff [DecidableEq α] (labels : List α) (groups : List ℕ) (B : ℕ)
    (date : ℕ → ℕ) (p : Policy α) (h : Leaf α) : ℝ :=
  (serving (run B date p h.1) labels 0 (horizon groups B date) : ℕ)

abbrev Admissible [DecidableEq α] (B : ℕ) (date : ℕ → ℕ) (p : Policy α) :=
  ∀ (a : List (List α)) (s : ℕ) (l : α), run B date p a (s+1) l ≤
    run B date p a s l - tx (run B date p a s l) + offered B (s+1) (expiry date a 0 l)

abbrev Capacity [DecidableEq α] (labels : List α) (B : ℕ) (date : ℕ → ℕ) (p : Policy α) :=
  ∀ (a : List (List α)) (s : ℕ), total labels (run B date p a s) ≤ B

theorem total_range (f : ℕ → ℕ) (n : ℕ) :
    total (List.range n) f = ∑ j ∈ range n, f j := by
  induction n with
  | zero => simp [total]
  | succ n ih => simp [List.range_succ, total_append, total, sum_range_succ, ih]

private theorem cast_diff (x y : ℕ) : ((x-y : ℕ) : ℝ) = max 0 ((x:ℝ)-y) := by
  by_cases hy : y ≤ x
  · rw [Nat.cast_sub hy, max_eq_right]; exact_mod_cast (sub_nonneg.mpr (show (y:ℝ) ≤ x by exact_mod_cast hy))
  · rw [Nat.sub_eq_zero_of_le (by omega), Nat.cast_zero, max_eq_left]
    exact sub_nonpos.mpr (by exact_mod_cast (show x ≤ y by omega))



theorem rawRow [DecidableEq α] (labels : List α) (distinct : labels.Nodup)
    (groups : List ℕ) (B v : ℕ) (date size : ℕ → ℕ) (p : Policy α)
    (mono : Monotone date) (admit : Admissible B date p) (cap : Capacity labels B date p)
    (sizes : ∀ i, i<groups.length → groups[i]? = some (size i))
    (i : ℕ) (hi : i<groups.length) (hs : 0 < size i)
    (active : labels.length - (groups.take i).sum = v * size i) :
    let D := (histories labels groups).length
    let g := gainSum labels groups B date p
    v*g i + (∑ j ∈ range i, (g j - D*((date i-date j)*size j))) ≤ D*B := by
  let past := groups.take i
  let future := groups.drop (i+1)
  have plen : past.length = i := List.length_take_of_le hi.le
  have hd : size i-1+1=size i := by omega
  have gidx : groups[i] = size i := by
    have si := sizes i hi
    rw [List.getElem?_eq_getElem hi] at si
    exact Option.some.inj si
  have split : past ++ ((size i-1)+1)::future = groups := by
    rw [hd, ← gidx]
    simp [past, future, ← List.drop_eq_getElem_cons hi]
  have obs := observation_from_policy labels distinct past future (size i-1) B (horizon groups B date)
    (List.range i) size date (fun _ _ e => mono e) p admit cap
    (by rw [plen])
    (by intro j hj; have hj' := List.mem_range.mp hj
        simp [past, List.getElem?_take, hj', sizes j (by omega)])
    (by rw [plen]; exact (mono hi.le).trans (Nat.le_add_right _ _))
  rw [plen] at obs
  have raw := canonical_inventory labels past future (size i-1) i B v (List.range i) size
    (fun j => date i-date j) _ (by rw [hd]; exact active) obs
  dsimp only at raw
  rw [split, total_range] at raw
  exact raw

theorem rows [DecidableEq α] (labels : List α) (distinct : labels.Nodup)
    (groups : List ℕ) (B v : ℕ) (date size : ℕ → ℕ) (T : ℕ → ℝ) (p : Policy α)
    (mono : Monotone date) (admit : Admissible B date p) (cap : Capacity labels B date p)
    (sizes : ∀ i, i<groups.length → groups[i]? = some (size i))
    (enough : groups.sum ≤ labels.length) (hB : 0<B)
    (i : ℕ) (hi : i<groups.length) (hs : 0<size i)
    (active : labels.length-(groups.take i).sum=v*size i)
    (age : ∀ j, j < i → ((size j*(date i-date j) : ℕ):ℝ) = B*T (i-j)) :
    let X := inventory labels groups B date p
    v*X i + (∑ j ∈ range i, Averaging.residual X T i (j+1)) ≤ 1 := by
  let D := (histories labels groups).length
  let g := gainSum labels groups B date p
  let den : ℝ := (D:ℝ)*B
  let X := inventory labels groups B date p
  have dpos : 0<D := denominator_positive labels groups enough
  have pos : 0<den := mul_pos (Nat.cast_pos.mpr dpos) (Nat.cast_pos.mpr hB)
  let cost := fun j => D*((date i-date j)*size j)
  let f := fun j => ((g j - cost j : ℕ):ℝ) / den
  have term (j : ℕ) (hj : j < i) :
      Averaging.residual X T i (j+1) = f (i-1-j) := by
    let k := i-1-j
    have hk : k < i := by dsimp [k]; omega
    have idx : i-(j+1)=k := by dsimp [k]; omega
    have lag : i-k=j+1 := by dsimp [k]; omega
    have ag := age k hk
    rw [lag, Nat.cast_mul, mul_comm (size k : ℝ)] at ag
    have ce : (cost k : ℝ) = den*T (j+1) := by
      dsimp only [cost, den]; push_cast; rw [mul_assoc, ← ag]
    change Averaging.residual X T i (j+1) = ((g k-cost k : ℕ):ℝ)/den
    rw [Averaging.residual, if_pos (by omega), idx, cast_diff, ce]
    change max 0 ((g k : ℝ)/den-T (j+1)) = max 0 ((g k:ℝ)-den*T (j+1))/den
    rw [← max_div_div_right pos.le, zero_div, sub_div]
    field_simp
  change (v:ℝ)*X i + _ ≤ 1
  calc
    _ = (v:ℝ)*X i + ∑ j ∈ range i, f j := by
      rw [← sum_range_reflect f i]
      exact congrArg ((v:ℝ)*X i + ·) (sum_congr rfl (fun j hj => term j (mem_range.mp hj)))
    _ = ((v*g i + ∑ j ∈ range i, (g j-cost j) : ℕ):ℝ)/den := by
      change (v:ℝ)*((g i:ℝ)/den) + (∑ j ∈ range i, ((g j-cost j:ℕ):ℝ)/den) = _
      push_cast
      simp only [div_eq_mul_inv, ← sum_mul, add_mul]
      ring
    _ ≤ 1 := by
      apply (div_le_one pos).mpr
      have bound : v*g i + (∑ j ∈ range i, (g j-cost j)) ≤ D*B :=
        rawRow labels distinct groups B v date size p mono admit cap sizes i hi hs active
      change _ ≤ (D:ℝ)*B
      rw [← Nat.cast_mul]
      exact_mod_cast bound



theorem traceSplit [DecidableEq α] (labels : List α) (distinct : labels.Nodup)
    (groups : List ℕ) (B : ℕ) (date size : ℕ → ℕ) (p : Policy α)
    (mono : Monotone date) (admit : Admissible B date p) (cap : Capacity labels B date p)
    (sizes : ∀ i, i<groups.length → groups[i]? = some (size i))
    (h : Leaf α) (hh : h∈histories labels groups) :
    let f := horizon groups B date
    let G := gainFromRun (run B date p) date f h.1
    serving (run B date p h.1) labels 0 f ≤
      (∑ i ∈ range groups.length, size i*date i) +
      (labels.length-groups.sum)*date groups.length + B + ∑ i ∈ range groups.length, G i := by
  let f := horizon groups B date
  let Q := run B date p h.1
  let L := fun l => (slots (fun t => tx (Q t l)) 0 f).sum
  let G := gainFromRun (run B date p) date f h.1
  have shape := history_shape labels groups h hh
  have len := congrArg List.length shape
  simp only [List.length_map] at len
  have part := history_partition labels groups h hh
  have hsize (j : ℕ) (hj : j<groups.length) : (cohort h.1 j).length = size j := by
    have atj := congrArg (fun l : List ℕ => l[j]?) shape
    simpa [cohort, List.getElem?_eq_getElem (show j < h.1.length by omega),
      List.getElem?_map, sizes j hj] using atj
  have restLen := history_rest labels groups h hh
  have terminal (l : α) (hl : l ∈ h.2) : expiry date h.1 0 l ≤ date groups.length := by
    have dis := (List.pairwise_append.mp (part.nodup_iff.mpr distinct)).2.2
    have away : l ∉ h.1.flatten := fun hl' => dis l hl' l hl rfl
    rw [terminal_expiry _ _ _ _ away, Nat.zero_add, len]
  have hfinal : date groups.length ≤ f := Nat.le_add_right _ _
  have termGain := no_future_arrivals (closed_from_switch B (date groups.length) (f-date groups.length)
      h.2 Q (expiry date h.1 0) (admit h.1) terminal)
  have termStock := total_perm (h.1.flatten++h.2) labels (Q (date groups.length)) part
  rw [total_append] at termStock
  have capTerm : total labels (Q (date groups.length)) ≤ B := cap h.1 _
  have boundTerm := before_service Q h.2 f (date groups.length) hfinal
  change serving Q h.2 (date groups.length) (f-date groups.length) + _ ≤ _ at termGain
  have count : h.2.length = labels.length-groups.sum := by omega
  rw [count] at boundTerm
  have terminalBound : serving Q h.2 0 f ≤ (labels.length-groups.sum)*date groups.length+B := by omega
  have mains := total_le (List.range groups.length) (fun j => serving Q (cohort h.1 j) 0 f)
    (fun j => size j*date j+G j) (by
      intro j hj
      have js := List.mem_range.mp hj
      have bd := before_service Q (cohort h.1 j) f (date j) ((mono js.le).trans hfinal)
      rw [hsize j js] at bd
      exact bd)
  rw [total_add] at mains
  simp only [total_range] at mains
  have allParts := total_perm (h.1.flatten++h.2) labels L part
  rw [total_append, ← total_flatten] at allParts
  have enum := group_enumeration h.1
  rw [len] at enum
  conv at allParts => lhs; lhs; arg 1; rw [← enum]
  rw [total_map] at allParts
  have into : total (List.range groups.length) (fun j => total (cohort h.1 j) L)
      = total (List.range groups.length) (fun j => serving Q (cohort h.1 j) 0 f) := by
    apply total_congr; intro j _; exact (by_label ..).symm
  rw [into, ← by_label Q h.2 0 f, ← by_label Q labels 0 f, total_range] at allParts
  change serving Q labels 0 f ≤ _ + _ + B + ∑ i ∈ range groups.length, G i
  omega

theorem finTotal (xs : List α) (g : α → ℕ) :
    (∑ t : Fin xs.length, g (xs.get t)) = total xs g := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih =>
    change (∑ t : Fin (xs.length+1), g ((x::xs).get t)) = _
    rw [Fin.sum_univ_succ]
    simpa [total] using congrArg (g x + ·) ih

theorem split [DecidableEq α] (labels : List α) (distinct : labels.Nodup)
    (groups : List ℕ) (B : ℕ) (date size : ℕ → ℕ) (p : Policy α)
    (mono : Monotone date) (admit : Admissible B date p) (cap : Capacity labels B date p)
    (sizes : ∀ i, i<groups.length → groups[i]? = some (size i))
    (enough : groups.sum ≤ labels.length) (hB : 0<B) :
    let H := histories labels groups
    let pref := (∑ i ∈ range groups.length, size i*date i) +
      (labels.length-groups.sum)*date groups.length
    (∑ t : Fin H.length, payoff labels groups B date p (H.get t)) / H.length ≤
      pref+(B:ℝ)*((∑ i ∈ range groups.length, inventory labels groups B date p i)+1) := by
  let H := histories labels groups
  let f := horizon groups B date
  let G := gainFromRun (run B date p) date f
  let score := fun h : Leaf α => serving (run B date p h.1) labels 0 f
  let pref := (∑ i ∈ range groups.length, size i*date i) +
    (labels.length-groups.sum)*date groups.length
  let g := gainSum labels groups B date p
  have raw := total_le H score (fun h => (pref+B)+total (List.range groups.length) (G h.1))
    (by intro h hh
        change score h ≤ (pref+B)+total (List.range groups.length) (G h.1)
        rw [total_range]
        exact traceSplit labels distinct groups B date size p mono admit cap sizes h hh)
  rw [total_add, total_const, total_swap, total_range] at raw
  change total H score ≤ H.length*(pref+B) + ∑ i ∈ range groups.length, g i at raw
  rw [← finTotal] at raw
  have natD : 0<H.length := denominator_positive labels groups enough
  have Dpos : (0:ℝ)<H.length := Nat.cast_pos.mpr natD
  have Bpos : (0:ℝ)<B := Nat.cast_pos.mpr hB
  have rawReal : (∑ t : Fin H.length, (score (H.get t):ℝ)) ≤
      (H.length:ℝ)*(pref+B) + ∑ i ∈ range groups.length, (g i:ℝ) := by exact_mod_cast raw
  change (∑ t : Fin H.length, (score (H.get t):ℝ)) / H.length ≤
    (pref:ℝ)+B*((∑ i ∈ range groups.length, (g i:ℝ)/(H.length*(B:ℝ)))+1)
  apply (div_le_iff₀ Dpos).mpr
  refine rawReal.trans_eq ?_
  simp only [div_eq_mul_inv, ← sum_mul]
  field_simp
  ring



theorem rowsGeometry [DecidableEq α] (P : Geometry.Params)
    (labels : List α) (distinct : labels.Nodup) (hk : labels.length=P.K)
    (p : Policy α) (admit : Admissible P.B P.date p) (cap : Capacity labels P.B P.date p)
    (i : ℕ) (hi : i<P.n) :
    let X := inventory labels P.groups P.B P.date p
    (P.v:ℝ)*X i + (∑ j ∈ range i, Averaging.residual X P.T i (j+1)) ≤ 1 := by
  apply rows labels distinct P.groups P.B P.v P.date P.d P.T p P.date_mono admit cap
    (fun j hj => P.groupIndex (P.groupLength ▸ hj)) (hk ▸ P.groups_fit) P.B_pos
    i (P.groupLength.symm ▸ hi) (P.d_pos i)
  · rw [hk, ← P.pop hi]
    have e := P.counts hi.le
    omega
  · exact fun j hj => P.age hj.le hi.le



theorem splitGeometry [DecidableEq α] (P : Geometry.Params)
    (labels : List α) (distinct : labels.Nodup) (hk : labels.length=P.K)
    (p : Policy α) (admit : Admissible P.B P.date p) (cap : Capacity labels P.B P.date p) :
    let H := histories labels P.groups
    (∑ t : Fin H.length, payoff labels P.groups P.B P.date p (H.get t)) / H.length ≤
      (P.n:ℝ)*P.B*P.W+(P.B:ℝ)*((∑ i ∈ range P.n, inventory labels P.groups P.B P.date p i)+1) := by
  have bound := split labels distinct P.groups P.B P.date P.d p P.date_mono admit cap
    (fun j hj => P.groupIndex (P.groupLength ▸ hj)) (hk ▸ P.groups_fit) P.B_pos
  dsimp only at bound ⊢
  rw [P.groupLength] at bound
  have count := P.counts (i:=P.n) le_rfl
  have takeAll : P.groups.take P.n = P.groups := by rw [← P.groupLength, List.take_length]
  rw [takeAll] at count
  have rem : labels.length - P.groups.sum = P.U P.n := by omega
  rw [rem, ← P.prior, P.S_real] at bound
  exact bound

#print axioms rowsGeometry
#print axioms splitGeometry
end SharedBuffer.PhysicalOnline
