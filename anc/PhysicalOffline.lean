import OfflineRun
import PhysicalFamily
import limit_bridge
import Mathlib.Data.Nat.Find



namespace SharedBuffer.PhysicalOffline
open HiddenStock Geometry Finset
open scoped BigOperators
noncomputable section

def quota (P : Params) (x : ℝ) : ℕ := ⌊((P.B:ℝ)-P.K)*x⌋₊

theorem quota_real (P : Params) (x : ℝ) (hKB : P.K≤P.B) (hx : 0≤x) :
    (quota P x:ℝ)=(⌊((P.B:ℝ)-P.K)*x⌋ : ℤ) :=
  natCast_floor_eq_intCast_floor (mul_nonneg
    (sub_nonneg.mpr (by exact_mod_cast hKB)) hx)

private theorem castResidual (q a : ℕ) : ((q-a:ℕ):ℝ)=max ((q:ℝ)-a) 0 := by
  by_cases h : a≤q
  · rw [Nat.cast_sub h,max_eq_left (sub_nonneg.mpr (by exact_mod_cast h))]
  · have hr : (q:ℝ)≤a := by exact_mod_cast Nat.le_of_not_ge h
    simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge h),max_eq_right (sub_nonpos.mpr hr)]

private theorem stationary (P : Params) (x : ℝ) (hx : 0≤x)
    (level : BufferLimit.Level 1 ((P.v:ℝ)/(P.v-1)) P.W x) (i : ℕ) :
    ∑ k ∈ range (i+1), max (x-P.T k) 0 ≤ 1 := by
  have identity (m : ℕ) : ∑ k ∈ range (m+1), max (x-P.T k) 0 =
      x+BufferLimit.stock ((P.v:ℝ)/(P.v-1)) P.W x m := by
    induction m with
    | zero => simp [Geometry.Params.T,BufferLimit.stock,max_eq_left hx]
    | succ m ih =>
      rw [sum_range_succ,ih]
      simp [BufferLimit.stock,Geometry.Params.T,add_assoc]
  simpa [identity] using (show x+BufferLimit.stock ((P.v:ℝ)/(P.v-1)) P.W x i ≤ 1 by
    simpa using level.1 i)

private theorem capacity (P : Params) (x : ℝ) (hKB : P.K≤P.B) (hx : 0≤x)
    (level : BufferLimit.Level 1 ((P.v:ℝ)/(P.v-1)) P.W x) (t : ℕ) :
    P.K + (∑ j ∈ range P.n, if P.date j≤t then quota P x - P.d j*(t-P.date j) else 0) ≤ P.B := by
  let i := Nat.findGreatest (fun j => P.date j≤t) P.n
  have hi : i≤P.n := Nat.findGreatest_le _
  have hit : P.date i≤t := Nat.findGreatest_spec (P:=fun j => P.date j≤t) (m:=0) (Nat.zero_le _) (by simp [P.date_zero])
  let sel := (range P.n).filter (fun j => P.date j≤t)
  have sub : sel ⊆ range (i+1) := by
    intro j hj
    obtain ⟨hn,ht⟩ := mem_filter.mp hj
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_findGreatest (mem_range.mp hn).le ht))
  let q := quota P x
  have hreal (j : ℕ) (hj : j∈sel) :
      ((q-P.d j*(t-P.date j):ℕ):ℝ) ≤ max ((q:ℝ)-P.B*P.T (i-j)) 0 := by
    have hji : j ≤ i := Nat.le_of_lt_succ (mem_range.mp (sub hj))
    rw [castResidual,← P.age hji hi]
    apply max_le_max_right
    exact sub_le_sub_left (Nat.cast_le.mpr (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hit _))) _
  let F := fun k => max ((q:ℝ)-P.B*P.T k) 0
  have s : ∑ j ∈ sel, ((q-P.d j*(t-P.date j):ℕ):ℝ) ≤ ∑ k ∈ range (i+1), F k := calc
    _ ≤ ∑ j ∈ sel, F (i-j) := sum_le_sum (fun j hj => hreal j hj)
    _ ≤ ∑ j ∈ range (i+1), F (i-j) :=
       sum_le_sum_of_subset_of_nonneg sub (fun j _ _ => le_max_right _ _)
    _ = _ := by simpa using (sum_range_reflect F (i+1))
  have hkb : (P.K:ℝ)≤P.B := by exact_mod_cast hKB
  have qle : (q:ℝ) ≤ ((P.B:ℝ)-P.K)*x :=
    Nat.floor_le (mul_nonneg (sub_nonneg.mpr hkb) hx)
  have ratio : 1≤(P.v:ℝ)/(P.v-1) := by
    have v3 : (3:ℝ)≤P.v := by exact_mod_cast P.hv
    apply (le_div_iff₀ (by linarith)).mpr; linarith
  have hnT (k : ℕ) : 0≤P.T k :=
    mul_nonneg P.W_pos.le (sub_nonneg.mpr (one_le_pow₀ ratio))
  have bound := Family.offlineCapacity (i+1) (Nat.cast_nonneg P.K) hkb qle hnT (stationary P x hx level i)
  change (P.K:ℝ)+ (∑ k ∈ range (i+1), F k) ≤ P.B at bound
  rw [← sum_filter]
  change P.K+(∑ j ∈ sel, (q-P.d j*(t-P.date j))) ≤ P.B
  exact_mod_cast (show (P.K:ℝ) + ((∑ j ∈ sel, (q-P.d j*(t-P.date j)) : ℕ):ℝ) ≤ P.B by
    rw [Nat.cast_sum]
    linarith)

theorem witness [DecidableEq α] (P : Params) (x : ℝ) (hKB : P.K≤P.B) (hx : 0<x)
    (level : BufferLimit.Level 1 ((P.v:ℝ)/(P.v-1)) P.W x)
    (labels : List α) (len : labels.length=P.K) (distinct : labels.Nodup)
    (h : List (List α) × List α) (hm : h∈histories labels P.groups) :
    ∃ Q : ℕ → α → ℕ,
      (∀ t, total labels (Q t) ≤ P.B) ∧
      (∀ l∈labels, Q 0 l ≤ offered P.B 0 (expiry P.date h.1 0 l)) ∧
      (∀ t l, l∈labels → Q (t+1) l ≤ Q t l-tx (Q t l)+offered P.B (t+1) (expiry P.date h.1 0 l)) ∧
      (∀ l∈labels, Q (P.date P.n+P.B) l=0) ∧
      BufferWitness.Physical.serving Q labels 0 (P.date P.n+P.B) = P.S + P.n*quota P x := by
  have shape := history_shape _ _ _ hm
  have hn : h.1.length=P.n := by simpa [P.groupLength] using congrArg List.length shape
  have size (j : ℕ) (hj : j<P.n) : (cohort h.1 j).length=P.d j := by
    have hh : j<h.1.length := by omega
    have eq := congrArg (fun g : List ℕ => g[j]?) shape
    simpa [cohort, List.getElem?_eq_getElem hh, List.getElem?_map, P.groupIndex hj] using eq
  have rest := history_rest _ _ _ hm
  have count := P.counts (i:=P.n) le_rfl
  rw [show P.groups.take P.n=P.groups by rw [← P.groupLength,List.take_length]] at count
  have tailLen : h.2.length=P.U P.n := by omega
  have x1 : x≤1 := by simpa [BufferLimit.stock] using level.1 0
  have realKB : (P.K:ℝ)≤P.B := by exact_mod_cast hKB
  have qR : (quota P x:ℝ)≤((P.B:ℝ)-P.K)*x :=
    Nat.floor_le (mul_nonneg (sub_nonneg.mpr realKB) hx.le)
  have qB : quota P x ≤ P.B := by
    have small := mul_le_mul_of_nonneg_left x1 (sub_nonneg.mpr realKB)
    exact_mod_cast (show (quota P x:ℝ)≤P.B by
      have k0 : 0≤(P.K:ℝ) := Nat.cast_nonneg _
      linarith)
  obtain ⟨Q,g⟩ := OfflineRun.witness labels h.1 h.2 P.n P.B (quota P x) P.d P.date
    distinct hn (history_partition _ _ _ hm) size (fun j _ => P.d_pos j)
    P.date_mono P.B_pos qB (fun t => len ▸ capacity P x hKB hx.le level t)
  exact ⟨Q,g.1,g.2.1,g.2.2.1,g.2.2.2.1,by simpa [P.prior,tailLen] using g.2.2.2.2⟩

#print axioms quota_real
#print axioms witness
end
end SharedBuffer.PhysicalOffline
