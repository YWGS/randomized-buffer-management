import finiteThroughput
import Offline
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Range


namespace SharedBuffer.OfflineRun
open HiddenStock SharedBuffer.Offline
open Finset
open scoped BigOperators

private theorem realizeMap [DecidableEq α] (ls : List α) (xs : List ℕ)
    (nd : ls.Nodup) (len : xs.length=ls.length) : ∃ f : α → ℕ, ls.map f = xs := by
  induction ls generalizing xs with
  | nil => simp at len; subst xs; exact ⟨fun _ => 0,rfl⟩
  | cons l ls ih =>
    cases xs with
    | nil => simp at len
    | cons x xs =>
      obtain ⟨notIn,nd'⟩ := List.nodup_cons.mp nd
      obtain ⟨f,hf⟩ := ih xs nd' (by simpa using len)
      refine ⟨fun a => if a=l then x else f a,?_⟩
      simp only [List.map_cons, if_true, List.cons.injEq, true_and,eq_self]
      rw [← hf]
      apply List.map_congr_left
      intro a ha
      simp [show a≠l by intro he; exact notIn (he ▸ ha)]

private theorem assign [DecidableEq α] (groups : List (List α)) (q : ℕ)
    (nd : groups.flatten.Nodup) (pos : ∀ g∈groups, 0<g.length) :
    ∃ f : α → ℕ, (∀ g∈groups, g.map f = balanced g.length q) ∧
      (∀ l, l∉groups.flatten → f l=0) := by
  induction groups with
  | nil => exact ⟨fun _ => 0, by simp, by simp⟩
  | cons g gs ih =>
    have nd' := List.pairwise_append.mp (show (g ++ gs.flatten).Nodup from nd)
    have dg := pos g (by simp)
    obtain ⟨f,hf⟩ := realizeMap g (balanced g.length q) nd'.1 (blockLength _ _ dg)
    obtain ⟨z,hz,z0⟩ := ih nd'.2.1 (by intro a ha; exact pos a (by simp [ha]))
    refine ⟨fun a => if a∈g then f a else z a,?_,?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl|ha
      · exact (List.map_congr_left (fun x hx => if_pos hx)).trans hf
      · refine (List.map_congr_left (fun x hx => if_neg ?_)).trans (hz a ha)
        exact fun hx' => nd'.2.2 x hx' x (List.mem_flatten.mpr ⟨a,ha,hx⟩) rfl
    · intro l hl
      simp only [List.flatten_cons,List.mem_append,not_or] at hl
      simp [hl.1,z0 l hl.2]

private theorem sumMap (ls : List α) (f : α → ℕ) : total ls f = (ls.map f).sum := by
  induction ls with
  | nil => rfl
  | cons x xs ih => simp [total,ih]

private theorem totalRange (f : ℕ → ℕ) (n : ℕ) : total (List.range n) f = ∑ j ∈ range n, f j := by
  induction n with
  | zero => simp [total]
  | succ n ih => simp [List.range_succ, total_append, total, ih, sum_range_succ]

theorem partitionSum (labels : List α) (a : List (List α)) (tail : List α)
    (n : ℕ) (hlen : a.length=n) (part : (a.flatten++tail).Perm labels) (f : α → ℕ) :
    total labels f = (∑ j ∈ range n, total (cohort a j) f) + total tail f := by
  rw [← total_perm _ _ f part,total_append,← total_flatten]
  have groups := BufferWitness.Physical.group_enumeration a
  rw [hlen] at groups
  conv => lhs; lhs; arg 1; rw [← groups]
  rw [total_map,totalRange]

private theorem slotsMap (f : ℕ → ℕ) (s n : ℕ) :
    slots f s n = (List.range' s n).map f := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [slots, List.range'_succ, ih]




theorem witness [DecidableEq α] (labels : List α) (a : List (List α)) (tail : List α)
    (n B q : ℕ) (d date : ℕ → ℕ) (distinct : labels.Nodup)
    (len : a.length=n) (part : (a.flatten++tail).Perm labels)
    (sizes : ∀ j<n, (cohort a j).length=d j) (pos : ∀ j<n, 0<d j)
    (mono : Monotone date) (hB : 0<B) (hq : q≤B)
    (fits : ∀ t, labels.length + (∑ j ∈ range n,
       if date j ≤ t then q - d j * (t-date j) else 0) ≤ B) :
    ∃ Q : ℕ → α → ℕ,
      (∀ t, total labels (Q t) ≤ B) ∧
      (∀ l∈labels, Q 0 l ≤ offered B 0 (expiry date a 0 l)) ∧
      (∀ t l, l∈labels → Q (t+1) l ≤ Q t l - tx (Q t l) + offered B (t+1) (expiry date a 0 l)) ∧
      (∀ l∈labels, Q (date n+B) l=0) ∧
      BufferWitness.Physical.serving Q labels 0 (date n+B) =
        (∑ j ∈ range n, d j * date j)+tail.length*date n+n*q := by
  have nd := List.pairwise_append.mp (part.nodup_iff.mpr distinct)
  have here (j : ℕ) (hj : j<n) : cohort a j ∈ a := by
    have hja : j<a.length := by omega
    simp [cohort,List.getElem?_eq_getElem hja]
  have pos' (g : List α) (hg : g∈a) : 0<g.length := by
    obtain ⟨j,hj,eq⟩ := List.getElem_of_mem hg
    have hj' : j<n := by omega
    subst g
    have z := sizes j hj'
    simp [cohort,List.getElem?_eq_getElem hj] at z
    rw [z]; exact pos j hj'
  obtain ⟨A,hA,hA0⟩ := assign a q nd.1 pos'
  let e := expiry date a 0
  let Q := fun t l => stock (e l) (A l) t
  have ed (j : ℕ) (l : α) (hl : l∈cohort a j) : e l=date j := by
    simpa [e] using expiry_at_cohort date a nd.1 j 0 l hl
  have away (l : α) (hl : l∈tail) : l∉a.flatten := fun h => nd.2.2 l h l hl rfl
  have et (l : α) (hl : l∈tail) : e l=date n := by
    simpa [e,len] using terminal_expiry date a 0 l (away l hl)
  have atail (l : α) (hl : l∈tail) : A l=0 := hA0 l (away l hl)
  have residual (j age : ℕ) (hj : j<n) :
      total (cohort a j) (fun l => A l - age) = q - d j * age := by
    rw [sumMap]
    change (List.map ((fun x => x-age) ∘ A) _).sum = _
    rw [← List.map_map]
    rw [hA _ (here j hj),sizes j hj,blockResidual _ _ _ (pos j hj)]
  have budgets (j : ℕ) (hj : j<n) : total (cohort a j) A=q := by
    simpa using residual j 0 hj
  have tsum : total tail A=0 := by
    simpa [total_const] using total_congr tail A (fun _ => 0) atail
  have per (l : α) (hl : l∈labels) : A l ≤ B := by
    rcases List.mem_append.mp (part.mem_iff.mpr hl) with hg|ht
    · obtain ⟨g,hg,hl'⟩ := List.mem_flatten.mp hg
      obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
      have hmem : l∈cohort a j := by simpa [cohort,List.getElem?_eq_getElem hj] using hl'
      exact (member_stock _ A _ hmem).trans ((budgets j (by omega)) ▸ hq)
    · rw [atail l ht]; exact Nat.zero_le _
  have ht : ∀ t, total labels (Q t) ≤ B := by
    intro t
    have side (j : ℕ) (hj : j<n) : total (cohort a j) (Q t) ≤
        d j + (if date j≤t then q-d j*(t-date j) else 0) := by
      by_cases past : date j ≤ t
      · rw [if_pos past]
        have eq := total_congr (cohort a j) (Q t) (fun l => A l-(t-date j))
           (fun l hl => by simp [Q, stock, ed j l hl, Nat.not_lt.mpr past])
        rw [eq, residual j _ hj]; omega
      · rw [if_neg past]
        have eq := total_congr (cohort a j) (Q t) (fun _ => 1)
           (fun l hl => by simp [Q, stock, ed j l hl, Nat.lt_of_not_ge past])
        simp [eq,total_const,sizes j hj]
    have stail : total tail (Q t) ≤ tail.length := by
      have h := total_le tail (Q t) (fun _ => 1) (by
        intro l hl; simp [Q, stock, atail l hl]; split <;> omega)
      simpa [total_const] using h
    have count := partitionSum labels a tail n len part (fun _ => 1)
    simp only [total_const,Nat.mul_one] at count
    have ds : (∑ j ∈ range n, (cohort a j).length) = ∑ j ∈ range n, d j :=
      sum_congr rfl (fun j hj => sizes j (mem_range.mp hj))
    rw [ds] at count
    have s := sum_le_sum (s:=range n) (fun j hj => side j (mem_range.mp hj))
    rw [sum_add_distrib] at s
    rw [partitionSum _ _ _ _ len part]
    have := fits t
    omega
  have expBound (l : α) : e l ≤ date n := by
    simpa [e,len] using expiry_upper date (fun _ _ h => mono h) a 0 l
  have endBound (l : α) (hl : l∈labels) : e l+A l ≤ date n+B :=
    Nat.add_le_add (expBound l) (per l hl)
  refine ⟨Q,ht,?_,?_,?_,?_⟩
  · intro l hl
    simpa [Q,e,offered] using refill B (e l) (A l) 0 hB (per l hl)
  · intro t l hl
    simpa [Q,e,offered,tx_remainder] using refill B (e l) (A l) (t+1) hB (per l hl)
  · intro l hl; have he:=expBound l; have h:=endBound l hl
    simp [Q, stock, show ¬ date n+B < e l by omega]; omega
  · rw [BufferWitness.Physical.by_label]
    have byPort (l : α) (hl : l∈labels) :
        (slots (fun t => tx (Q t l)) 0 (date n+B)).sum = e l + A l := by
      have same (t : ℕ) : tx (Q t l)=sent (stock (e l) (A l) t) := by
        unfold tx sent; change (if Q t l=0 then 0 else 1)=min 1 (Q t l)
        split <;> omega
      simp only [slotsMap, ← List.range_eq_range', same]
      exact payoff _ _ _ (endBound l hl)
    rw [total_congr _ _ _ byPort,total_add,partitionSum labels a tail n len part e]
    have ep (j : ℕ) (hj : j<n) : total (cohort a j) e=d j*date j := by
      rw [total_congr _ _ _ (ed j),total_const,sizes j hj]
    rw [sum_congr rfl (fun j hj => ep j (mem_range.mp hj)),
      total_congr _ _ _ et,total_const,partitionSum labels a tail n len part A,tsum,
      sum_congr rfl (fun j hj => budgets j (mem_range.mp hj))]
    simp
#print axioms witness
end SharedBuffer.OfflineRun
