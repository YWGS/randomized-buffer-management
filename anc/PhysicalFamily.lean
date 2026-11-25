import Family


namespace SharedBuffer.Geometry
open Finset
open scoped BigOperators

structure Params where
  v : ℕ
  n : ℕ
  b : ℕ
  c : ℕ
  hv : 3 ≤ v
  hn : 0 < n
  hb : 0 < b
  hc : 0 < c

namespace Params
variable (P : Params)

def w := P.v-1
def K := P.v^P.n
def B := P.c*(P.v*P.w)^(P.n-1)
noncomputable def W : ℝ := P.b*P.w/(P.c:ℝ)
def d := Family.deaths P.v P.w P.n
def U := Family.active P.v P.w P.n
def gap := Family.gap P.v P.w P.b P.n
def date (i : ℕ) := ∑ j ∈ range i, P.gap j
def groups := (List.range P.n).map P.d
def S := (∑ j ∈ range P.n, P.d j*P.date j) + P.U P.n*P.date P.n
noncomputable def T (k : ℕ) : ℝ := P.W*(((P.v:ℝ)/(P.v-1))^k-1)

theorem w_pos : 0<P.w := by unfold w; have := P.hv; omega
theorem v_pos : 0<P.v := by have := P.hv; omega
theorem v_eq : P.v=P.w+1 := by unfold w; have := P.hv; omega
theorem w_real : (P.w:ℝ) = (P.v:ℝ)-1 := by
  unfold w; rw [Nat.cast_sub (by have := P.hv; omega),Nat.cast_one]

theorem d_pos (i : ℕ) : 0<P.d i :=
  Nat.mul_pos (Nat.pow_pos P.v_pos) (Nat.pow_pos P.w_pos)

theorem B_pos : 0<P.B := Nat.mul_pos P.hc (Nat.pow_pos (Nat.mul_pos P.v_pos P.w_pos))
theorem K_pos : 0<P.K := Nat.pow_pos P.v_pos
theorem W_pos : 0<P.W := by
  have hb := P.hb
  have hw := P.w_pos
  have hc := P.hc
  unfold W
  positivity

theorem pop {i : ℕ} (hi : i<P.n) : P.U i = P.v*P.d i :=
  (Family.populations hi P.v_eq).1

theorem pop_next {i : ℕ} (hi : i<P.n) : P.U (i+1) = P.w*P.d i :=
  (Family.populations hi P.v_eq).2.1

theorem pop_step {i : ℕ} (hi : i<P.n) : P.U i = P.d i + P.U (i+1) :=
  (Family.populations hi P.v_eq).2.2

theorem start_pop : P.U 0=P.K := by simp [U,Family.active,K]

theorem groupLength : P.groups.length=P.n := by simp [groups]

theorem groupIndex {i : ℕ} (hi : i<P.n) : P.groups[i]?=some (P.d i) := by
  simp [groups, List.getElem?_eq_getElem,hi]

theorem counts {i : ℕ} (hi : i≤P.n) :
    P.K=(P.groups.take i).sum + P.U i := by
  simp only [groups,← List.map_take,List.take_range,min_eq_left hi]
  induction i with
  | zero => simpa using P.start_pop.symm
  | succ i ih =>
    have h := ih (by omega)
    have pop' := P.pop_step (i:=i) (by omega)
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega

theorem groups_fit : P.groups.sum≤P.K := by
  have h := P.counts (i:=P.n) le_rfl
  rw [← P.groupLength, List.take_length] at h
  omega

theorem date_succ (i : ℕ) : P.date (i+1)=P.date i+P.gap i := Finset.sum_range_succ _ _
theorem date_zero : P.date 0=0 := by simp [date]
theorem date_strict : StrictMono P.date := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [P.date_succ]
  have g : 0<P.gap i :=
    Nat.mul_pos (Nat.mul_pos P.hb (Nat.pow_pos P.v_pos)) (Nat.pow_pos P.w_pos)
  omega
theorem date_mono : Monotone P.date := P.date_strict.monotone

theorem age {j i : ℕ} (hji : j ≤ i) (hi : i≤P.n) :
    ((P.d j * (P.date i-P.date j) : ℕ):ℝ)=P.B*P.T (i-j) := by
  have hjk : j+(i-j)=i := by omega
  have diff : P.date i-P.date j=∑ l ∈ range (i-j), P.gap (j+l) := by
    have e := sum_range_add P.gap j (i-j)
    rw [hjk] at e
    unfold date
    omega
  rw [diff,Nat.cast_mul,Nat.cast_sum]
  have ag := Family.age (b:=P.b) (n:=P.n) (j:=j) (k:=i-j)
    P.w_pos P.v_eq (by omega)
  calc
    _ = (((P.b*(P.v*P.w)^(P.n-1) : ℕ):ℝ)*(P.w:ℝ)) *
        (((P.v:ℝ)/P.w)^(i-j)-1) := ag
    _ = _ := by
      unfold B T W
      rw [← P.w_real]
      push_cast
      have hc : (P.c:ℝ)≠0 := by exact_mod_cast P.hc.ne'
      field_simp
      ring

theorem prior : P.S=(∑ j ∈ range P.n, P.d j*P.date j)+P.U P.n*P.date P.n := rfl

theorem prefix_budget {i : ℕ} (hi : i≤P.n) :
    (∑ j ∈ range i, P.d j * P.date j)+P.U i*P.date i =
      i*(P.w*(P.b*(P.v*P.w)^(P.n-1))) := by
  induction i with
  | zero => simp [date]
  | succ i ih =>
    have prev := ih (by omega)
    have now := P.pop_step (i:=i) (by omega)
    have next := P.pop_next (i:=i) (by omega)
    have cell : P.d i*P.gap i=P.b*(P.v*P.w)^(P.n-1) := Family.budget (by omega)
    rw [P.date_succ,Finset.sum_range_succ,Nat.mul_add,Nat.succ_mul]
    rw [now,Nat.add_mul] at prev
    have earn : P.U (i+1)*P.gap i=P.w*(P.b*(P.v*P.w)^(P.n-1)) := by
      rw [next, Nat.mul_assoc, cell]
    rw [earn]
    omega

theorem S_real : (P.S:ℝ) = (P.n:ℝ)*P.B*P.W := by
  have e := P.prefix_budget (i:=P.n) le_rfl
  change P.S = _ at e
  rw [e]
  unfold W B
  push_cast
  have hc : (P.c:ℝ)≠0 := by exact_mod_cast P.hc.ne'
  field_simp
  ring

theorem B_real : (P.B:ℝ) = (P.c:ℝ)*((P.v:ℝ)*(P.v-1))^(P.n-1) := by
  simp [B,P.w_real]
theorem K_real : (P.K:ℝ) = (P.v:ℝ)^P.n := by simp [K]

theorem fits {P : Params} (hc : P.v ≤ P.c) : P.K≤P.B := by
  have n := P.hn
  have ex : P.n=(P.n-1)+1 := by omega
  have e : P.v^P.n=P.v^(P.n-1)*P.v := by rw [← pow_succ,←ex]
  have w1 : 1≤P.w^(P.n-1) := Nat.one_le_pow _ _ P.w_pos
  unfold K B
  rw [e, mul_pow]
  calc
    _ ≤ P.v^(P.n-1)*P.c := Nat.mul_le_mul_left _ hc
    _ ≤ (P.v^(P.n-1)*P.c)*P.w^(P.n-1) := Nat.le_mul_of_pos_right _ w1
    _ = _ := by ring



theorem ofRationalChoice (v : ℕ) (hv : 3≤v) (W : ℚ) (hW : 0<W) :
    ∃ b c : ℕ, 0<b ∧ 0<c ∧ v≤c ∧
      (b:ℝ)*((v:ℝ)-1)/(c:ℝ) = (W:ℝ) := by
  let w := v-1
  have hw : 0<w := by dsimp [w]; omega
  have hv0 : 0<v := by omega
  have hd := W.den_pos
  have ha : 0<W.num := Rat.num_pos.mpr hW
  have haN : 0<W.num.toNat := by omega
  have he : (W.num.toNat : ℤ)=W.num := by omega
  have he' : (W.num.toNat : ℝ)=(W.num:ℝ) := by exact_mod_cast he
  have hw' : (w:ℝ)=(v:ℝ)-1 := by
    dsimp [w]
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  refine ⟨W.num.toNat*v,w*W.den*v,Nat.mul_pos haN hv0,
    Nat.mul_pos (Nat.mul_pos hw hd) hv0,?_,?_⟩
  · exact Nat.le_mul_of_pos_left v (Nat.mul_pos hw hd)
  · rw [Rat.cast_def,←hw']
    push_cast
    rw [he']
    have hw0 : (w:ℝ)≠0 := by exact_mod_cast hw.ne'
    have hv' : (v:ℝ)≠0 := by exact_mod_cast hv0.ne'
    have hd' : (W.den:ℝ)≠0 := by exact_mod_cast hd.ne'
    field_simp
    ring

#print axioms ofRationalChoice
#print axioms age
#print axioms S_real
end Params
end SharedBuffer.Geometry
