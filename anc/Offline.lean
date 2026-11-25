import Std





namespace SharedBuffer.Offline

private theorem appendSum (xs ys : List Nat) : (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc]

def stock (e a t : Nat) : Nat := if t < e then 1 else a - (t - e)
def sent (s : Nat) : Nat := min 1 s

theorem refill (B e a t : Nat) (hB : 0 < B) (ha : a ≤ B) :
    stock e a t ≤ (if t = 0 then 0 else stock e a (t-1) - 1) +
                    (if t ≤ e then B else 0) := by
  unfold stock
  split <;> split <;> split <;> (try split) <;> omega

theorem payoff (e a N : Nat) (h : e + a ≤ N) :
    ((List.range N).map (fun t => sent (stock e a t))).sum = e + a := by
  have initialSum (n : Nat) :
      ((List.range n).map (fun t => sent (stock e a t))).sum = min n (e+a) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.map_append, appendSum, ih]
      simp [sent, stock]
      split <;> omega
  rw [initialSum]
  omega


def balanced (d q : Nat) : List Nat :=
  List.replicate (q % d) (q / d + 1) ++ List.replicate (d - q % d) (q / d)

theorem blockLength (d q : Nat) (hd : 0 < d) : (balanced d q).length = d := by
  have := Nat.mod_lt q hd
  simp [balanced]
  omega

theorem blockResidual (d q age : Nat) (hd : 0 < d) :
    ((balanced d q).map (fun a => a - age)).sum = q - d * age := by
  let a := q / d
  let e := q % d
  have he : e ≤ d := Nat.le_of_lt (Nat.mod_lt q hd)
  have hq : e + d * a = q := Nat.mod_add_div q d
  simp only [balanced, List.map_append, List.map_replicate, appendSum,
    List.sum_replicate_nat]
  change e * (a + 1 - age) + (d - e) * (a - age) = q - d * age
  by_cases h : age ≤ a
  · have hs : a + 1 - age = (a - age) + 1 := by omega
    rw [hs, Nat.mul_add, Nat.mul_one, Nat.add_right_comm, ← Nat.add_mul,
        Nat.add_sub_of_le he, Nat.mul_sub]
    have hda := Nat.mul_le_mul_left d h
    omega
  · have hzero : a + 1 - age = 0 := by omega
    have hzero' : a - age = 0 := by omega
    have hm := Nat.mul_le_mul_left d (show a+1 ≤ age by omega)
    rw [Nat.mul_add, Nat.mul_one] at hm
    rw [hzero, hzero']
    simp
    omega

abbrev Output := Nat × Nat
def occupancy (outputs : List Output) (t : Nat) : Nat :=
  (outputs.map (fun o => stock o.1 o.2 t)).sum



theorem fromEvents (B : Nat) (outputs : List Output)
    (initial : occupancy outputs 0 ≤ B)
    (event : ∀ o ∈ outputs, occupancy outputs o.1 ≤ B) :
    ∀ t, occupancy outputs t ≤ B := by
  intro t
  induction t with
  | zero => exact initial
  | succ t ih =>
    by_cases h : ∃ o ∈ outputs, o.1 = t+1
    · obtain ⟨o, ho, he⟩ := h
      exact he ▸ event o ho
    · apply Nat.le_trans _ ih
      have point (o : Output) (ho : o ∈ outputs) : stock o.1 o.2 (t+1) ≤ stock o.1 o.2 t := by
        have ne : o.1 ≠ t+1 := fun eq => h ⟨o,ho,eq⟩
        unfold stock
        split <;> split <;> omega
      unfold occupancy
      have mono (l : List Output) (hp : ∀ o ∈ l, stock o.1 o.2 (t+1) ≤ stock o.1 o.2 t) :
          (l.map (fun o => stock o.1 o.2 (t+1))).sum ≤ (l.map (fun o => stock o.1 o.2 t)).sum := by
        induction l with
        | nil => simp
        | cons o l ih' =>
          simp only [List.map_cons, List.sum_cons]
          exact Nat.add_le_add (hp o (by simp)) (ih' (fun x hx => hp x (by simp [hx])))
      exact mono outputs point




theorem schedule (B N : Nat) (outputs : List Output) (hB : 0 < B)
    (ha : ∀ o ∈ outputs, o.2 ≤ B) (hN : ∀ o ∈ outputs, o.1 + o.2 ≤ N)
    (fits : ∀ t, occupancy outputs t ≤ B) :
    (∀ t, occupancy outputs t ≤ B) ∧
    (∀ o ∈ outputs, ∀ t, stock o.1 o.2 t ≤
      (if t = 0 then 0 else stock o.1 o.2 (t-1) - 1) +
      (if t ≤ o.1 then B else 0)) ∧
    (outputs.map (fun o => ((List.range N).map (fun t => sent (stock o.1 o.2 t))).sum)).sum =
      (outputs.map (fun o => o.1 + o.2)).sum := by
  refine ⟨fits, fun o ho t => refill B o.1 o.2 t hB (ha o ho), ?_⟩
  congr 1
  apply List.map_congr_left
  exact fun o ho => payoff o.1 o.2 N (hN o ho)

#print axioms fromEvents
#print axioms schedule
#print axioms blockResidual
end SharedBuffer.Offline
