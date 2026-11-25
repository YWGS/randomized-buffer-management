import Std









set_option exponentiation.threshold 5000
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

namespace BufferWitness

def total (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => total f n + f n

def eleven (f : Nat → Nat) (i : Nat) : Nat :=
  f i + f (i + 1) + f (i + 2) + f (i + 3) + f (i + 4) + f (i + 5) + f (i + 6) + f (i + 7) + f (i + 8) + f (i + 9) + f (i + 10)

def potential (p : Nat → Nat) (i : Nat) : Nat :=
  20 * p (i+11) + eleven p i

theorem expand_eleven (f : Nat → Nat) (i : Nat) :
    total f (i+11) = total f i + eleven f i := by
  simp only [total, eleven, Nat.add_assoc]

theorem potential_step (p : Nat → Nat) (i budget : Nat)
    (cap : 20*p (i+12) + p (i+11) ≤ budget + 20*p (i+11) + p i) :
    potential p (i+1) ≤ potential p i + budget := by
  simp only [potential, eleven, Nat.add_assoc, Nat.reduceAdd] at *
  omega

theorem aggregate (f : Nat → Nat) (budget stock : Nat)
    (initial : potential (total f) 0 = 0)
    (row : ∀ i < 1600, 20 * f (i+11) + eleven f i ≤ budget)
    (single : ∀ i < 1600, 20 * f (i+11) ≤ stock) :
    620 * total f 1611 ≤ 32000 * budget + 66 * stock := by
  have byTime : ∀ t ≤ 1600, potential (total f) t ≤ t*budget := by
    intro t
    induction t with
    | zero => simp [initial]
    | succ t ih =>
      intro ht
      have hlt : t < 1600 := by omega
      have hcap : 20 * total f (t+12) + total f (t+11) ≤
          budget + 20*total f (t+11) + total f t := by
        have cur := row t hlt
        have seg := expand_eleven f t
        have next : total f (t+12) = total f (t+11) + f (t+11) := rfl
        omega
      have hs := potential_step (total f) t budget hcap
      have old := ih (by omega)
      rw [Nat.succ_mul]
      omega
  have last := byTime 1600 (by decide)
  simp only [potential, eleven] at last
  have one (i : Nat) (h : i < 1600) :
      20 * total f (i+12) ≤ 20 * total f (i+11) + stock := by
    have cap := single i h
    have next : total f (i+12) = total f (i+11) + f (i+11) := rfl
    omega
  have h1589 := one 1589 (by decide)
  have h1590 := one 1590 (by decide)
  have h1591 := one 1591 (by decide)
  have h1592 := one 1592 (by decide)
  have h1593 := one 1593 (by decide)
  have h1594 := one 1594 (by decide)
  have h1595 := one 1595 (by decide)
  have h1596 := one 1596 (by decide)
  have h1597 := one 1597 (by decide)
  have h1598 := one 1598 (by decide)
  have h1599 := one 1599 (by decide)
  simp only [Nat.reduceAdd] at last h1589 h1590 h1591 h1592 h1593 h1594 h1595 h1596 h1597 h1598 h1599
  omega

def B : Nat := 400 * 380^1599
def K : Nat := 20^1600
def prior : Nat := 76*B
def q : Nat := ((B-K)*333)/4000

def groupSize (j : Nat) := 20^(1599-j) * 19^j
def duration (j : Nat) := 20^j * 19^(1599-j)
def eventTime := total duration
def agingStep (k : Nat) := 20^(1599+k) * 19^(1599-k)
def lagCost := total agingStep

theorem age_step (j k : Nat) (inRange : j+k < 1600) :
    groupSize j * duration (j+k) = agingStep k := by
  calc
    _ = 20^((1599-j)+(j+k)) * 19^(j+(1599-(j+k))) := by
      simp only [groupSize, duration, Nat.pow_add]
      ac_rfl
    _ = _ := by
      have a : 1599-j+(j+k) = 1599+k := by omega
      have b : j+(1599-(j+k)) = 1599-k := by omega
      rw [a, b]
      rfl

theorem geometric_age (j k : Nat) (inRange : j+k ≤ 1600) :
    groupSize j * eventTime (j+k) = groupSize j * eventTime j + lagCost k := by
  induction k with
  | zero => simp [lagCost, total]
  | succ k ih =>
    have h : j+k < 1600 := by omega
    have prev := ih (by omega)
    have age := age_step j k h
    change groupSize j * (eventTime (j+k) + duration (j+k)) =
      groupSize j * eventTime j + (lagCost k + agingStep k)
    rw [Nat.mul_add, prev, age, Nat.add_assoc]

def budget : Nat := B + lagCost 1 + lagCost 2 + lagCost 3 + lagCost 4 + lagCost 5 + lagCost 6 + lagCost 7 + lagCost 8 + lagCost 9 + lagCost 10 + lagCost 11
def offline : Nat := prior + 1600*q
def upper620 : Nat := 620*(prior+B) + 32000*budget + 66*B


theorem exact_gap : 3*upper620 < 2*620*offline := by decide

theorem finite_separation (f : Nat → Nat) (D A O : Nat)
    (positive : 0 < D)
    (initial : potential (total f) 0 = 0)
    (row : ∀ i < 1600, 20*f (i+11) + eleven f i ≤ budget*D)
    (single : ∀ i < 1600, 20*f (i+11) ≤ B*D)
    (online : A ≤ (prior+B)*D + total f 1611)
    (feasible : offline*D ≤ O) :
    3*A < 2*O := by
  have agg := aggregate f (budget*D) (B*D) initial row single
  have adv := Nat.mul_lt_mul_of_pos_right exact_gap positive
  have upper : 620*A ≤ upper620*D := by
    simp only [Nat.add_mul] at online
    simp only [upper620, Nat.add_mul, Nat.mul_assoc]
    omega
  have lower := Nat.mul_le_mul_left (2*620) feasible
  simp only [Nat.mul_assoc] at adv lower
  omega



def terms (f : Nat → Nat) (D i : Nat) : List (Nat × Nat) :=
  [(f i, lagCost 11 * D),
   (f (i+1), lagCost 10 * D),
   (f (i+2), lagCost 9 * D),
   (f (i+3), lagCost 8 * D),
   (f (i+4), lagCost 7 * D),
   (f (i+5), lagCost 6 * D),
   (f (i+6), lagCost 5 * D),
   (f (i+7), lagCost 4 * D),
   (f (i+8), lagCost 3 * D),
   (f (i+9), lagCost 2 * D),
   (f (i+10), lagCost 1 * D)]

def residual (xs : List (Nat × Nat)) : Nat :=
  (xs.map (fun p => p.1 - p.2)).sum

theorem reverse_truncation (xs : List (Nat × Nat)) :
    (xs.map Prod.fst).sum ≤ residual xs + (xs.map Prod.snd).sum := by
  induction xs with
  | nil => simp [residual]
  | cons x xs ih =>
    have h : x.1 ≤ (x.1-x.2)+x.2 := by omega
    simp only [residual, List.map_cons, List.sum_cons] at *
    omega




theorem finite_from_inventory (f : Nat → Nat) (D A O : Nat)
    (positive : 0 < D)
    (initial : potential (total f) 0 = 0)
    (inventory : ∀ i < 1600, 20*f (i+11) + residual (terms f D i) ≤ B*D)
    (online : A ≤ (prior+B)*D + total f 1611)
    (feasible : offline*D ≤ O) :
    3*A < 2*O := by
  apply finite_separation f D A O positive initial _ _ online feasible
  · intro i hi
    have h := inventory i hi
    have hh := reverse_truncation (terms f D i)
    have hl : ((terms f D i).map Prod.fst).sum = eleven f i := by
      simp [terms, eleven, Nat.add_assoc]
    have hr : B*D + ((terms f D i).map Prod.snd).sum = budget*D := by
      simp only [terms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        budget, Nat.add_mul]
      omega
    rw [hl] at hh
    omega
  · intro i hi
    have h := inventory i hi
    omega


theorem numerical_margin : 1505*upper620 < 1000*620*offline := by decide




def stockEnvelope : Nat := total (fun k => q-lagCost k) 20

theorem stock_fits : K + stockEnvelope ≤ B := by decide
theorem twenty_events_drain : q ≤ lagCost 20 := by decide

theorem total_mono (f : Nat → Nat) (i j : Nat) (h : i ≤ j) :
    total f i ≤ total f j := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    simp [this]
  | succ j ih =>
    by_cases e : i = j+1
    · simp [e]
    · have prev := ih (by omega)
      change total f i ≤ total f j + f j
      omega

theorem any_event_fits (count live : Nat) (h : live ≤ K) :
    live + total (fun k => q-lagCost k) count ≤ B := by
  have bound : total (fun k => q-lagCost k) count ≤ stockEnvelope := by
    induction count with
    | zero => simp [total]
    | succ c ih =>
      by_cases stop : c < 20
      · exact total_mono _ _ 20 (by omega)
      · have old := total_mono agingStep 20 c (by omega)
        have start := twenty_events_drain
        change lagCost 20 ≤ lagCost c at old
        have empty : q-lagCost c = 0 := by omega
        change total (fun k => q-lagCost k) c + (q-lagCost c) ≤ stockEnvelope
        simpa [empty] using ih
  have fits := stock_fits
  omega

end BufferWitness

#print axioms BufferWitness.aggregate
#print axioms BufferWitness.exact_gap
#print axioms BufferWitness.finite_separation

#print axioms BufferWitness.finite_from_inventory
#print axioms BufferWitness.numerical_margin

#print axioms BufferWitness.geometric_age
#print axioms BufferWitness.any_event_fits
