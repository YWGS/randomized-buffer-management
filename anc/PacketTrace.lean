import finiteThroughput
import Repeat



namespace SharedBuffer.Packet
open HiddenStock MeasureTheory
open BufferWitness.Physical (serving)

def sent (ports : List α) (q : α → ℕ) := total ports (fun l => tx (q l))
def left (q : α → ℕ) (l : α) := q l - tx (q l)



inductive CanSend (B : ℕ) (ports : List α) :
    (α → ℕ) → List (α → ℕ) → ℕ → Prop where
  | nil (prior) : CanSend B ports prior [] 0
  | cons {prior a more q count} (budget : total ports q ≤ B)
      (supply : ∀ l ∈ ports, q l ≤ prior l + a l)
      (tail : CanSend B ports (left q) more count) :
      CanSend B ports prior (a::more) (sent ports q + count)

theorem CanSend.moreStock {B : ℕ} {ports : List α} {p q I n}
    (h : CanSend B ports p I n) (hle : ∀ l ∈ ports, p l ≤ q l) :
    CanSend B ports q I n := by
  cases h with
  | nil => exact .nil _
  | cons cap supply tail =>
    exact .cons cap (fun l hl => (supply l hl).trans (Nat.add_le_add_right (hle l hl) _)) tail

theorem CanSend.append {B : ℕ} {ports : List α} {p I m J n}
    (h : CanSend B ports p I m) (g : CanSend B ports (fun _ => 0) J n) :
    CanSend B ports p (I++J) (m+n) := by
  induction h with
  | nil p => simpa using g.moreStock (q:=p) (fun _ _ => Nat.zero_le _)
  | @cons prior a more q count cap supply tail ih =>
    simpa [Nat.add_assoc] using CanSend.cons cap supply ih

theorem CanSend.discard (B : ℕ) (ports : List α) (I : List (α → ℕ)) :
    CanSend B ports (fun _ => 0) I 0 := by
  induction I with
  | nil => exact .nil _
  | cons a I ih =>
    have zero : sent ports (fun _ => 0) = 0 := by simp [sent, tx, total_const]
    have h := CanSend.cons (q:=fun _ => 0) (prior:=fun _ => 0) (a:=a)
      (by simp [total_const]) (fun _ _ => Nat.zero_le _) ih
    simpa [zero] using h


def count (ports : List α) (p : Policy α) (past : List (α → ℕ)) :
    List (α → ℕ) → ℕ
  | [] => 0
  | a::rest => sent ports (p (past++[a])) + count ports p (past++[a]) rest

theorem count_append (ports : List α) (p : Policy α) (past I J : List (α → ℕ)) :
    count ports p past (I++J) = count ports p past I + count ports p (past++I) J := by
  induction I generalizing past with
  | nil => simp [count]
  | cons a I ih => simp [count, ih, List.append_assoc, Nat.add_assoc]

theorem count_bound (ports : List α) (p : Policy α) (past I) :
    count ports p past I ≤ I.length * ports.length := by
  induction I generalizing past with
  | nil => simp [count]
  | cons a I ih =>
    have h : sent ports (p (past++[a])) ≤ ports.length := deliveries_rate (fun _ => p (past++[a])) ports 0
    simp only [count, List.length_cons, Nat.add_mul, Nat.one_mul]
    exact (Nat.add_le_add h (ih _)).trans_eq (Nat.add_comm _ _)



structure PolicyLaw (B : ℕ) (ports : List α) where
  Seed : Type
  [meas : MeasurableSpace Seed]
  mu : Measure Seed
  [prob : IsProbabilityMeasure mu]
  keep : Seed → Policy α
  measurable_keep : ∀ I l, Measurable (fun s => keep s I l)
  initial : ∀ s l, keep s [] l = 0
  capacity : ∀ s I, total ports (keep s I) ≤ B
  admit : ∀ s I a l, keep s (I++[a]) l ≤ left (keep s I) l + a l

attribute [instance] PolicyLaw.meas PolicyLaw.prob

theorem PolicyLaw.measurable_count {ports : List α} (p : PolicyLaw B ports) (past I) :
    Measurable (fun s => count ports (p.keep s) past I) := by
  have ms (pre : List (α → ℕ)) (ls : List α) :
      Measurable (fun s => sent ls (p.keep s pre)) := by
    induction ls with
    | nil => exact measurable_const
    | cons l ls ih =>
      exact ((measurable_of_countable tx).comp (p.measurable_keep pre l)).add ih
  induction I generalizing past with
  | nil => exact measurable_const
  | cons a I ih => exact (ms _ _).add (ih _)

theorem PolicyLaw.integrable_count {ports : List α} (p : PolicyLaw B ports) (past I) :
    Integrable (fun s => (count ports (p.keep s) past I : ℝ)) p.mu := by
  refine ⟨((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (p.measurable_count past I)).aestronglyMeasurable, ?_⟩
  apply hasFiniteIntegral_of_bounded (C:=((I.length*ports.length : ℕ):ℝ))
  exact Filter.Eventually.of_forall (fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast count_bound ports (p.keep s) past I)




def Competitive {ports : List α} (p : PolicyLaw B ports) (R allowance : ℝ) : Prop :=
  ∀ I n, CanSend B ports (fun _ => 0) (I ++ List.replicate B (fun _ => 0)) n →
    (n : ℝ) ≤ R*(∫ s, (count ports (p.keep s) [] (I ++ List.replicate B (fun _ => 0)) : ℝ) ∂p.mu) + allowance



theorem Competitive.prefix {ports : List α} {p : PolicyLaw B ports} {R h : ℝ}
    (comp : Competitive p R h) (hR : 0≤R) (I n) (path : CanSend B ports (fun _ => 0) I n) :
    (n:ℝ) ≤ R*(∫ s, (count ports (p.keep s) [] I : ℝ) ∂p.mu) + (h+R*(B*ports.length)) := by
  let tail : List (α → ℕ) := List.replicate B (fun _ => 0)
  have hc := comp I n (by simpa [tail] using path.append (CanSend.discard B ports tail))
  have mono : (∫ s, (count ports (p.keep s) [] (I++tail) : ℝ) ∂p.mu) ≤
      ∫ s, ((count ports (p.keep s) [] I : ℝ) + (B*ports.length)) ∂p.mu := by
    apply integral_mono (p.integrable_count [] _) ((p.integrable_count [] _).add (integrable_const _))
    intro s
    change (count ports (p.keep s) [] (I++tail):ℝ) ≤ (count ports (p.keep s) [] I:ℝ) + _
    rw [count_append, Nat.cast_add]
    apply add_le_add_left
    have bd := count_bound ports (p.keep s) ([]++I) tail
    simp [tail] at bd
    change (count ports (p.keep s) I tail : ℝ) ≤ (B:ℝ)*ports.length
    exact_mod_cast bd
  rw [integral_add (p.integrable_count [] I) (integrable_const _), integral_const] at mono
  simp at mono
  change _ ≤ R * (∫ s, (count ports (p.keep s) [] (I++tail) : ℝ) ∂p.mu) + h at hc
  linarith [mul_le_mul_of_nonneg_left mono hR]

def stream (a : ℕ → α) (t : ℕ) := (List.range t).map a

theorem stream_succ (a : ℕ → α) (t : ℕ) : stream a (t+1) = stream a t ++ [a t] := by
  simp [stream, List.range_succ]


def arrivals [DecidableEq α] (B : ℕ) (date : ℕ → ℕ) (assignment : List (List α))
    (t : ℕ) (l : α) := offered B t (expiry date assignment 0 l)

def shifted (p : Policy α) (past : List (α → ℕ)) : Policy α := fun observations => p (past++observations)

theorem shifted_admit [DecidableEq α] {ports : List α} (p : PolicyLaw B ports)
    (s : p.Seed) (past) (date) (a : List (List α)) (t l) :
    run B date (shifted (p.keep s) past) a (t+1) l ≤
      run B date (shifted (p.keep s) past) a t l -
      tx (run B date (shifted (p.keep s) past) a t l) + offered B (t+1) (expiry date a 0 l) := by
  have eq := stream_succ (arrivals B date a) (t+1)
  change p.keep s (past ++ stream (arrivals B date a) (t+1+1)) l ≤ _
  rw [eq, ← List.append_assoc]
  exact p.admit s _ _ _

theorem shifted_capacity [DecidableEq α] {ports : List α} (p : PolicyLaw B ports)
    (s : p.Seed) (past) (date) (a : List (List α)) (t) :
    total ports (run B date (shifted (p.keep s) past) a t) ≤ B := p.capacity s _

def window (a : ℕ → α) (start : ℕ) : ℕ → List α
  | 0 => []
  | n+1 => a start :: window a (start+1) n

theorem window_succ_last (a : ℕ → α) (t n : ℕ) :
    window a t (n+1) = window a t n ++ [a (t+n)] := by
  induction n generalizing t with
  | zero => simp [window]
  | succ n ih =>
    change a t :: window a (t+1) (n+1) = a t :: (window a (t+1) n ++ [a (t+(n+1))])
    rw [ih, show t+1+n = t+(n+1) by omega]

theorem stream_slots (a : ℕ → α) (t : ℕ) : stream a t = window a 0 t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [stream_succ, ih, window_succ_last, Nat.zero_add]

theorem count_slots (ports : List α) (p : Policy α) (past) (a : ℕ → α → ℕ) (offset n : ℕ) :
    count ports p (past ++ stream a offset) (window a offset n) =
    serving (fun t => p (past ++ stream a (t+1))) ports offset n := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih =>
    simp only [window, count]
    rw [List.append_assoc, ← stream_succ, ih]
    rfl

theorem count_cohort [DecidableEq α] (ports : List α) (B : ℕ) (p : Policy α) (past)
    (date : ℕ → ℕ) (a : List (List α)) (f : ℕ) :
    count ports p past (stream (arrivals B date a) f) =
      serving (run B date (shifted p past) a) ports 0 f := by
  rw [stream_slots]
  simpa only [stream, List.range_zero, List.map_nil, List.append_nil, shifted, run, arrivals] using
    (count_slots ports p past (arrivals B date a) 0 f)



theorem CanSend.of_run (B : ℕ) (ports : List α) (a Q : ℕ → α → ℕ) (f : ℕ)
    (cap : ∀ t, total ports (Q t) ≤ B)
    (initial : ∀ l ∈ ports, Q 0 l ≤ a 0 l)
    (step : ∀ t l, l ∈ ports → Q (t+1) l ≤ left (Q t) l + a (t+1) l) :
    CanSend B ports (fun _ => 0) (stream a f) (serving Q ports 0 f) := by
  have segment (t n : ℕ) (p : α → ℕ) (hp : ∀ l ∈ ports, Q t l ≤ p l + a t l) :
      CanSend B ports p (window a t n) (serving Q ports t n) := by
    induction n generalizing t p with
    | zero => exact .nil _
    | succ n ih => exact .cons (cap t) hp (ih (t+1) _ (step t))
  rw [stream_slots]
  exact segment 0 f _ (by simpa using initial)



def priorInputs {α β : Type} (block : β → List (α → ℕ)) : List β → List (α → ℕ)
  | [] => []
  | a::past => priorInputs block past ++ block a

noncomputable def blockGain {α β : Type} (ports : List α) (p : Policy α)
    (block : β → List (α → ℕ)) (past : List β) (a : β) : ℝ :=
  count ports p (priorInputs block past) (block a)

theorem play_counts {α β : Type} (ports : List α) (p : Policy α) (block : β → List (α → ℕ))
    (past l : List β) :
    Repeat.play (blockGain ports p block) past l =
      (count ports p (priorInputs block past) (l.flatMap block) : ℝ) := by
  induction l generalizing past with
  | nil => simp [Repeat.play, count]
  | cons a l ih =>
    rw [Repeat.play, ih, List.flatMap_cons, count_append, Nat.cast_add]
    rfl

theorem repeatedOffline {α β : Type} (B : ℕ) (ports : List α) (block : β → List (α → ℕ)) (pay : ℕ)
    (one : ∀ a, CanSend B ports (fun _ => 0) (block a) pay) (l : List β) :
    CanSend B ports (fun _ => 0) (l.flatMap block) (l.length*pay) := by
  induction l with
  | nil => simpa using (CanSend.nil (B:=B) (ports:=ports) (fun _ => 0))
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    exact (one a).append ih

#print axioms Competitive.prefix
#print axioms CanSend.of_run
end SharedBuffer.Packet
