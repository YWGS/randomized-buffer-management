import Std






namespace HiddenStock

def total (xs : List α) (f : α → Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: ys => f x + total ys f

theorem total_append (xs ys : List α) (f : α → Nat) :
    total (xs ++ ys) f = total xs f + total ys f := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp [total, ih, Nat.add_assoc]

theorem total_map (xs : List α) (g : α → β) (f : β → Nat) :
    total (xs.map g) f = total xs (fun x => f (g x)) := by
  induction xs <;> simp_all [total]

theorem total_add (xs : List α) (f g : α → Nat) :
    total xs (fun x => f x + g x) = total xs f + total xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [total, ih]; omega

theorem total_const (xs : List α) (c : Nat) :
    total xs (fun _ => c) = xs.length * c := by
  induction xs <;> simp_all [total, Nat.succ_mul, Nat.add_comm]

theorem total_congr (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x = g x) : total xs f = total xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [total]
    rw [h x (by simp), ih (by intro y hy; exact h y (by simp [hy]))]

theorem total_le (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x ≤ g x) : total xs f ≤ total xs g := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    exact Nat.add_le_add (h x (by simp)) (ih (by intro y hy; exact h y (by simp [hy])))

theorem total_swap (xs : List α) (ys : List β) (f : α → β → Nat) :
    total xs (fun x => total ys (f x)) =
      total ys (fun y => total xs (fun x => f x y)) := by
  induction xs with
  | nil => simp [total, total_const]
  | cons x xs ih => simp only [total, total_add, ih]


def blocks : List α → Nat → List (List α)
  | [], 0 => [[]]
  | [], _ + 1 => []
  | _ :: _, 0 => [[]]
  | x :: xs, k + 1 => blocks xs (k+1) ++ (blocks xs k).map (x :: ·)


def choose : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _+1, 0 => 1
  | n+1, k+1 => choose n (k+1) + choose n k

theorem blocks_length (xs : List α) (k : Nat) :
    (blocks xs k).length = choose xs.length k := by
  induction xs generalizing k with
  | nil => cases k <;> rfl
  | cons x xs ih => cases k <;> simp [blocks, choose, ih]

theorem selected_length (xs : List α) (k : Nat) (b : List α)
    (hb : b ∈ blocks xs k) : b.length = k := by
  induction xs generalizing k b with
  | nil =>
    cases k with
    | zero => simp [blocks] at hb; subst b; rfl
    | succ k => simp [blocks] at hb
  | cons x xs ih =>
    cases k with
    | zero => simp [blocks] at hb; subst b; rfl
    | succ k =>
      simp only [blocks, List.mem_append, List.mem_map] at hb
      rcases hb with h | ⟨t, ht, heq⟩
      · exact ih _ _ h
      · subst b; simp [ih _ _ ht]

theorem include_weight (xs : List (List α)) (x : α) (stock : α → Nat) :
    total (xs.map (x :: ·)) (fun b => total b stock) =
      xs.length * stock x + total xs (fun b => total b stock) := by
  rw [total_map]; simp only [total, total_add, total_const]


theorem counted_weight (x : α) (xs : List α) (k : Nat) (stock : α → Nat) :
    total (blocks (x :: xs) (k+1)) (fun b => total b stock) =
      choose xs.length k * total (x :: xs) stock := by
  induction xs generalizing x k with
  | nil => cases k <;> simp [blocks, choose, total]
  | cons y ys ih =>
    cases k with
    | zero =>
      change total (blocks (y::ys) 1 ++ (blocks (y::ys) 0).map (x :: ·)) _ = _
      rw [total_append, include_weight, ih]
      cases ys <;> simp [blocks, choose, total, Nat.add_comm, Nat.add_left_comm]
    | succ k =>
      change total (blocks (y::ys) (k+1+1) ++ (blocks (y::ys) (k+1)).map (x :: ·)) _ = _
      rw [total_append, include_weight, blocks_length, ih, ih]
      simp only [List.length_cons, choose, total, Nat.add_mul, Nat.mul_add]
      omega


theorem uniform_block_identity (x : α) (xs : List α) (k : Nat) (stock : α → Nat) :
    (x::xs).length * total (blocks (x::xs) (k+1)) (fun b => total b stock) =
    ((blocks (x::xs) (k+1)).length * (k+1)) * total (x::xs) stock := by
  have hc := counted_weight x xs k (fun _ => 1)
  have hl : total (blocks (x::xs) (k+1)) (fun b => total b (fun _ => 1)) =
        (blocks (x::xs) (k+1)).length * (k+1) := by
    rw [← total_const]
    apply total_congr
    intro b hb
    rw [total_const, Nat.mul_one, selected_length _ _ _ hb]
  rw [hl, total_const, Nat.mul_one] at hc
  rw [counted_weight, ← Nat.mul_assoc, Nat.mul_comm (x::xs).length (choose xs.length k), ← hc]



theorem post_stock (before after sent : Nat)
    (h : after + sent ≤ before) : sent ≤ before := by omega



theorem conditional_live (x : α) (xs : List α) (k : Nat)
    (stock : α → Nat) (sent : List α → Nat)
    (h : ∀ b ∈ blocks (x::xs) (k+1), sent b ≤ total b stock) :
    (x::xs).length * total (blocks (x::xs) (k+1)) sent ≤
    ((blocks (x::xs) (k+1)).length * (k+1)) * total (x::xs) stock := by
  rw [← uniform_block_identity]
  exact Nat.mul_le_mul_left _ (total_le _ _ _ h)


theorem old_group (worlds : List α) (sent kept : α → Nat) (ageBudget : Nat)
    (h : ∀ w ∈ worlds, sent w ≤ kept w + ageBudget) :
    total worlds sent - worlds.length * ageBudget ≤ total worlds kept := by
  have h' := total_le worlds sent (fun w => kept w + ageBudget) h
  rw [total_add, total_const] at h'
  omega



theorem event_inventory (worlds : List α) (prior : List β) (u d B : Nat)
    (lastSent live : α → Nat) (pastSent kept : α → β → Nat) (age : β → Nat)
    (hLive : u * total worlds lastSent ≤ d * total worlds live)
    (hService : ∀ w ∈ worlds, ∀ j ∈ prior, pastSent w j ≤ kept w j + age j)
    (hCap : ∀ w ∈ worlds, live w + total prior (kept w) ≤ B) :
    u * total worlds lastSent +
      d * total prior (fun j => total worlds (fun w => pastSent w j) -
                                  worlds.length * age j) ≤ d * (worlds.length * B) := by
  have ho := total_le prior _ _ (fun j hj =>
    old_group worlds (fun w => pastSent w j) (fun w => kept w j) (age j)
      (fun w hw => hService w hw j hj))
  have hc := total_le worlds _ (fun _ => B) hCap
  rw [total_add, total_swap, total_const] at hc
  calc
    _ ≤ d * total worlds live + d * total prior (fun j => total worlds (fun w => kept w j)) :=
      Nat.add_le_add hLive (Nat.mul_le_mul_left d ho)
    _ = d * (total worlds live + total prior (fun j => total worlds (fun w => kept w j))) :=
      (Nat.mul_add ..).symm
    _ ≤ _ := Nat.mul_le_mul_left d hc


theorem total_flatMap (xs : List α) (children : α → List β) (f : β → Nat) :
    total (xs.flatMap children) f = total xs (fun x => total (children x) f) := by
  induction xs <;> simp_all [total, total_append]

theorem total_scale (xs : List α) (f : α → Nat) (c : Nat) :
    total xs (fun x => c * f x) = c * total xs f := by
  induction xs <;> simp_all [total, Nat.mul_add]


def splits : List α → Nat → List (List α × List α)
  | [], 0 => [([], [])]
  | [], _+1 => []
  | x::xs, 0 => [([], x::xs)]
  | x::xs, k+1 =>
    ((splits xs (k+1)).map (fun b => (b.1, x::b.2))) ++
    ((splits xs k).map (fun b => (x::b.1, b.2)))

theorem split_blocks (xs : List α) (d : Nat) :
    (splits xs d).map Prod.fst = blocks xs d := by
  induction xs generalizing d with
  | nil => cases d <;> rfl
  | cons x xs ih =>
    cases d with
    | zero => rfl
    | succ d =>
      simp only [splits, blocks, List.map_append, List.map_map, Function.comp_def]
      rw [← ih d]
      simp only [List.map_map, Function.comp_def]
      rw [← ih (d+1)]

theorem split_length (xs : List α) (d : Nat) :
    (splits xs d).length = choose xs.length d := by
  have h := congrArg List.length (split_blocks xs d)
  simpa only [List.length_map, blocks_length] using h

theorem split_rest (xs : List α) (d : Nat) (b : List α × List α)
    (hb : b ∈ splits xs d) : b.2.length + d = xs.length := by
  induction xs generalizing b d with
  | nil =>
    cases d with
    | zero => simp [splits] at hb; subst b; rfl
    | succ d => simp [splits] at hb
  | cons x xs ih =>
    cases d with
    | zero => simp [splits] at hb; subst b; simp
    | succ d =>
      simp only [splits, List.mem_append, List.mem_map] at hb
      rcases hb with ⟨c,hc,heq⟩ | ⟨c,hc,heq⟩
      · subst b; have he := ih (d+1) c hc; simp; omega
      · subst b; have he := ih d c hc; simp; omega



def histories (labels : List α) : List Nat → List (List (List α) × List α)
  | [] => [([],labels)]
  | d :: ds => (splits labels d).flatMap (fun b =>
      (histories b.2 ds).map (fun h => (b.1::h.1,h.2)))

def nHist (u : Nat) : List Nat → Nat
  | [] => 1
  | d::ds => choose u d * nHist (u-d) ds

theorem length_histories (labels : List α) (groups : List Nat) :
    (histories labels groups).length = nHist labels.length groups := by
  induction groups generalizing labels with
  | nil => rfl
  | cons d ds ih =>
    rw [histories, nHist]
    have foldlen {β γ : Type _} (bs : List β) (f : β → List γ) :
        (bs.flatMap f).length = total bs (fun b => (f b).length) := by
      induction bs <;> simp_all [total]
    rw [foldlen]
    simp only [List.length_map, ih]
    calc
      _ = total (splits labels d) (fun _ => nHist (labels.length-d) ds) := by
        apply total_congr; intro b hb
        have he := split_rest labels d b hb
        congr 1; omega
      _ = _ := by rw [total_const, split_length]

theorem history_rest (labels : List α) (groups : List Nat) (h : List (List α) × List α)
    (hh : h ∈ histories labels groups) : h.2.length + groups.sum = labels.length := by
  induction groups generalizing labels h with
  | nil => simp [histories] at hh; subst h; simp
  | cons d ds ih =>
    simp only [histories, List.mem_flatMap, List.mem_map] at hh
    rcases hh with ⟨b, hb, h', hh', eq⟩
    subst h
    have he := ih b.2 h' hh'
    have hb' := split_rest labels d b hb
    simp only [List.sum_cons]; omega



structure World (α : Type u) where
  past : List (List α)
  live : List α
  chosen : List α
  future : List (List α)

def layer (history : List (List α) × List α) (d : Nat) (future : List Nat) :
    List (World α) :=
  (splits history.2 d).flatMap (fun b =>
    (histories b.2 future).map (fun s => ⟨history.1,history.2,b.1,s.1⟩))

def worlds (labels : List α) (past : List Nat) (d : Nat) (future : List Nat) :
    List (World α) :=
  (histories labels past).flatMap (fun h => layer h d future)

theorem layer_live (hist : List (List α) × List α) (k : Nat) (future : List Nat)
    (stock : List (List α) → α → Nat) (z : World α → Nat)
    (hService : ∀ w ∈ layer hist (k+1) future, z w ≤ total w.chosen (stock w.past)) :
    hist.2.length * total (layer hist (k+1) future) z ≤
      (k+1) * total (layer hist (k+1) future) (fun _ => total hist.2 (stock hist.1)) := by
  let d := k+1
  let restCount := nHist (hist.2.length - d) future
  let P := total hist.2 (stock hist.1)
  have expand (f : List α → Nat) :
      total (layer hist d future) (fun w => f w.chosen) =
      restCount * total (blocks hist.2 d) f := by
    rw [layer, total_flatMap]
    simp only [total_map, total_const, length_histories]
    calc
      _ = total (splits hist.2 d) (fun b => restCount * f b.1) := by
        apply total_congr; intro b hb
        have he := split_rest hist.2 d b hb
        have ha : b.2.length = hist.2.length-d := by omega
        rw [ha]
      _ = _ := by rw [total_scale, ← split_blocks, total_map]
  have pastFixed : ∀ w ∈ layer hist d future, w.past = hist.1 := by
    intro w hw
    simp only [layer, List.mem_flatMap, List.mem_map] at hw
    rcases hw with ⟨b,_,s,_,h⟩; subst w; rfl
  have hZ : total (layer hist d future) z ≤
        total (layer hist d future) (fun w => total w.chosen (stock hist.1)) := by
    apply total_le; intro w hw
    simpa only [pastFixed w hw] using hService w hw
  have hid : hist.2.length * total (blocks hist.2 d) (fun b => total b (stock hist.1)) =
      ((blocks hist.2 d).length * d) * P := by
    dsimp only [d,P]
    cases hls : hist.2 with
    | nil => simp [blocks,total]
    | cons x xs => exact uniform_block_identity x xs k (stock hist.1)
  change hist.2.length * total (layer hist d future) z ≤ d * total (layer hist d future) (fun _ => P)
  calc
    _ ≤ hist.2.length * total (layer hist d future) (fun w => total w.chosen (stock hist.1)) :=
      Nat.mul_le_mul_left _ hZ
    _ = restCount * (hist.2.length * total (blocks hist.2 d) (fun b => total b (stock hist.1))) := by
      rw [expand (fun b => total b (stock hist.1))]; ac_rfl
    _ = restCount * (((blocks hist.2 d).length * d) * P) := by rw [hid]
    _ = d * (restCount * total (blocks hist.2 d) (fun _ => P)) := by
      rw [total_const]; ac_rfl
    _ = _ := by rw [← expand (fun _ => P)]





theorem whole_history_live (labels : List α) (past future : List Nat) (k : Nat)
    (stock : List (List α) → α → Nat) (z : World α → Nat)
    (hService : ∀ w ∈ worlds labels past (k+1) future,
                   z w ≤ total w.chosen (stock w.past)) :
    (labels.length-past.sum) * total (worlds labels past (k+1) future) z ≤
      (k+1) * total (worlds labels past (k+1) future) (fun w => total w.live (stock w.past)) := by
  rw [worlds, total_flatMap, total_flatMap, ← total_scale, ← total_scale]
  apply total_le
  intro h hh
  have he := history_rest labels past h hh
  have hs : labels.length-past.sum = h.2.length := by omega
  rw [hs]
  have frozen : total (layer h (k+1) future) (fun w => total w.live (stock w.past)) =
          total (layer h (k+1) future) (fun _ => total h.2 (stock h.1)) := by
    apply total_congr; intro w hw
    simp only [layer, List.mem_flatMap, List.mem_map] at hw
    rcases hw with ⟨b,_,s,_,heq⟩; subst w; rfl
  rw [frozen]
  apply layer_live
  intro w hw
  apply hService
  exact List.mem_flatMap.mpr ⟨h,hh,hw⟩

#print axioms whole_history_live




inductive Closed (size : Nat) : Nat → List Nat → Nat → Prop where
  | nil (q : Nat) : Closed size q [] q
  | step {before remaining final sent : Nat} {later : List Nat}
      (portRate : sent ≤ size) (inventory : sent + remaining ≤ before)
      (tail : Closed size remaining later final) :
      Closed size before (sent :: later) final

theorem no_future_arrivals {size stock final : Nat} {svc : List Nat}
    (h : Closed size stock svc final) : svc.sum + final ≤ stock := by
  induction h with
  | nil => simp
  | step rate inventory tail ih => simp only [List.sum_cons]; omega

theorem elapsed_slots (p : List Nat) (size : Nat) (h : ∀ s ∈ p, s ≤ size) :
    p.sum ≤ p.length * size := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have ha := h a (by simp)
    have hp := ih (by intro s hs; exact h s (by simp [hs]))
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]; omega




def offered (B t last : Nat) : Nat := if t ≤ last then B else 0

theorem same_observed_offer (B t event last₁ last₂ : Nat)
    (ht : t ≤ event) (h₁ : event ≤ last₁) (h₂ : event ≤ last₂) :
    offered B t last₁ = offered B t last₂ := by
  simp [offered, Nat.le_trans ht h₁, Nat.le_trans ht h₂]






theorem physical_capacity (labels : List α) (past future : List Nat) (k B : Nat)
    (old : List β) (size age : β → Nat)
    (stock : List (List α) → α → Nat) (kept : World α → β → Nat)
    (current : World α → List Nat) (early late : World α → β → List Nat)
    (hCurrent : ∀ w ∈ worlds labels past (k+1) future,
      ∃ final, Closed (k+1) (total w.chosen (stock w.past)) (current w) final)
    (hElapsed : ∀ w ∈ worlds labels past (k+1) future, ∀ j ∈ old,
      (early w j).length = age j ∧ ∀ s ∈ early w j, s ≤ size j)
    (hOld : ∀ w ∈ worlds labels past (k+1) future, ∀ j ∈ old,
      ∃ final, Closed (size j) (kept w j) (late w j) final)
    (hCapacity : ∀ w ∈ worlds labels past (k+1) future,
      total w.live (stock w.past) + total old (kept w) ≤ B) :
    let W := worlds labels past (k+1) future
    (labels.length-past.sum) * total W (fun w => (current w).sum) +
      (k+1) * total old (fun j => total W (fun w => (early w j).sum + (late w j).sum) -
                                    W.length * (age j * size j)) ≤ (k+1) * (W.length * B) := by
  dsimp
  apply event_inventory _ _ _ _ _ _ _ _ _ _ _ _ hCapacity
  · apply whole_history_live
    intro w hw
    obtain ⟨final,h⟩ := hCurrent w hw
    have hn := no_future_arrivals h
    omega
  · intro w hw j hj
    obtain ⟨eq,rate⟩ := hElapsed w hw j hj
    have he := elapsed_slots (early w j) (size j) rate
    rw [eq] at he
    obtain ⟨final,h⟩ := hOld w hw j hj
    have hl := no_future_arrivals h
    omega

#print axioms physical_capacity


def assignment (w : World α) : List (List α) := w.past ++ w.chosen :: w.future



theorem split_history_sum (labels : List α) (past rest : List Nat)
    (f : List (List α) → Nat) :
    total (histories labels (past ++ rest)) (fun h => f h.1) =
      total (histories labels past) (fun h =>
        total (histories h.2 rest) (fun z => f (h.1 ++ z.1))) := by
  induction past generalizing labels f with
  | nil => simp [histories, total]
  | cons d ds ih =>
    simp only [List.cons_append, histories, total_flatMap]
    apply total_congr; intro b _
    simp only [total_map, List.cons_append]
    exact ih b.2 (fun t => f (b.1::t))

theorem canonical_sum (labels : List α) (past future : List Nat) (d : Nat)
    (f : List (List α) → Nat) :
    total (worlds labels past d future) (fun w => f (assignment w)) =
      total (histories labels (past ++ d::future)) (fun h => f h.1) := by
  rw [split_history_sum, worlds, total_flatMap]
  apply total_congr; intro h _
  simp only [histories, layer, total_flatMap, total_map, assignment]

theorem canonical_count (labels : List α) (past future : List Nat) (d : Nat) :
    (worlds labels past d future).length =
      (histories labels (past ++ d::future)).length := by
  simpa only [total_const, Nat.mul_one] using canonical_sum labels past future d (fun _ => 1)




structure Observation (labels : List α) (past future : List Nat) (k event B : Nat)
    (old : List Nat) (nPorts elapsed : Nat → Nat)
    (gain : List (List α) → Nat → Nat) where
  stock : List (List α) → α → Nat
  kept : World α → Nat → Nat
  current : World α → List Nat
  early : World α → Nat → List Nat
  late : World α → Nat → List Nat
  currentClosed : ∀ w ∈ worlds labels past (k+1) future,
      ∃ q, Closed (k+1) (total w.chosen (stock w.past)) (current w) q
  pastRate : ∀ w ∈ worlds labels past (k+1) future, ∀ j ∈ old,
      (early w j).length = elapsed j ∧ ∀ s ∈ early w j, s ≤ nPorts j
  pastClosed : ∀ w ∈ worlds labels past (k+1) future, ∀ j ∈ old,
      ∃ q, Closed (nPorts j) (kept w j) (late w j) q
  capacity : ∀ w ∈ worlds labels past (k+1) future,
      total w.live (stock w.past) + total old (kept w) ≤ B
  sameCurrent : ∀ w ∈ worlds labels past (k+1) future,
      (current w).sum = gain (assignment w) event
  samePast : ∀ w ∈ worlds labels past (k+1) future, ∀ j ∈ old,
      (early w j).sum + (late w j).sum = gain (assignment w) j





theorem canonical_inventory (labels : List α) (past future : List Nat)
    (k event B v : Nat) (old : List Nat) (nPorts elapsed : Nat → Nat)
    (gain : List (List α) → Nat → Nat)
    (hU : labels.length-past.sum = v*(k+1))
    (obs : Observation labels past future k event B old nPorts elapsed gain) :
    let H := histories labels (past ++ (k+1)::future)
    let D := H.length
    let f := fun j => total H (fun h => gain h.1 j)
    v * f event + total old (fun j => f j - D*(elapsed j * nPorts j)) ≤ D*B := by
  let W := worlds labels past (k+1) future
  let H := histories labels (past ++ (k+1)::future)
  have h := physical_capacity labels past future k B old nPorts elapsed
              obs.stock obs.kept obs.current obs.early obs.late
              obs.currentClosed obs.pastRate obs.pastClosed obs.capacity
  have hc : total W (fun w => (obs.current w).sum) =
            total H (fun p => gain p.1 event) := by
    calc
      _ = total W (fun w => gain (assignment w) event) :=
        total_congr _ _ _ obs.sameCurrent
      _ = _ := canonical_sum labels past future (k+1) (fun p => gain p event)
  have he (j : Nat) (hj : j ∈ old) :
            total W (fun w => (obs.early w j).sum + (obs.late w j).sum) =
            total H (fun p => gain p.1 j) := by
    calc
      _ = total W (fun w => gain (assignment w) j) :=
        total_congr _ _ _ (fun w hw => obs.samePast w hw j hj)
      _ = _ := canonical_sum labels past future (k+1) (fun p => gain p j)
  have hD : W.length = H.length := canonical_count _ _ _ _
  have hos : total old (fun j => total W (fun w => (obs.early w j).sum +
                  (obs.late w j).sum) - W.length * (elapsed j * nPorts j)) =
               total old (fun j => total H (fun p => gain p.1 j) -
                                    H.length * (elapsed j * nPorts j)) := by
    apply total_congr; intro j hj; rw [he j hj, hD]
  change (labels.length - past.sum) * total W (fun w => (obs.current w).sum) +
    (k+1) * total old (fun j => total W (fun w => (obs.early w j).sum +
                  (obs.late w j).sum) - W.length * (elapsed j * nPorts j)) ≤
      (k+1) * (W.length * B) at h
  rw [hU, hc, hos, hD, Nat.mul_comm v (k+1), Nat.mul_assoc, ← Nat.mul_add] at h
  exact Nat.le_of_mul_le_mul_left h (by omega)

#print axioms canonical_inventory

theorem choose_positive (n k : Nat) (h : k ≤ n) : 0 < choose n k := by
  induction n generalizing k with
  | zero =>
    have he : k = 0 := by omega
    subst k; decide
  | succ n ih =>
    cases k with
    | zero => simp [choose]
    | succ k =>
      have hp := ih k (by omega)
      simp only [choose]; omega

theorem nHist_positive (n : Nat) (groups : List Nat) (h : groups.sum ≤ n) :
    0 < nHist n groups := by
  induction groups generalizing n with
  | nil => simp [nHist]
  | cons d ds ih =>
    simp only [List.sum_cons] at h
    exact Nat.mul_pos (choose_positive n d (by omega)) (ih (n-d) (by omega))

theorem denominator_positive (labels : List α) (groups : List Nat)
    (h : groups.sum ≤ labels.length) : 0 < (histories labels groups).length := by
  rw [length_histories]; exact nHist_positive _ _ h

#print axioms denominator_positive

end HiddenStock

#print axioms HiddenStock.uniform_block_identity
#print axioms HiddenStock.conditional_live
#print axioms HiddenStock.event_inventory
