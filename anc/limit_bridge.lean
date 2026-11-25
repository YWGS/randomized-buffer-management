import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring




noncomputable section
namespace BufferLimit

def J0 (y : ℝ) := y * Real.log y - y + 1
def J1 (y : ℝ) := y * Real.log y
def g (q : ℝ) := q * Real.log q - (q-1) * Real.log (q-1)

def gridStock (b d y : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => gridStock b d y n + d * max (y-b^(n+1)) 0

def lin (b d y : ℝ) (m : ℕ) := (m:ℝ)*d*y + 1-b^m

lemma upper_lin {b d y : ℝ} (hb : 1 < b) (hd : d = 1-b⁻¹) (hy : 0 < y)
    (m : ℕ) : lin b d y m ≤ J0 y := by
  have hb0 : 0 < b := by linarith
  have ht : 0 < b^m := pow_pos hb0 m
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hy ht)
  rw [Real.log_div hy.ne' ht.ne', Real.log_pow, inv_div] at hlog
  have hr := (mul_le_mul_of_nonneg_left hlog hy.le)
  have hyc : y * ((b^m)/y) = b^m := by field_simp
  have hB := Real.one_sub_inv_le_log_of_pos hb0
  rw [← hd] at hB
  have hh := mul_le_mul_of_nonneg_left hB (mul_nonneg (Nat.cast_nonneg m) hy.le)
  unfold lin J0
  nlinarith only [hr, hyc, hh]

lemma lower_lin {b d y : ℝ} (hb : 1 < b) (hd : d=1-b⁻¹) (hy : 0 < y)
    {m : ℕ} (hm : b^m ≤ y) (hn : y ≤ b^(m+1)) :
    (1-d)*J1 y ≤ y-1+lin b d y m := by
  have hb0 : 0 < b := by linarith
  have ht : 0 < b^m := pow_pos hb0 m
  let a := y/(b^m)
  have ha : 1 ≤ a := (one_le_div₀ ht).mpr hm
  have hab : a ≤ b := by
    apply (div_le_iff₀ ht).mpr
    rw [pow_succ] at hn
    linarith
  have ha0 : 0 < a := by linarith
  have hAL := Real.log_nonneg ha
  have hA := Real.log_le_sub_one_of_pos ha0
  have hB := Real.log_le_sub_one_of_pos hb0
  have hLog : Real.log y = (m:ℝ)*Real.log b+Real.log a := by
    dsimp [a]
    rw [Real.log_div hy.ne' ht.ne', Real.log_pow]
    ring
  have hAT : a*b^m=y := by dsimp [a]; field_simp
  have h1 : a * Real.log a ≤ b * (a-1) :=
    le_trans (mul_le_mul_of_nonneg_right hab hAL)
      (mul_le_mul_of_nonneg_left hA hb0.le)
  have h2 := mul_le_mul_of_nonneg_left h1 ht.le
  have h3 := mul_le_mul_of_nonneg_left hB (mul_nonneg (Nat.cast_nonneg m) hy.le)
  have hRA : y * Real.log a ≤ b*(y-b^m) := by
    calc
      _ = b^m*(a*Real.log a) := by rw [← hAT]; ring
      _ ≤ _ := h2
      _ = _ := by rw [← hAT]; ring
  unfold J1 lin
  rw [hLog, hd]
  apply (mul_le_mul_iff_of_pos_left hb0).mp
  field_simp
  nlinarith only [h3, hRA]

lemma prefix_active {b d y : ℝ} (hb : 1 < b) (hd : d=1-b⁻¹) :
    ∀ m : ℕ, b^m ≤ y → gridStock b d y m = lin b d y m := by
  have hb0 : 0 < b := by linarith
  intro m
  induction m with
  | zero => simp [gridStock, lin]
  | succ m ih =>
    intro h
    have hold : b^m ≤ y := le_trans (pow_le_pow_right₀ hb.le (Nat.le_succ m)) h
    rw [gridStock, ih hold, max_eq_left (sub_nonneg.mpr h)]
    unfold lin
    rw [Nat.cast_succ, pow_succ, hd]
    field_simp
    ring

lemma prefix_tail {b d y : ℝ} (hb : 1 < b) {m : ℕ} (hn : y ≤ b^(m+1)) :
    ∀ j : ℕ, gridStock b d y (m+j) = gridStock b d y m := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hh : y ≤ b^(m+j+1) := le_trans hn (pow_le_pow_right₀ hb.le (by omega))
    rw [← Nat.add_assoc, gridStock, max_eq_right (sub_nonpos.mpr hh), mul_zero, add_zero, ih]

lemma prefix_le {b d y : ℝ} (hb : 1 < b) (hd : d = 1-b⁻¹) (hy : 1 ≤ y)
    (n : ℕ) : gridStock b d y n ≤ J0 y := by
  obtain ⟨m,hm,hn⟩ := exists_nat_pow_near hy hb
  have hy0 : 0 < y := by linarith
  by_cases h : n ≤ m
  · have hny : b^n ≤ y := le_trans (pow_le_pow_right₀ hb.le h) hm
    rw [prefix_active hb hd n hny]
    exact upper_lin hb hd hy0 n
  · have hh : m+(n-m)=n := by omega
    rw [← hh, prefix_tail hb hn.le, prefix_active hb hd m hm]
    exact upper_lin hb hd hy0 m

lemma some_prefix_ge {b d y : ℝ} (hb : 1 < b) (hd : d=1-b⁻¹) (hy : 1 ≤ y) :
    ∃ m : ℕ, (1-d)*J1 y ≤ y-1+gridStock b d y m := by
  obtain ⟨m,hm,hn⟩ := exists_nat_pow_near hy hb
  refine ⟨m, ?_⟩
  rw [prefix_active hb hd m hm]
  exact lower_lin hb hd (by linarith) hm hn.le



def stock (b c x : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => stock b c x n + max (x-c*(b^(n+1)-1)) 0

def Feasible (a b c x : ℝ) : Prop := ∀ n : ℕ, a*x + stock b c x n ≤ 1

lemma scale_stock {H c d : ℝ} (hc : 0 ≤ c) (hHd : H*c=d)
    (b y : ℝ) : ∀ n : ℕ, H*stock b c (c*(y-1)) n = gridStock b d y n := by
  intro n
  induction n with
  | zero => simp [stock, gridStock]
  | succ n ih =>
    simp only [stock, gridStock, mul_add, ih, add_right_inj]
    have hx : c*(y-1)-c*(b^(n+1)-1) = c*(y-b^(n+1)) := by ring
    rw [hx, ← mul_zero c, ← mul_max_of_nonneg _ _ hc, ← mul_assoc, hHd, mul_zero]

lemma stock_mono {x y : ℝ} (h : x ≤ y) (b c : ℝ) :
    ∀ n : ℕ, stock b c x n ≤ stock b c y n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    apply add_le_add ih
    exact max_le_max_right _ (sub_le_sub_right h _)

lemma feasible_down {a b c x y : ℝ} (ha : 0 ≤ a) (h : x ≤ y)
    (hf : Feasible a b c y) : Feasible a b c x := by
  intro n
  exact (add_le_add (mul_le_mul_of_nonneg_left h ha) (stock_mono h b c n)).trans (hf n)

lemma parameters {u z : ℝ} (hu : 1 ≤ u) (gap : J0 u < J1 z) :
    ∃ (H : ℚ) (v : ℕ), 0 < H ∧ 3 ≤ v ∧
      J0 u+(u-1)/v < (H:ℝ) ∧ (H:ℝ) < (1-1/(v:ℝ))*J1 z := by
  have hJ : 0 ≤ J0 u := by
    have t := upper_lin (b:=2) (d:=1-(2:ℝ)⁻¹) (by norm_num) rfl
      (show 0 < u by linarith) 0
    simpa [lin] using t
  obtain ⟨H,hlo,hhi⟩ := exists_rat_btwn gap
  have hH : (0:ℝ) < H := lt_of_le_of_lt hJ hlo
  obtain ⟨v,hv⟩ := exists_nat_gt (max (3:ℝ)
    (max ((u-1)/(H-J0 u)) (J1 z/(J1 z-H))))
  have h3 : (3:ℝ) < v := lt_of_le_of_lt (le_max_left _ _) hv
  have hv0 : (0:ℝ) < v := by linarith
  have hvl : (u-1)/(H-J0 u) < v := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hv
  have hvr : J1 z/(J1 z-H) < v := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_right _ _)) hv
  have hl := (div_lt_iff₀ (sub_pos.mpr hlo)).mp hvl
  have hr := (div_lt_iff₀ (sub_pos.mpr hhi)).mp hvr
  refine ⟨H,v,by exact_mod_cast hH,?_,?_,?_⟩
  · have hv3 : 3 < v := by exact_mod_cast h3
    omega
  · have hsmall : (u-1)/v < (H:ℝ)-J0 u :=
      (div_lt_iff₀ hv0).mpr (by linarith)
    linarith
  · apply (mul_lt_mul_iff_of_pos_right hv0).mp
    have hh : (1-1/(v:ℝ))*J1 z*v = ((v:ℝ)-1)*J1 z := by field_simp
    rw [hh]
    linarith



def Level (a b c x : ℝ) := Feasible a b c x ∧ ∃ n : ℕ, a*x+stock b c x n=1

lemma level_greatest {a b c x : ℝ} (ha : 0 < a) (h : Level a b c x)
    {y : ℝ} (hy : Feasible a b c y) : y ≤ x := by
  refine le_of_not_gt fun hlt => ?_
  obtain ⟨n,hn⟩ := h.2
  have hh := stock_mono hlt.le b c n
  have hs := mul_lt_mul_of_pos_left hlt ha
  linarith [hy n]

lemma stock_zero {b c : ℝ} (hb : 1 ≤ b) (hc : 0 ≤ c) : ∀ n : ℕ, stock b c 0 n=0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    have hh : 0 ≤ c*(b^(n+1)-1) := mul_nonneg hc (sub_nonneg.mpr (one_le_pow₀ hb))
    rw [stock, ih, max_eq_right (by linarith : 0-c*(b^(n+1)-1) ≤ 0), add_zero]

lemma stock_increasing (b c x : ℝ) : Monotone (stock b c x) := by
  apply monotone_nat_of_le_succ
  intro n
  exact le_add_of_nonneg_right (le_max_right _ _)

lemma stock_tail {b c x : ℝ} (hb : 1 ≤ b) (hc : 0 ≤ c)
    {m : ℕ} (bound : x ≤ c*(b^(m+1)-1)) :
    ∀ j : ℕ, stock b c x (m+j) = stock b c x m := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have ble : b^(m+1) ≤ b^(m+j+1) := pow_le_pow_right₀ hb (by omega)
    have h := bound.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right ble _) hc)
    rw [← Nat.add_assoc, stock, max_eq_right (sub_nonpos.mpr h), add_zero, ih]

lemma stock_continuous (b c : ℝ) : ∀ n : ℕ, Continuous (fun x => stock b c x n) := by
  intro n
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact ih.add ((continuous_id.sub continuous_const).max continuous_const)

theorem exists_unique_level {a b c : ℝ} (ha : 1 ≤ a) (hb : 1 < b) (hc : 0 < c) :
    ∃! x : ℝ, 0 < x ∧ Level a b c x := by
  have hlim : 1 ≤ 1+1/c := by linarith [one_div_pos.mpr hc]
  obtain ⟨m,_,hm⟩ := exists_nat_pow_near hlim hb
  have hm1 : 1 ≤ c*(b^(m+1)-1) := by
    have hs : 1/c < b^(m+1)-1 := by linarith
    have hh := (div_lt_iff₀ hc).mp hs
    linarith
  let f : ℝ → ℝ := fun x => a*x+stock b c x m
  have hcont : Continuous f := (continuous_const.mul continuous_id).add (stock_continuous b c m)
  have f0 : f 0=0 := by dsimp [f]; rw [stock_zero hb.le hc.le]; ring
  have f1 : 1 ≤ f 1 := by
    have hh := stock_increasing b c 1 (Nat.zero_le m)
    change 0 ≤ stock b c 1 m at hh
    dsimp [f]; linarith
  have htarget : (1:ℝ) ∈ Set.Icc (f 0) (f 1) := ⟨by rw [f0]; norm_num, f1⟩
  obtain ⟨x,⟨hx0,hx1⟩,hfx⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1)
    hcont.continuousOn htarget
  have hxpos : 0 < x := by
    refine lt_of_le_of_ne hx0 fun eq => ?_
    rw [←eq, f0] at hfx
    norm_num at hfx
  have hxf : Feasible a b c x := by
    intro n
    have hn : stock b c x n ≤ stock b c x m := by
      by_cases h : n ≤ m
      · exact stock_increasing b c x h
      · have he : m+(n-m)=n := by omega
        rw [← he, stock_tail hb.le hc.le (hx1.trans hm1)]
    change a*x+stock b c x m=1 at hfx
    linarith
  have lvl : Level a b c x := ⟨hxf, m, hfx⟩
  refine ⟨x,⟨hxpos,lvl⟩,?_⟩
  intro y hy
  have hapos : 0 < a := by linarith
  exact le_antisymm (level_greatest hapos lvl hy.2.1) (level_greatest hapos hy.2 lvl.1)



theorem active_level {a b c x : ℝ} (hb : 1 < b) (hc : 0 < c) (hx : 0 < x)
    (L : Level a b c x) :
    ∃ m : ℕ, (a+m)*x = 1+∑ j ∈ Finset.range m, c*(b^(j+1)-1) ∧
      (∀ j < m, c*(b^(j+1)-1)<x) ∧ x ≤ c*(b^(m+1)-1) := by
  classical
  have hlim : 1 ≤ 1+x/c := by linarith [div_pos hx hc]
  obtain ⟨t,_,ht⟩ := exists_nat_pow_near hlim hb
  have hcross : ∃ k : ℕ, x ≤ c*(b^(k+1)-1) := by
    refine ⟨t,?_⟩
    have hh := (div_lt_iff₀ hc).mp (show x/c < b^(t+1)-1 by linarith)
    linarith
  let m := Nat.find hcross
  have hstop : x ≤ c*(b^(m+1)-1) := Nat.find_spec hcross
  have hbefore (j : ℕ) (hj : j<m) : c*(b^(j+1)-1)<x :=
    lt_of_not_ge (Nat.find_min hcross hj)
  obtain ⟨N,hN⟩ := L.2
  have hcap : a*x+stock b c x m=1 := by
    have hle := L.1 m
    by_cases h : N ≤ m
    · have hh := stock_increasing b c x h
      linarith
    · have he : m+(N-m)=N := by omega
      rw [← he, stock_tail hb.le hc.le hstop] at hN
      exact hN
  have hs : ∀ k ≤ m, stock b c x k =
      (k:ℝ)*x-∑ j ∈ Finset.range k, c*(b^(j+1)-1) := by
    intro k
    induction k with
    | zero => simp [stock]
    | succ k ih =>
      intro hk
      have hkm : k<m := by omega
      rw [stock, ih hkm.le, max_eq_left (sub_nonneg.mpr (hbefore k hkm).le),
        Finset.sum_range_succ, Nat.cast_succ]
      ring
  refine ⟨m,?_,hbefore,hstop⟩
  rw [hs m (le_refl _)] at hcap
  linarith




def FixedArityBound (R : ℝ) : Prop :=
  ∀ (v : ℕ), 3 ≤ v → ∀ (c : ℚ), 0 < c →
    ∃ x₀ x₁ : ℝ,
      (∀ x : ℝ, 0 ≤ x → Feasible 1 (v/((v:ℝ)-1)) c x → x ≤ x₀) ∧
      Feasible v (v/((v:ℝ)-1)) c x₁ ∧ 0 ≤ x₁ ∧
      ((c:ℝ)+x₀)/((c:ℝ)+x₁) ≤ R



def FixedLevelBound (R : ℝ) : Prop :=
  ∀ (v : ℕ), 3 ≤ v → ∀ (c : ℚ), 0 < c → ∀ x₀ x₁ : ℝ,
    0 < x₀ → Level 1 (v/((v:ℝ)-1)) c x₀ →
    0 < x₁ → Level v (v/((v:ℝ)-1)) c x₁ →
    ((c:ℝ)+x₀)/((c:ℝ)+x₁) ≤ R

theorem fixed_of_levels {R : ℝ} (fixed : FixedLevelBound R) : FixedArityBound R := by
  intro v hv c hc
  have hv3 : (3:ℝ) ≤ v := by exact_mod_cast hv
  have hv1 : 0 < (v:ℝ)-1 := by linarith
  have hb : 1 < (v:ℝ)/((v:ℝ)-1) := (lt_div_iff₀ hv1).mpr (by linarith)
  have hc0 : (0:ℝ) < c := by exact_mod_cast hc
  obtain ⟨x₀,⟨h0,level0⟩,_⟩ := exists_unique_level (by norm_num : (1:ℝ) ≤ 1) hb hc0
  obtain ⟨x₁,⟨h1,level1⟩,_⟩ := exists_unique_level (by linarith : (1:ℝ) ≤ v) hb hc0
  refine ⟨x₀,x₁,(fun _ _ hf => level_greatest (by norm_num) level0 hf),level1.1,h1.le,?_⟩
  exact fixed v hv c hc _ _ h0 level0 h1 level1

theorem ratio_of_gap {R u z : ℝ} (fixed : FixedArityBound R)
    (hu : 1 ≤ u) (hz : 1 ≤ z) (gap : J0 u < J1 z) : u/z ≤ R := by
  obtain ⟨H,v,hHrat,hv3,hlo,hhi⟩ := parameters hu gap
  have hH : (0:ℝ) < H := by exact_mod_cast hHrat
  have hv3' : (3:ℝ) ≤ v := by exact_mod_cast hv3
  have hv0 : (0:ℝ) < v := by linarith
  have hv1 : 0 < (v:ℝ)-1 := by linarith
  let b : ℝ := v/((v:ℝ)-1)
  let d : ℝ := 1/v
  let c : ℚ := 1/((v:ℚ)*H)
  have hvRat : (0:ℚ) < v := by exact_mod_cast hv0
  have hcr : 0 < c := by dsimp [c]; positivity
  have hc : (0:ℝ) < c := by exact_mod_cast hcr
  have hb : 1 < b := (lt_div_iff₀ hv1).mpr (by linarith)
  have hd : d=1-b⁻¹ := by dsimp [d,b]; rw [inv_div]; field_simp
  have hHd : (H:ℝ)*c=d := by dsimp [c,d]; push_cast; field_simp; ring
  obtain ⟨x₀,x₁,off,onl,hx1,hR⟩ := fixed v hv3 c hcr
  have hoff : Feasible 1 b c (c*(u-1)) := by
    intro n
    apply (mul_le_mul_iff_of_pos_left hH).mp
    rw [mul_one, mul_add, scale_stock hc.le hHd, one_mul, ← mul_assoc, hHd]
    have hsum := prefix_le hb hd hu n
    dsimp [d]
    have hdiv : 1/(v:ℝ)*(u-1) = (u-1)/v := by ring
    linarith
  have hon : ¬Feasible v b c (c*(z-1)) := by
    intro hfit
    obtain ⟨m,hm⟩ := some_prefix_ge hb hd hz
    have hcap := mul_le_mul_of_nonneg_left (hfit m) hH.le
    rw [mul_one, mul_add, scale_stock hc.le hHd] at hcap
    have hre : (H:ℝ)*((v:ℝ)*(c*(z-1))) = z-1 := by
      calc
        _ = ((v:ℝ)*((H:ℝ)*c))*(z-1) := by ring
        _ = z-1 := by rw [hHd]; dsimp [d]; field_simp
    rw [hre] at hcap
    dsimp [d] at hm
    linarith
  have hxl := off _ (mul_nonneg hc.le (sub_nonneg.mpr hu)) hoff
  have hxr : x₁ < c*(z-1) := by
    exact lt_of_not_ge fun hbad => hon (feasible_down hv0.le hbad onl)
  have hz0 : 0 < z := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hratio : u/z ≤ ((c:ℝ)+x₀)/((c:ℝ)+x₁) := by
    apply (div_le_div_iff₀ hz0 (by linarith)).mpr
    have hr := mul_le_mul_of_nonneg_left hxr.le hu0
    have hl := mul_le_mul_of_nonneg_right hxl hz0.le
    nlinarith only [hr,hl]
  exact hratio.trans hR



theorem sharp_from_stationary_ratio {R q : ℝ} (fixed : FixedArityBound R)
    (hq : 1 < q) (h2 : q < 2) (hg : g q < 1) : q ≤ R := by
  let z : ℝ := 1/(q-1)
  let u : ℝ := z+1
  have hp : 0 < q-1 := by linarith
  have hq0 : 0 < q := by linarith
  have hz0 : 0 < z := by dsimp [z]; positivity
  have hz : 1 ≤ z := (one_le_div₀ hp).mpr (by linarith)
  have hu : 1 ≤ u := by dsimp [u]; linarith
  have hzu : q*z = u := by dsimp [u,z]; field_simp
  have hzlog : Real.log z = -Real.log (q-1) := by
    dsimp [z]; rw [Real.log_div one_ne_zero hp.ne',Real.log_one]; ring
  have hulog : Real.log u = Real.log q + Real.log z := by
    rw [← hzu, Real.log_mul hq0.ne' hz0.ne']
  have heq : J1 z-J0 u = z*(1-g q) := by
    unfold J1 J0 g
    rw [hulog,hzlog, ← hzu]
    calc
      _ = z*(1-(q*Real.log q-(q-1)*Real.log (q-1))) + (q*z-z-1) := by ring
      _ = _ := by dsimp [u] at hzu; linarith
  have hgap : J0 u < J1 z := by
    have hh := mul_pos hz0 (sub_pos.mpr hg)
    linarith
  have rat := ratio_of_gap fixed hu hz hgap
  have hquot : u/z=q := (div_eq_iff hz0.ne').mpr hzu.symm
  rwa [hquot] at rat

theorem sharp_from_fixed_levels {R q : ℝ} (fixed : FixedLevelBound R)
    (hq : 1 < q) (h2 : q < 2) (hg : g q < 1) : q ≤ R :=
  sharp_from_stationary_ratio (fixed_of_levels fixed) hq h2 hg

end BufferLimit

#print axioms BufferLimit.active_level
#print axioms BufferLimit.exists_unique_level
#print axioms BufferLimit.sharp_from_fixed_levels
#print axioms BufferLimit.sharp_from_stationary_ratio
