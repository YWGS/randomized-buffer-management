import PacketTrace
import OutcomeTable
import PhysicalOnline
import PhysicalOffline
import Cohorts




namespace SharedBuffer.PolicyBridge
open Geometry Packet MeasureTheory HiddenStock
open scoped BigOperators

noncomputable def experiment (P : Params) (x R h : ℝ) (hR : 0≤R)
    (hx : 0<x) (level : BufferLimit.Level 1 ((P.v:ℝ)/(P.v-1)) P.W x)
    (fits : P.K≤P.B) (p : PolicyLaw P.B (List.finRange P.K)) (comp : Competitive p R h) :
    Cohorts.Experiment P.n P.v P.W P.B P.K x R := by
  let ports := List.finRange P.K
  have hk : ports.length = P.K := List.length_finRange
  have distinct : ports.Nodup := List.nodup_finRange _
  let table := histories ports P.groups
  have nonempty : 0 < table.length := denominator_positive ports P.groups (by rw [hk]; exact P.groups_fit)
  let Index := Fin (table.length-1+1)
  let leaf := OutcomeTable.read table nonempty
  let block (i : Index) := stream (arrivals P.B P.date (leaf i).1) (P.date P.n+P.B)
  let gain s := blockGain ports (p.keep s) block
  let rule s (past : List Index) := shifted (p.keep s) (priorInputs block past)
  let inv s (past : List Index) := PhysicalOnline.inventory ports P.groups P.B P.date (rule s past)
  have admit s past : PhysicalOnline.Admissible P.B P.date (rule s past) :=
    shifted_admit p s (priorInputs block past) P.date
  have capacity s past : PhysicalOnline.Capacity ports P.B P.date (rule s past) :=
    shifted_capacity p s (priorInputs block past) P.date
  have gain_eq s past (i : Index) : gain s past i =
      PhysicalOnline.payoff ports P.groups P.B P.date (rule s past) (leaf i) := by
    unfold gain blockGain block PhysicalOnline.payoff PhysicalOnline.horizon
    rw [P.groupLength, count_cohort]
  have one i : CanSend P.B ports (fun _ => 0) (block i) (P.S+P.n*PhysicalOffline.quota P x) := by
    obtain ⟨Q, cap, init, step, _, score⟩ := PhysicalOffline.witness P x fits hx level ports hk distinct
      (leaf i) (OutcomeTable.read_mem table nonempty i)
    rw [← score]
    exact CanSend.of_run P.B ports _ Q _ cap init step
  refine { outcomes := table.length-1, Seed := p.Seed, meas := p.meas, mu := p.mu, prob := p.prob,
           gain := gain, inventory := inv, allowance := h+R*(P.B*ports.length),
           rows := ?_, split := ?_, integrable := ?_, compare_payoffs := ?_ }
  · exact fun s past i hi => PhysicalOnline.rowsGeometry P ports distinct hk (rule s past)
      (admit s past) (capacity s past) i hi
  · intro s past
    simp_rw [gain_eq]
    rw [OutcomeTable.mean_eq]
    exact PhysicalOnline.splitGeometry P ports distinct hk _ (admit s past) (capacity s past)
  · intro l
    change Integrable (fun s => Repeat.play (blockGain ports (p.keep s) block) [] l) p.mu
    simp only [play_counts]
    exact p.integrable_count _ _
  · intro l
    have path := repeatedOffline P.B ports block _ one l
    have bound := comp.prefix hR _ _ path
    change _ ≤ R*(∫ s, Repeat.play (blockGain ports (p.keep s) block) [] l ∂p.mu) + _
    simp only [play_counts, priorInputs]
    push_cast at bound
    rw [P.S_real, PhysicalOffline.quota_real P x fits hx.le] at bound
    exact bound





theorem sharpFromPolicies {R : ℝ} (hR : 0≤R)
    (uniform : ∀ B K : ℕ, 0<B → 0<K →
      ∃ (p : Packet.PolicyLaw B (List.finRange K)) (h : ℝ), Packet.Competitive p R h) :
    ∃ r : ℝ, 3/2 < r ∧ r<2 ∧ Ratio.entropy r=1 ∧
      (∀ t, 1<t → Ratio.entropy t=1 → t=r) ∧ r≤R := by
  apply Cohorts.sharpFromCohorts hR
  intro v hv W hW x hx level
  obtain ⟨b,c,hb,hc,hvc,spacing⟩ := Params.ofRationalChoice v hv W hW
  refine ⟨c,hc,Filter.Eventually.of_forall (fun j => ?_)⟩
  let P : Params := ⟨v,j+1,b,c,hv,by omega,hb,hc⟩
  have hspace : P.W = (W:ℝ) := by
    change (b:ℝ)*(P.w:ℝ)/c = _
    rw [P.w_real]
    exact spacing
  obtain ⟨p,allowance,comp⟩ := uniform P.B P.K P.B_pos P.K_pos
  have L : BufferLimit.Level 1 ((P.v:ℝ)/(P.v-1)) P.W x := hspace ▸ level
  have ex := experiment P x R allowance hR hx L (Params.fits hvc) p comp
  have hB : (P.B:ℝ) = c*((v:ℝ)*(v-1))^j := by simpa [P] using P.B_real
  have hK : (P.K:ℝ) = (v:ℝ)^(j+1) := P.K_real
  rw [hspace, hB, hK] at ex
  exact ⟨ex⟩

#print axioms experiment
#print axioms sharpFromPolicies
end SharedBuffer.PolicyBridge
