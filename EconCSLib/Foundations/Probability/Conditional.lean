import EconCSLib.Foundations.Probability.FiniteExpectation
import Mathlib.Topology.Instances.Real.Lemmas

namespace EconCSLib

/-- A convenient algebra lemma for positivity after division by a positive real. -/
theorem zero_lt_div_iff_pos_right {a b : ℝ} (hb : 0 < b) :
    0 < a / b ↔ 0 < a := by
  constructor
  · intro hdiv
    have hprod : 0 < (a / b) * b := mul_pos hdiv hb
    have hcancel : (a / b) * b = a := by
      field_simp [hb.ne']
    calc
      0 < (a / b) * b := hprod
      _ = a := hcancel
  · intro ha
    by_contra hnot
    have hnonpos : a / b ≤ 0 := le_of_not_gt hnot
    have hprod_nonpos : (a / b) * b ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg hnonpos (le_of_lt hb)
    have hcancel : (a / b) * b = a := by
      field_simp [hb.ne']
    have : a ≤ 0 := by
      calc
        a = (a / b) * b := hcancel.symm
        _ ≤ 0 := hprod_nonpos
    linarith

/-- Expectation of `f` restricted to an event `p`, implemented via an indicator. -/
noncomputable def pmfIndicatorExp {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ) : ℝ :=
  pmfExp μ (fun a => if p a then f a else 0)

theorem pmfIndicatorExp_eq_zero_of_pmfProb_eq_zero {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (hprob : pmfProb μ p = 0) :
    pmfIndicatorExp μ p f = 0 := by
  unfold pmfIndicatorExp pmfExp
  have hsum_nonneg : ∀ a : α, 0 ≤ (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
    intro a
    exact mul_nonneg ENNReal.toReal_nonneg (by by_cases hp : p a <;> simp [hp])
  have hsum_nonneg' : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ (μ a).toReal * (if p a then (1 : ℝ) else 0) := by
    intro a _
    exact hsum_nonneg a
  have hprob' : ∑ b : α, (μ b).toReal * (if p b then (1 : ℝ) else 0) = 0 := by
    simpa [pmfProb, pmfExp] using hprob
  have hmass_zero : ∀ a : α, p a → (μ a).toReal = 0 := by
    intro a ha
    have hle : (μ a).toReal ≤ 0 := by
      have hsingle : (μ a).toReal * (if p a then (1 : ℝ) else 0) ≤
          ∑ b : α, (μ b).toReal * (if p b then (1 : ℝ) else 0) := by
        exact Finset.single_le_sum hsum_nonneg' (Finset.mem_univ a)
      have hsingle' : (μ a).toReal * (if p a then (1 : ℝ) else 0) ≤ 0 := by
        rwa [hprob'] at hsingle
      simpa [ha] using hsingle'
    exact le_antisymm hle ENNReal.toReal_nonneg
  have hterm : ∀ a : α, (μ a).toReal * (if p a then f a else 0) = 0 := by
    intro a
    by_cases ha : p a
    · simp [ha, hmass_zero a ha]
    · simp [ha]
  calc
    ∑ a : α, (μ a).toReal * (if p a then f a else 0)
        = ∑ a : α, (0 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          exact hterm a
    _ = 0 := by simp

@[simp] theorem pmfIndicatorExp_const_one {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    pmfIndicatorExp μ p (fun _ => 1) = pmfProb μ p := by
  rfl

/-- Conditional expectation of `f` on event `p`, with value `0` when `p` has zero probability. -/
noncomputable def pmfConditionalExp {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ) : ℝ :=
  let q := pmfProb μ p
  if _h : q = 0 then 0 else pmfIndicatorExp μ p f / q

@[simp] theorem pmfConditionalExp_of_prob_zero {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (h : pmfProb μ p = 0) :
    pmfConditionalExp μ p f = 0 := by
  simp [pmfConditionalExp, h]

theorem pmfConditionalExp_eq_div_of_pos {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (h : 0 < pmfProb μ p) :
    pmfConditionalExp μ p f = pmfIndicatorExp μ p f / pmfProb μ p := by
  simp [pmfConditionalExp, h.ne']

/-- Positive-probability conditional expectation with the denominator cleared. -/
theorem pmfConditionalExp_mul_prob_eq_indicatorExp_of_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (h : 0 < pmfProb μ p) :
    pmfConditionalExp μ p f * pmfProb μ p = pmfIndicatorExp μ p f := by
  rw [pmfConditionalExp_eq_div_of_pos μ p f h]
  field_simp [h.ne']

theorem pmfIndicatorExp_nonneg_of_nonneg
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (hf : ∀ a, p a → 0 ≤ f a) :
    0 ≤ pmfIndicatorExp μ p f := by
  unfold pmfIndicatorExp pmfExp
  refine Finset.sum_nonneg ?_
  intro a _
  refine mul_nonneg ENNReal.toReal_nonneg ?_
  by_cases hp : p a
  · simpa [hp] using hf a hp
  · simp [hp]

/-- Indicator expectations over an event inherit a pointwise upper bound. -/
theorem pmfIndicatorExp_le_prob_mul_of_forall_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    {c : ℝ} (hf : ∀ a, p a → f a ≤ c) :
    pmfIndicatorExp μ p f ≤ pmfProb μ p * c := by
  unfold pmfIndicatorExp pmfProb pmfExp
  calc
    (∑ a : α, (μ a).toReal * (if p a then f a else 0))
        ≤ ∑ a : α, (μ a).toReal * (if p a then c else 0) := by
            refine Finset.sum_le_sum ?_
            intro a _
            by_cases hp : p a
            · simpa [hp] using
                mul_le_mul_of_nonneg_left (hf a hp) ENNReal.toReal_nonneg
            · simp [hp]
    _ = (∑ a : α, (μ a).toReal * (if p a then (1 : ℝ) else 0)) * c := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases hp : p a <;> simp [hp]

/-- The conditional expectation of a constant-one value is one on positive events. -/
theorem pmfConditionalExp_const_one_eq_one_of_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    (h : 0 < pmfProb μ p) :
    pmfConditionalExp μ p (fun _ => (1 : ℝ)) = 1 := by
  rw [pmfConditionalExp_eq_div_of_pos μ p (fun _ => (1 : ℝ)) h]
  simp [h.ne']

/-- Conditional expectations preserve nonnegativity on positive events. -/
theorem pmfConditionalExp_nonneg_of_nonneg
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (hf : ∀ a, p a → 0 ≤ f a) :
    0 ≤ pmfConditionalExp μ p f := by
  by_cases hzero : pmfProb μ p = 0
  · simpa [pmfConditionalExp_of_prob_zero μ p f hzero]
  · have hpos : 0 < pmfProb μ p :=
      lt_of_le_of_ne (pmfProb_nonneg μ p) (by simpa [eq_comm] using hzero)
    rw [pmfConditionalExp_eq_div_of_pos μ p f hpos]
    exact div_nonneg (pmfIndicatorExp_nonneg_of_nonneg μ p f hf) (le_of_lt hpos)

/-- Conditional expectations preserve upper bounds on positive events. -/
theorem pmfConditionalExp_le_of_forall_le_of_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (h : 0 < pmfProb μ p) {c : ℝ}
    (hf : ∀ a, p a → f a ≤ c) :
    pmfConditionalExp μ p f ≤ c := by
  rw [pmfConditionalExp_eq_div_of_pos μ p f h]
  have hle := pmfIndicatorExp_le_prob_mul_of_forall_le μ p f hf
  rw [div_le_iff₀ h]
  calc
    pmfIndicatorExp μ p f ≤ pmfProb μ p * c := hle
    _ = c * pmfProb μ p := by ring

/-- Conditional expectations preserve interval bounds on positive events. -/
theorem pmfConditionalExp_mem_Icc_of_mem_Icc_of_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (h : 0 < pmfProb μ p) {a b : ℝ}
    (hf : ∀ x, p x → f x ∈ Set.Icc a b) :
    pmfConditionalExp μ p f ∈ Set.Icc a b := by
  constructor
  · have hneg :
        pmfConditionalExp μ p (fun x => -f x) ≤ -a :=
      pmfConditionalExp_le_of_forall_le_of_pos μ p (fun x => -f x) h
        (fun x hx => neg_le_neg (hf x hx).1)
    rw [pmfConditionalExp_eq_div_of_pos μ p f h]
    rw [pmfConditionalExp_eq_div_of_pos μ p (fun x => -f x) h] at hneg
    have hind_neg :
        pmfIndicatorExp μ p (fun x => -f x) = -pmfIndicatorExp μ p f := by
      unfold pmfIndicatorExp pmfExp
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro x _
      by_cases hx : p x <;> simp [hx]
    rw [hind_neg, neg_div] at hneg
    linarith
  · exact pmfConditionalExp_le_of_forall_le_of_pos μ p f h
      (fun x hx => (hf x hx).2)

theorem pmfConditionalExp_pos_iff {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (h : 0 < pmfProb μ p) :
    0 < pmfConditionalExp μ p f ↔ 0 < pmfIndicatorExp μ p f := by
  rw [pmfConditionalExp_eq_div_of_pos (μ := μ) (p := p) (f := f) h]
  exact zero_lt_div_iff_pos_right h

/-- Conditional probability of event `q` given event `p` under a finite PMF. -/
noncomputable def pmfConditionalProb {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] : ℝ :=
  pmfConditionalExp μ p (fun a => if q a then 1 else 0)

/-- The indicator expectation of `q` restricted to `p` is `Pr[p and q]`. -/
theorem pmfIndicatorExp_event_eq_inter_prob
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    pmfIndicatorExp μ p (fun a => if q a then 1 else 0) =
      pmfProb μ (fun a => p a ∧ q a) := by
  classical
  unfold pmfIndicatorExp pmfProb
  refine pmfExp_congr μ ?_
  intro a
  by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq]

/-- Positive-probability conditional event formula for finite PMFs. -/
theorem pmfConditionalProb_eq_inter_div_of_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (h : 0 < pmfProb μ p) :
    pmfConditionalProb μ p q =
      pmfProb μ (fun a => p a ∧ q a) / pmfProb μ p := by
  unfold pmfConditionalProb
  rw [pmfConditionalExp_eq_div_of_pos μ p (fun a => if q a then 1 else 0) h]
  rw [pmfIndicatorExp_event_eq_inter_prob]

/--
If every fiber of a finite map inside a conditioning event has the same
positive cardinality, then the conditional pushforward of the uniform law is
the uniform law on the codomain, stated as equality of event probabilities.
-/
theorem pmfConditionalProb_uniformPMF_comp_eq_of_constant_conditional_fiber_card
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (condition : α → Prop) [DecidablePred condition]
    (f : α → β) (fiberCard : ℕ) (hfiber_pos : 0 < fiberCard)
    (hfiber : ∀ b : β,
      ((Finset.univ : Finset α).filter
        (fun a => condition a ∧ f a = b)).card = fiberCard)
    (p : β → Prop) [DecidablePred p] :
    pmfConditionalProb (uniformPMF α) condition (fun a => p (f a)) =
      pmfProb (uniformPMF β) p := by
  classical
  let sourceEvent : Finset α :=
    (Finset.univ : Finset α).filter fun a => condition a ∧ p (f a)
  let conditionSet : Finset α :=
    (Finset.univ : Finset α).filter fun a => condition a
  let targetEvent : Finset β :=
    (Finset.univ : Finset β).filter fun b => p b
  have hsource_card :
      sourceEvent.card = fiberCard * targetEvent.card := by
    have hmaps : ∀ a ∈ sourceEvent, f a ∈ targetEvent := by
      intro a ha
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.2⟩
    calc
      sourceEvent.card =
          ∑ b ∈ targetEvent,
            ((sourceEvent.filter fun a => f a = b).card) := by
            exact Finset.card_eq_sum_card_fiberwise hmaps
      _ = ∑ _b ∈ targetEvent, fiberCard := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            have hp : p b := (Finset.mem_filter.mp hb).2
            have hfiber_event :
                sourceEvent.filter (fun a => f a = b) =
                  (Finset.univ : Finset α).filter
                    (fun a => condition a ∧ f a = b) := by
              ext a
              by_cases hfb : f a = b
              · simp [sourceEvent, hfb, hp]
              · simp [sourceEvent, hfb]
            rw [hfiber_event, hfiber b]
      _ = fiberCard * targetEvent.card := by
            rw [Finset.sum_const, nsmul_eq_mul]
            exact Nat.mul_comm targetEvent.card fiberCard
  have hcondition_card :
      conditionSet.card = fiberCard * Fintype.card β := by
    have hmaps : ∀ a ∈ conditionSet, f a ∈ (Finset.univ : Finset β) := by
      intro a _ha
      exact Finset.mem_univ _
    calc
      conditionSet.card =
          ∑ b : β,
            ((conditionSet.filter fun a => f a = b).card) := by
            simpa using
              (Finset.card_eq_sum_card_fiberwise
                (s := conditionSet)
                (t := (Finset.univ : Finset β))
                (f := f) hmaps)
      _ = ∑ _b : β, fiberCard := by
            refine Finset.sum_congr rfl ?_
            intro b _hb
            have hfiber_event :
                conditionSet.filter (fun a => f a = b) =
                  (Finset.univ : Finset α).filter
                    (fun a => condition a ∧ f a = b) := by
              ext a
              simp [conditionSet]
            rw [hfiber_event, hfiber b]
      _ = fiberCard * Fintype.card β := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            exact Nat.mul_comm (Fintype.card β) fiberCard
  have hcondition_card_pos : 0 < conditionSet.card := by
    rw [hcondition_card]
    exact Nat.mul_pos hfiber_pos (Fintype.card_pos_iff.mpr ‹Nonempty β›)
  have hcondition_prob :
      pmfProb (uniformPMF α) condition =
        (conditionSet.card : ℝ) / (Fintype.card α : ℝ) := by
    simpa [conditionSet] using
      (pmfProb_uniformPMF_finset (α := α) conditionSet)
  have hcondition_prob_pos :
      0 < pmfProb (uniformPMF α) condition := by
    rw [hcondition_prob]
    exact div_pos
      (by exact_mod_cast hcondition_card_pos)
      (by exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›))
  have hsource_prob :
      pmfProb (uniformPMF α) (fun a => condition a ∧ p (f a)) =
        (sourceEvent.card : ℝ) / (Fintype.card α : ℝ) := by
    simpa [sourceEvent] using
      (pmfProb_uniformPMF_finset (α := α) sourceEvent)
  have htarget_prob :
      pmfProb (uniformPMF β) p =
        (targetEvent.card : ℝ) / (Fintype.card β : ℝ) := by
    simpa [targetEvent] using
      (pmfProb_uniformPMF_finset (α := β) targetEvent)
  rw [pmfConditionalProb_eq_inter_div_of_pos
    (uniformPMF α) condition (fun a => p (f a)) hcondition_prob_pos]
  rw [hsource_prob, hcondition_prob, htarget_prob]
  have hfiber_ne_real : (fiberCard : ℝ) ≠ 0 := by
    exact_mod_cast hfiber_pos.ne'
  have hcard_alpha_ne_real : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty α›).ne'
  have hcard_beta_ne_real : (Fintype.card β : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty β›).ne'
  rw [hsource_card, hcondition_card]
  norm_num [Nat.cast_mul]
  field_simp [hfiber_ne_real, hcard_alpha_ne_real, hcard_beta_ne_real]

/--
Conditional probability is continuous along any filter when the conditioning
event and the joint event converge and the limiting conditioning probability is
positive.
-/
theorem pmfConditionalProb_tendsto_of_inter_tendsto_of_condition_tendsto
    {ι α : Type*} [Fintype α] [DecidableEq α] {l : Filter ι}
    (μSeq : ι → PMF α) (μ : PMF α)
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hp_pos : 0 < pmfProb μ p)
    (hinter :
      Filter.Tendsto
        (fun i : ι => pmfProb (μSeq i) (fun a => p a ∧ q a))
        l
        (nhds (pmfProb μ (fun a => p a ∧ q a))))
    (hcondition :
      Filter.Tendsto
        (fun i : ι => pmfProb (μSeq i) p)
        l
        (nhds (pmfProb μ p))) :
    Filter.Tendsto
      (fun i : ι => pmfConditionalProb (μSeq i) p q)
      l
      (nhds (pmfConditionalProb μ p q)) := by
  classical
  have hseq_pos :
      ∀ᶠ i in l, 0 < pmfProb (μSeq i) p :=
    hcondition.eventually (eventually_gt_nhds hp_pos)
  have hquot :
      Filter.Tendsto
        (fun i : ι =>
          pmfProb (μSeq i) (fun a => p a ∧ q a) /
            pmfProb (μSeq i) p)
        l
        (nhds
          (pmfProb μ (fun a => p a ∧ q a) / pmfProb μ p)) :=
    hinter.div hcondition hp_pos.ne'
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p q hp_pos]
  exact hquot.congr' <| hseq_pos.mono fun i hi => by
    exact (pmfConditionalProb_eq_inter_div_of_pos (μSeq i) p q hi).symm

/-- If an event holds on every finite PMF atom, its probability is one. -/
theorem pmfProb_eq_one_of_forall
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    (hp : ∀ a, p a) :
    pmfProb μ p = 1 := by
  unfold pmfProb
  simpa [hp] using (pmfExp_const μ (1 : ℝ))

/--
If `q` implies `p`, then the probability of `p ∧ q` is just the probability
of `q`.
-/
theorem pmfProb_inter_eq_right_of_imp
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (himp : ∀ a, q a → p a) :
    pmfProb μ (fun a => p a ∧ q a) = pmfProb μ q := by
  classical
  unfold pmfProb
  refine pmfExp_congr μ ?_
  intro a
  by_cases hq : q a
  · have hp : p a := himp a hq
    simp [hp, hq]
  · simp [hq]

/-- Conditioning on an event that always holds leaves event probability unchanged. -/
theorem pmfConditionalProb_eq_pmfProb_of_forall_condition
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hp : ∀ a, p a) :
    pmfConditionalProb μ p q = pmfProb μ q := by
  classical
  have hp_prob : pmfProb μ p = 1 :=
    pmfProb_eq_one_of_forall μ p hp
  have hp_pos : 0 < pmfProb μ p := by
    rw [hp_prob]
    norm_num
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p q hp_pos]
  rw [pmfProb_inter_eq_right_of_imp μ p q (by intro a _hq; exact hp a)]
  rw [hp_prob]
  ring

/--
For nested events `q ⊆ p`, the probability of `q` is the conditional
probability of `q` given `p`, multiplied by the probability of `p`.
-/
theorem pmfProb_eq_mul_conditionalProb_of_imp
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (himp : ∀ a, q a → p a)
    (hp_pos : 0 < pmfProb μ p) :
    pmfProb μ q = pmfConditionalProb μ p q * pmfProb μ p := by
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p q hp_pos]
  rw [pmfProb_inter_eq_right_of_imp μ p q himp]
  field_simp [hp_pos.ne']

/--
Conditional probabilities are unchanged when the target events agree on the
conditioning event.
-/
theorem pmfConditionalProb_congr_of_condition
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q r : α → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r]
    (hqr : ∀ a, p a → (q a ↔ r a)) :
    pmfConditionalProb μ p q = pmfConditionalProb μ p r := by
  classical
  have hind :
      pmfIndicatorExp μ p (fun a => if q a then (1 : ℝ) else 0) =
        pmfIndicatorExp μ p (fun a => if r a then (1 : ℝ) else 0) := by
    unfold pmfIndicatorExp
    refine pmfExp_congr μ ?_
    intro a
    by_cases hp : p a
    · have hiff := hqr a hp
      by_cases hq : q a
      · have hr : r a := hiff.1 hq
        simp [hp, hq, hr]
      · have hr : ¬ r a := fun hr => hq (hiff.2 hr)
        simp [hp, hq, hr]
    · simp [hp]
  unfold pmfConditionalProb pmfConditionalExp
  simp [hind]

/--
Conditional probability is invariant under replacing the conditioning event by
an equivalent event and replacing the target by an event that agrees on that
conditioning event.
-/
theorem pmfConditionalProb_congr
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p p' q q' : α → Prop)
    [DecidablePred p] [DecidablePred p'] [DecidablePred q] [DecidablePred q']
    (hp : ∀ a, p a ↔ p' a)
    (hq : ∀ a, p a → (q a ↔ q' a)) :
    pmfConditionalProb μ p q = pmfConditionalProb μ p' q' := by
  classical
  have hprob : pmfProb μ p = pmfProb μ p' :=
    pmfProb_congr μ hp
  have hind :
      pmfIndicatorExp μ p (fun a => if q a then (1 : ℝ) else 0) =
        pmfIndicatorExp μ p' (fun a => if q' a then (1 : ℝ) else 0) := by
    unfold pmfIndicatorExp
    refine pmfExp_congr μ ?_
    intro a
    by_cases hpa : p a
    · have hp'a : p' a := (hp a).1 hpa
      have hiff := hq a hpa
      by_cases hqa : q a
      · have hq'a : q' a := hiff.1 hqa
        simp [hpa, hp'a, hqa, hq'a]
      · have hq'a : ¬ q' a := fun hq'a => hqa (hiff.2 hq'a)
        simp [hpa, hp'a, hqa, hq'a]
    · have hp'a : ¬ p' a := fun hp'a => hpa ((hp a).2 hp'a)
      simp [hpa, hp'a]
  unfold pmfConditionalProb pmfConditionalExp
  simp [hprob, hind]

/-- Conditional probability complement rule on a positive-probability event. -/
theorem pmfConditionalProb_compl_eq_one_sub_of_pos
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hp_pos : 0 < pmfProb μ p) :
    pmfConditionalProb μ p (fun a => ¬ q a) =
      1 - pmfConditionalProb μ p q := by
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p (fun a => ¬ q a) hp_pos]
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p q hp_pos]
  have hsplit := pmfProb_eq_inter_add_inter_not μ p q
  have hdiff :
      pmfProb μ (fun a => p a ∧ ¬ q a) =
        pmfProb μ p - pmfProb μ (fun a => p a ∧ q a) := by
    linarith
  rw [hdiff]
  field_simp [hp_pos.ne']

/--
If the conditional probability of `q` given `p` is at most `eps`, then the
conditional probability of its complement is at least `1 - eps`.
-/
theorem one_sub_le_pmfConditionalProb_compl_of_conditionalProb_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    {eps : ℝ}
    (hp_pos : 0 < pmfProb μ p)
    (hprob : pmfConditionalProb μ p q ≤ eps) :
    1 - eps ≤ pmfConditionalProb μ p (fun a => ¬ q a) := by
  rw [pmfConditionalProb_compl_eq_one_sub_of_pos μ p q hp_pos]
  linarith

/--
Finite product lower bound for a nested sequence of events.  If `event 0`
always holds and every conditional transition `event r -> event (r+1)` has
probability at least `base`, then `event k` has probability at least
`base ^ k`.
-/
theorem pmfProb_ge_pow_of_nested_conditionalProb_ge
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : PMF Ω) (event : ℕ → Ω → Prop)
    [∀ r, DecidablePred fun ω => event r ω]
    (k : ℕ) {base : ℝ}
    (hbase_nonneg : 0 ≤ base)
    (hzero : ∀ ω, event 0 ω)
    (hnested : ∀ r, r < k → ∀ ω, event (r + 1) ω → event r ω)
    (hcond : ∀ r, r < k →
      base ≤ pmfConditionalProb μ
        (fun ω => event r ω) (fun ω => event (r + 1) ω)) :
    base ^ k ≤ pmfProb μ (fun ω => event k ω) := by
  classical
  induction k with
  | zero =>
      have hprob0 : pmfProb μ (fun ω => event 0 ω) = 1 :=
        pmfProb_eq_one_of_forall μ (fun ω => event 0 ω) hzero
      simp [hprob0]
  | succ k ih =>
      by_cases hbase_zero : base = 0
      · subst base
        simp [pmfProb_nonneg]
      · have hbase_pos : 0 < base :=
          lt_of_le_of_ne hbase_nonneg (Ne.symm hbase_zero)
        have hprev :
            base ^ k ≤ pmfProb μ (fun ω => event k ω) :=
          ih
            (by
              intro r hr
              exact hnested r (Nat.lt_trans hr (Nat.lt_succ_self k)))
            (by
              intro r hr
              exact hcond r (Nat.lt_trans hr (Nat.lt_succ_self k)))
        have hprev_pos : 0 < pmfProb μ (fun ω => event k ω) :=
          lt_of_lt_of_le (pow_pos hbase_pos k) hprev
        have hstep :
            base ≤ pmfConditionalProb μ
              (fun ω => event k ω) (fun ω => event (k + 1) ω) :=
          hcond k (Nat.lt_succ_self k)
        have hstep_nonneg :
            0 ≤ pmfConditionalProb μ
              (fun ω => event k ω) (fun ω => event (k + 1) ω) :=
          le_trans hbase_nonneg hstep
        have hpow_nonneg : 0 ≤ base ^ k := pow_nonneg hbase_nonneg k
        have hmul :
            base * base ^ k ≤
              pmfConditionalProb μ
                (fun ω => event k ω) (fun ω => event (k + 1) ω) *
                pmfProb μ (fun ω => event k ω) :=
          mul_le_mul hstep hprev hpow_nonneg hstep_nonneg
        have hprod :
            pmfProb μ (fun ω => event (k + 1) ω) =
              pmfConditionalProb μ
                (fun ω => event k ω) (fun ω => event (k + 1) ω) *
                pmfProb μ (fun ω => event k ω) :=
          pmfProb_eq_mul_conditionalProb_of_imp μ
            (fun ω => event k ω) (fun ω => event (k + 1) ω)
            (hnested k (Nat.lt_succ_self k)) hprev_pos
        calc
          base ^ (k + 1) = base * base ^ k := by
            rw [pow_succ]
            ring
          _ ≤ pmfConditionalProb μ
                (fun ω => event k ω) (fun ω => event (k + 1) ω) *
                pmfProb μ (fun ω => event k ω) := hmul
          _ = pmfProb μ (fun ω => event (k + 1) ω) := hprod.symm

/-- Split a finite PMF event according to a finite state map. -/
theorem pmfProb_eq_sum_state_inter
    {Ω σ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype σ] [DecidableEq σ]
    (μ : PMF Ω) (p : Ω → Prop) [DecidablePred p] (state : Ω → σ) :
    pmfProb μ p =
      ∑ s : σ, pmfProb μ (fun ω => p ω ∧ state ω = s) := by
  classical
  unfold pmfProb pmfExp
  calc
    ∑ ω : Ω, (μ ω).toReal * (if p ω then (1 : ℝ) else 0)
        = ∑ ω : Ω, ∑ s : σ,
            (μ ω).toReal *
              (if p ω ∧ state ω = s then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro ω _
          by_cases hp : p ω
          · simp [hp, eq_comm]
          · simp [hp]
    _ = ∑ s : σ, ∑ ω : Ω,
          (μ ω).toReal *
            (if p ω ∧ state ω = s then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]

/--
Conditional-mixture upper bound.  If a finite state map refines a conditioning
event and the conditional probability of `q` is at most `c` on every positive
refined state, then the coarser conditional probability is also at most `c`.
-/
theorem pmfConditionalProb_le_of_state_refinement
    {Ω σ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype σ] [DecidableEq σ]
    (μ : PMF Ω) (p q : Ω → Prop) [DecidablePred p] [DecidablePred q]
    (state : Ω → σ) {c : ℝ}
    (hc_nonneg : 0 ≤ c)
    (hp_pos : 0 < pmfProb μ p)
    (hstate : ∀ s : σ,
      0 < pmfProb μ (fun ω => p ω ∧ state ω = s) →
        pmfConditionalProb μ (fun ω => p ω ∧ state ω = s) q ≤ c) :
    pmfConditionalProb μ p q ≤ c := by
  classical
  have hstate_bound : ∀ s : σ,
      pmfProb μ (fun ω => (p ω ∧ state ω = s) ∧ q ω) ≤
        c * pmfProb μ (fun ω => p ω ∧ state ω = s) := by
    intro s
    by_cases hpos : 0 < pmfProb μ (fun ω => p ω ∧ state ω = s)
    · have h := hstate s hpos
      rw [pmfConditionalProb_eq_inter_div_of_pos
        μ (fun ω => p ω ∧ state ω = s) q hpos] at h
      rwa [div_le_iff₀ hpos] at h
    · have hstate_zero :
          pmfProb μ (fun ω => p ω ∧ state ω = s) = 0 := by
        exact le_antisymm (le_of_not_gt hpos)
          (pmfProb_nonneg μ (fun ω => p ω ∧ state ω = s))
      have hleft_zero :
          pmfProb μ (fun ω => (p ω ∧ state ω = s) ∧ q ω) = 0 := by
        have hle :
            pmfProb μ (fun ω => (p ω ∧ state ω = s) ∧ q ω) ≤
              pmfProb μ (fun ω => p ω ∧ state ω = s) :=
          pmfProb_le_of_imp μ
            (fun ω => (p ω ∧ state ω = s) ∧ q ω)
            (fun ω => p ω ∧ state ω = s)
            (by intro ω hω; exact hω.1)
        exact le_antisymm (by simpa [hstate_zero] using hle)
          (pmfProb_nonneg μ (fun ω => (p ω ∧ state ω = s) ∧ q ω))
      rw [hleft_zero, hstate_zero]
      simpa using hc_nonneg
  have hinter_bound :
      pmfProb μ (fun ω => p ω ∧ q ω) ≤ c * pmfProb μ p := by
    calc
      pmfProb μ (fun ω => p ω ∧ q ω)
          = ∑ s : σ,
              pmfProb μ (fun ω => (p ω ∧ q ω) ∧ state ω = s) := by
            rw [pmfProb_eq_sum_state_inter μ (fun ω => p ω ∧ q ω) state]
      _ ≤ ∑ s : σ,
            c * pmfProb μ (fun ω => p ω ∧ state ω = s) := by
            refine Finset.sum_le_sum ?_
            intro s _
            simpa [and_assoc, and_left_comm, and_comm] using hstate_bound s
      _ = c * ∑ s : σ,
            pmfProb μ (fun ω => p ω ∧ state ω = s) := by
            rw [Finset.mul_sum]
      _ = c * pmfProb μ p := by
            rw [← pmfProb_eq_sum_state_inter μ p state]
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p q hp_pos]
  rwa [div_le_iff₀ hp_pos]

/--
Conditional-mixture equality.  If a finite state map refines a conditioning
event and every positive refined state has the same conditional probability of
`q`, then the coarser conditional probability also has that value.
-/
theorem pmfConditionalProb_eq_of_state_refinement
    {Ω σ : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype σ] [DecidableEq σ]
    (μ : PMF Ω) (p q : Ω → Prop) [DecidablePred p] [DecidablePred q]
    (state : Ω → σ) {c : ℝ}
    (hp_pos : 0 < pmfProb μ p)
    (hstate : ∀ s : σ,
      0 < pmfProb μ (fun ω => p ω ∧ state ω = s) →
        pmfConditionalProb μ (fun ω => p ω ∧ state ω = s) q = c) :
    pmfConditionalProb μ p q = c := by
  classical
  have hstate_eq : ∀ s : σ,
      pmfProb μ (fun ω => (p ω ∧ state ω = s) ∧ q ω) =
        c * pmfProb μ (fun ω => p ω ∧ state ω = s) := by
    intro s
    by_cases hpos : 0 < pmfProb μ (fun ω => p ω ∧ state ω = s)
    · have h := hstate s hpos
      rw [pmfConditionalProb_eq_inter_div_of_pos
        μ (fun ω => p ω ∧ state ω = s) q hpos] at h
      rw [← h]
      field_simp [hpos.ne']
    · have hstate_zero :
          pmfProb μ (fun ω => p ω ∧ state ω = s) = 0 := by
        exact le_antisymm (le_of_not_gt hpos)
          (pmfProb_nonneg μ (fun ω => p ω ∧ state ω = s))
      have hleft_zero :
          pmfProb μ (fun ω => (p ω ∧ state ω = s) ∧ q ω) = 0 := by
        have hle :
            pmfProb μ (fun ω => (p ω ∧ state ω = s) ∧ q ω) ≤
              pmfProb μ (fun ω => p ω ∧ state ω = s) :=
          pmfProb_le_of_imp μ
            (fun ω => (p ω ∧ state ω = s) ∧ q ω)
            (fun ω => p ω ∧ state ω = s)
            (by intro ω hω; exact hω.1)
        exact le_antisymm (by simpa [hstate_zero] using hle)
          (pmfProb_nonneg μ (fun ω => (p ω ∧ state ω = s) ∧ q ω))
      rw [hleft_zero, hstate_zero]
      ring
  have hinter_eq :
      pmfProb μ (fun ω => p ω ∧ q ω) = c * pmfProb μ p := by
    calc
      pmfProb μ (fun ω => p ω ∧ q ω)
          = ∑ s : σ,
              pmfProb μ (fun ω => (p ω ∧ q ω) ∧ state ω = s) := by
            rw [pmfProb_eq_sum_state_inter μ (fun ω => p ω ∧ q ω) state]
      _ = ∑ s : σ,
            c * pmfProb μ (fun ω => p ω ∧ state ω = s) := by
            refine Finset.sum_congr rfl ?_
            intro s _
            simpa [and_assoc, and_left_comm, and_comm] using hstate_eq s
      _ = c * ∑ s : σ,
            pmfProb μ (fun ω => p ω ∧ state ω = s) := by
            rw [Finset.mul_sum]
      _ = c * pmfProb μ p := by
            rw [← pmfProb_eq_sum_state_inter μ p state]
  rw [pmfConditionalProb_eq_inter_div_of_pos μ p q hp_pos]
  rw [hinter_eq]
  field_simp [hp_pos.ne']

/--
Conditional negative dependence implies the pairwise negative-correlation
inequality `Pr[p and q] <= Pr[p] * Pr[q]`.
-/
theorem pmfProb_inter_le_mul_of_conditionalProb_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hq_pos : 0 < pmfProb μ q)
    (hcond : pmfConditionalProb μ q p ≤ pmfProb μ p) :
    pmfProb μ (fun a => p a ∧ q a) ≤
      pmfProb μ p * pmfProb μ q := by
  rw [pmfConditionalProb_eq_inter_div_of_pos μ q p hq_pos] at hcond
  rw [div_le_iff₀ hq_pos] at hcond
  simpa [and_comm, mul_comm] using hcond

/-- Probability of an event on a pair of independent PMF draws. -/
noncomputable def pmfPairProb {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (p : α × β → Prop) [DecidablePred p] : ℝ :=
  pmfPairExp μ ν (fun a b => if p (a, b) then 1 else 0)

/-- Pairwise indicator expectation on a product of two independent PMFs. -/
noncomputable def pmfPairIndicatorExp {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (p : α × β → Prop) [DecidablePred p]
    (f : α × β → ℝ) : ℝ :=
  pmfPairExp μ ν (fun a b => if p (a, b) then f (a, b) else 0)

@[simp] theorem pmfPairIndicatorExp_const_one {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (p : α × β → Prop) [DecidablePred p] :
    pmfPairIndicatorExp μ ν p (fun _ => 1) = pmfPairProb μ ν p := by
  rfl

/-- Conditional expectation on a product of two independent PMFs. -/
noncomputable def pmfPairConditionalExp {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (p : α × β → Prop) [DecidablePred p]
    (f : α × β → ℝ) : ℝ :=
  let q := pmfPairProb μ ν p
  if _h : q = 0 then 0 else pmfPairIndicatorExp μ ν p f / q

@[simp] theorem pmfPairConditionalExp_of_prob_zero {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (p : α × β → Prop) [DecidablePred p]
    (f : α × β → ℝ) (h : pmfPairProb μ ν p = 0) :
    pmfPairConditionalExp μ ν p f = 0 := by
  simp [pmfPairConditionalExp, h]

theorem pmfPairConditionalExp_eq_div_of_pos {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (p : α × β → Prop) [DecidablePred p]
    (f : α × β → ℝ) (h : 0 < pmfPairProb μ ν p) :
    pmfPairConditionalExp μ ν p f = pmfPairIndicatorExp μ ν p f / pmfPairProb μ ν p := by
  simp [pmfPairConditionalExp, h.ne']

theorem pmfPairConditionalExp_pos_iff {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (p : α × β → Prop) [DecidablePred p]
    (f : α × β → ℝ) (h : 0 < pmfPairProb μ ν p) :
    0 < pmfPairConditionalExp μ ν p f ↔ 0 < pmfPairIndicatorExp μ ν p f := by
  rw [pmfPairConditionalExp_eq_div_of_pos (μ := μ) (ν := ν) (p := p) (f := f) h]
  exact zero_lt_div_iff_pos_right h

end EconCSLib
