import DecisionCore.FiniteExpectation

namespace DecisionCore

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

@[simp] theorem pmfIndicatorExp_const_one {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    pmfIndicatorExp μ p (fun _ => 1) = pmfProb μ p := by
  rfl

/-- Conditional expectation of `f` on event `p`, with value `0` when `p` has zero probability. -/
noncomputable def pmfConditionalExp {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ) : ℝ :=
  let q := pmfProb μ p
  if h : q = 0 then 0 else pmfIndicatorExp μ p f / q

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

theorem pmfConditionalExp_pos_iff {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (f : α → ℝ)
    (h : 0 < pmfProb μ p) :
    0 < pmfConditionalExp μ p f ↔ 0 < pmfIndicatorExp μ p f := by
  rw [pmfConditionalExp_eq_div_of_pos (μ := μ) (p := p) (f := f) h]
  exact zero_lt_div_iff_pos_right h

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
  if h : q = 0 then 0 else pmfPairIndicatorExp μ ν p f / q

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

end DecisionCore
