import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-!
# PKG25: A No Free Lunch Theorem for Human-AI Collaboration

This file starts with the source-facing logical surface of the paper.  The
paper's substantive theorem is one-way: every reliable deterministic
collaboration strategy is non-collaborative.  The proof in the paper decomposes
this into two propositions:

1. reliability forces deferral to one fixed coordinate away from `1/2`;
2. for the same coordinate, reliability forces a fixed tie value on the
   `p_k = 1/2` slice.

The finite adversarial collaboration-setting constructions that prove these
two propositions are added below this logical layer.
-/

namespace PKG25NoFreeLunch

/-- Binary classifications are represented as booleans. -/
abbrev Label := Bool

/-- The paper's rounding convention: `round(1/2) = 1`. -/
noncomputable def roundProb (p : ℝ) : Label :=
  decide ((1 : ℝ) / 2 ≤ p)

/-- Interior prediction profiles, i.e. `(0,1)^n` in the paper. -/
def Interior {n : ℕ} (p : Fin n → ℝ) : Prop :=
  ∀ i, 0 < p i ∧ p i < 1

/-- A deterministic collaboration strategy `C : [0,1]^n -> {0,1}`. -/
abbrev CollaborationStrategy (n : ℕ) := (Fin n → ℝ) → Label

/--
The first clause of non-collaboration for a fixed agent `k`: away from the
tie point `1/2`, the strategy agrees with agent `k`'s rounded prediction.
-/
def DefersAwayFromHalf {n : ℕ} (C : CollaborationStrategy n) (k : Fin n) : Prop :=
  ∀ p : Fin n → ℝ, Interior p → p k ≠ (1 : ℝ) / 2 → C p = roundProb (p k)

/--
The second clause of non-collaboration for a fixed agent `k`: on the
`p_k = 1/2` slice, the strategy is constant.
-/
def ConstantOnHalfSlice {n : ℕ} (C : CollaborationStrategy n) (k : Fin n)
    (α : Label) : Prop :=
  ∀ p : Fin n → ℝ, Interior p → p k = (1 : ℝ) / 2 → C p = α

/--
The paper's non-collaboration condition.  It constrains only profiles in
`(0,1)^n`, matching Definition 4 in the source; boundary predictions `0` and
`1` are intentionally exempt.
-/
def NonCollaborative {n : ℕ} (C : CollaborationStrategy n) : Prop :=
  ∃ k : Fin n, ∃ α : Label,
    DefersAwayFromHalf C k ∧ ConstantOnHalfSlice C k α

/--
Abstract accuracy surface used by the logical proof assembly.  The finite
source-model constructions below instantiate this surface with honest finite
collaboration settings.
-/
structure AccuracySurface (n : ℕ) where
  strategyAcc : ℝ
  agentAcc : Fin n → ℝ

/--
The accuracy-profile form of the paper's `S_k` counterexample: the
collaboration strategy is weakly worse than every agent and strictly worse
than agent `k`.
-/
def WeakCounterexampleFor {n : ℕ} (S : AccuracySurface n) (k : Fin n) : Prop :=
  S.strategyAcc < S.agentAcc k ∧ ∀ i : Fin n, S.strategyAcc ≤ S.agentAcc i

/-- Sum the accuracy profiles of one setting per agent. -/
noncomputable def sumAccuracySurface {n : ℕ} (S : Fin n → AccuracySurface n) :
    AccuracySurface n where
  strategyAcc := ∑ k : Fin n, (S k).strategyAcc
  agentAcc := fun i => ∑ k : Fin n, (S k).agentAcc i

/--
If each `S k` is weakly bad for the collaboration strategy and strictly bad
relative to agent `k`, then the summed profile is strictly bad relative to
every agent.  This is the algebraic core of the paper's linear-combination
argument in Proposition 1.
-/
theorem sumAccuracySurface_strategy_lt_agent {n : ℕ} [Nonempty (Fin n)]
    (S : Fin n → AccuracySurface n)
    (hS : ∀ k : Fin n, WeakCounterexampleFor (S k) k) :
    ∀ i : Fin n, (sumAccuracySurface S).strategyAcc <
      (sumAccuracySurface S).agentAcc i := by
  intro i
  classical
  dsimp [sumAccuracySurface]
  refine Finset.sum_lt_sum ?hle ?hex
  · intro k _hk
    exact (hS k).2 i
  · exact ⟨i, Finset.mem_univ i, (hS i).1⟩

/-- Interpret a boolean prediction as a real-valued label. -/
def labelReal : Label → ℝ
  | false => 0
  | true => 1

/--
Expected correctness at one input whose conditional probability of label `1`
is `η`.  This is the accuracy notion used in the proof; the source paper's
opening display writes an error/loss expression, but all subsequent formulas
and arguments use correctness probability.
-/
def pointAccuracy (ŷ : Label) (η : ℝ) : ℝ :=
  if ŷ then η else 1 - η

theorem roundProb_zero : roundProb 0 = false := by
  norm_num [roundProb]

theorem roundProb_one : roundProb 1 = true := by
  norm_num [roundProb]

theorem roundProb_labelReal (b : Label) : roundProb (labelReal b) = b := by
  cases b <;> simp [labelReal, roundProb_zero, roundProb_one]

theorem roundProb_eq_true_iff {p : ℝ} : roundProb p = true ↔ (1 : ℝ) / 2 ≤ p := by
  simp [roundProb]

theorem roundProb_eq_false_iff {p : ℝ} : roundProb p = false ↔ p < (1 : ℝ) / 2 := by
  simp [roundProb, not_le]

theorem pointAccuracy_range {ŷ : Label} {η : ℝ} (hη : 0 ≤ η ∧ η ≤ 1) :
    0 ≤ pointAccuracy ŷ η ∧ pointAccuracy ŷ η ≤ 1 := by
  cases ŷ
  · simp [pointAccuracy]
    constructor <;> linarith
  · simp [pointAccuracy, hη.1, hη.2]

theorem pointAccuracy_labelReal_self (b : Label) :
    pointAccuracy b (labelReal b) = 1 := by
  cases b <;> simp [pointAccuracy, labelReal]

theorem pointAccuracy_labelReal_not (b : Label) :
    pointAccuracy b (labelReal (!b)) = 0 := by
  cases b <;> simp [pointAccuracy, labelReal]

theorem pointAccuracy_labelReal_eq_ite (ŷ b : Label) :
    pointAccuracy ŷ (labelReal b) = if ŷ = b then 1 else 0 := by
  cases ŷ <;> cases b <;> simp [pointAccuracy, labelReal]

theorem label_eq_not_of_ne {a b : Label} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

theorem pointAccuracy_le_one {ŷ : Label} {η : ℝ} (hη : 0 ≤ η ∧ η ≤ 1) :
    pointAccuracy ŷ η ≤ 1 :=
  (pointAccuracy_range hη).2

/-- Finite event mass. -/
noncomputable def eventMass {X : Type*} [Fintype X] (mass : X → ℝ)
    (A : X → Prop) [DecidablePred A] : ℝ :=
  ∑ x : X, if A x then mass x else 0

/-- Finite event label-one mass. -/
noncomputable def eventLabelMass {X : Type*} [Fintype X] (mass η : X → ℝ)
    (A : X → Prop) [DecidablePred A] : ℝ :=
  ∑ x : X, if A x then mass x * η x else 0

theorem eventMass_nonneg {X : Type*} [Fintype X] (mass : X → ℝ)
    (A : X → Prop) [DecidablePred A] (hmass_nonneg : ∀ x : X, 0 ≤ mass x) :
    0 ≤ eventMass mass A := by
  unfold eventMass
  exact Finset.sum_nonneg (by
    intro x _hx
    by_cases hA : A x
    · simp [hA, hmass_nonneg x]
    · simp [hA])

theorem eventLabelMass_eq_zero_of_eventMass_eq_zero {X : Type*} [Fintype X]
    (mass η : X → ℝ) (A : X → Prop) [DecidablePred A]
    (hmass_nonneg : ∀ x : X, 0 ≤ mass x) (heta_nonneg : ∀ x : X, 0 ≤ η x)
    (hzero : eventMass mass A = 0) :
    eventLabelMass mass η A = 0 := by
  classical
  unfold eventMass at hzero
  unfold eventLabelMass
  refine Finset.sum_eq_zero ?_
  intro x hx
  by_cases hA : A x
  · have hterm_nonneg :
        ∀ y ∈ (Finset.univ : Finset X), 0 ≤ if A y then mass y else 0 := by
      intro y _hy
      by_cases hAy : A y
      · simp [hAy, hmass_nonneg y]
      · simp [hAy]
    have hxmass :
        (if A x then mass x else 0) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hzero x (Finset.mem_univ x)
    have hmassx : mass x = 0 := by
      simpa [hA] using hxmass
    simp [hA, hmassx]
  · simp [hA]

theorem eventMass_const_mul {X : Type*} [Fintype X] (c : ℝ) (mass : X → ℝ)
    (A : X → Prop) [DecidablePred A] :
    eventMass (fun x => c * mass x) A = c * eventMass mass A := by
  classical
  unfold eventMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  by_cases hA : A x <;> simp [hA]

theorem eventLabelMass_const_mul {X : Type*} [Fintype X] (c : ℝ) (mass η : X → ℝ)
    (A : X → Prop) [DecidablePred A] :
    eventLabelMass (fun x => c * mass x) η A = c * eventLabelMass mass η A := by
  classical
  unfold eventLabelMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  by_cases hA : A x <;> simp [hA, mul_assoc]

/--
A finite collaboration setting.  This is enough for the paper proof because
all adversarial settings constructed in Section 4 are finite.
-/
structure FiniteCollaborationSetting (n : ℕ) where
  X : Type
  [fintypeX : Fintype X]
  [decidableEqX : DecidableEq X]
  mass : X → ℝ
  mass_nonneg : ∀ x : X, 0 ≤ mass x
  mass_sum : ∑ x : X, mass x = 1
  eta : X → ℝ
  eta_range : ∀ x : X, 0 ≤ eta x ∧ eta x ≤ 1
  pred : Fin n → X → ℝ
  pred_range : ∀ i x, 0 ≤ pred i x ∧ pred i x ≤ 1
  calibrated :
    ∀ i : Fin n, ∀ p : ℝ,
      let A : X → Prop := fun x => pred i x = p
      eventMass mass A > 0 →
        eventLabelMass mass eta A = p * eventMass mass A

namespace FiniteCollaborationSetting

attribute [instance] fintypeX decidableEqX

/-- Individual classifier induced by agent `i`'s predicted probability. -/
noncomputable def agentClassifier {n : ℕ} (S : FiniteCollaborationSetting n)
    (i : Fin n) (x : S.X) : Label :=
  roundProb (S.pred i x)

/-- Classifier induced by a collaboration strategy. -/
def strategyClassifier {n : ℕ} (C : CollaborationStrategy n)
    (S : FiniteCollaborationSetting n) (x : S.X) : Label :=
  C (fun i => S.pred i x)

/-- Accuracy of agent `i` in a finite collaboration setting. -/
noncomputable def agentAccuracy {n : ℕ} (S : FiniteCollaborationSetting n)
    (i : Fin n) : ℝ :=
  ∑ x : S.X, S.mass x * pointAccuracy (S.agentClassifier i x) (S.eta x)

/-- Accuracy of a collaboration strategy in a finite collaboration setting. -/
noncomputable def strategyAccuracy {n : ℕ} (C : CollaborationStrategy n)
    (S : FiniteCollaborationSetting n) : ℝ :=
  ∑ x : S.X, S.mass x * pointAccuracy (S.strategyClassifier C x) (S.eta x)

/-- The accuracy surface associated with a finite collaboration setting. -/
noncomputable def toAccuracySurface {n : ℕ} (C : CollaborationStrategy n)
    (S : FiniteCollaborationSetting n) : AccuracySurface n where
  strategyAcc := S.strategyAccuracy C
  agentAcc := fun i => S.agentAccuracy i

theorem calibrated_unconditional {n : ℕ} (S : FiniteCollaborationSetting n)
    (i : Fin n) (p : ℝ) :
    let A : S.X → Prop := fun x => S.pred i x = p
    eventLabelMass S.mass S.eta A = p * eventMass S.mass A := by
  classical
  dsimp
  by_cases hpos : eventMass S.mass (fun x => S.pred i x = p) > 0
  · exact S.calibrated i p hpos
  · have hnonneg :
        0 ≤ eventMass S.mass (fun x => S.pred i x = p) :=
      eventMass_nonneg S.mass (fun x => S.pred i x = p) S.mass_nonneg
    have hzero : eventMass S.mass (fun x => S.pred i x = p) = 0 :=
      le_antisymm (le_of_not_gt hpos) hnonneg
    rw [hzero, mul_zero]
    exact eventLabelMass_eq_zero_of_eventMass_eq_zero S.mass S.eta
      (fun x => S.pred i x = p) S.mass_nonneg (fun x => (S.eta_range x).1) hzero

noncomputable def mix {n m : ℕ} (S : Fin m → FiniteCollaborationSetting n)
    (w : Fin m → ℝ) (hw_nonneg : ∀ r, 0 ≤ w r) (hw_sum : ∑ r : Fin m, w r = 1) :
    FiniteCollaborationSetting n where
  X := Sigma fun r : Fin m => (S r).X
  mass := fun z => w z.1 * (S z.1).mass z.2
  mass_nonneg := by
    intro z
    exact mul_nonneg (hw_nonneg z.1) ((S z.1).mass_nonneg z.2)
  mass_sum := by
    classical
    rw [Fintype.sum_sigma]
    calc
      (∑ r : Fin m, ∑ x : (S r).X, w r * (S r).mass x)
          = ∑ r : Fin m, w r * ∑ x : (S r).X, (S r).mass x := by
            refine Finset.sum_congr rfl ?_
            intro r _hr
            rw [Finset.mul_sum]
      _ = ∑ r : Fin m, w r := by
            refine Finset.sum_congr rfl ?_
            intro r _hr
            rw [(S r).mass_sum, mul_one]
      _ = 1 := hw_sum
  eta := fun z => (S z.1).eta z.2
  eta_range := by
    intro z
    exact (S z.1).eta_range z.2
  pred := fun i z => (S z.1).pred i z.2
  pred_range := by
    intro i z
    exact (S z.1).pred_range i z.2
  calibrated := by
    intro i q
    classical
    dsimp
    intro _hpos
    let A : (Sigma fun r : Fin m => (S r).X) → Prop :=
      fun z => (S z.1).pred i z.2 = q
    have hlabel :
        eventLabelMass
            (fun z : Sigma fun r : Fin m => (S r).X => w z.1 * (S z.1).mass z.2)
            (fun z : Sigma fun r : Fin m => (S r).X => (S z.1).eta z.2) A
          =
        ∑ r : Fin m,
          w r * eventLabelMass (S r).mass (S r).eta
            (fun x : (S r).X => (S r).pred i x = q) := by
      unfold eventLabelMass
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl ?_
      intro r _hr
      change eventLabelMass (fun x : (S r).X => w r * (S r).mass x) (S r).eta
          (fun x : (S r).X => (S r).pred i x = q)
        =
        w r * eventLabelMass (S r).mass (S r).eta
          (fun x : (S r).X => (S r).pred i x = q)
      exact eventLabelMass_const_mul (w r) (S r).mass (S r).eta
        (fun x : (S r).X => (S r).pred i x = q)
    have hmass :
        eventMass
            (fun z : Sigma fun r : Fin m => (S r).X => w z.1 * (S z.1).mass z.2) A
          =
        ∑ r : Fin m,
          w r * eventMass (S r).mass
            (fun x : (S r).X => (S r).pred i x = q) := by
      unfold eventMass
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl ?_
      intro r _hr
      change eventMass (fun x : (S r).X => w r * (S r).mass x)
          (fun x : (S r).X => (S r).pred i x = q)
        =
        w r * eventMass (S r).mass
          (fun x : (S r).X => (S r).pred i x = q)
      exact eventMass_const_mul (w r) (S r).mass
        (fun x : (S r).X => (S r).pred i x = q)
    rw [hlabel, hmass]
    calc
      (∑ r : Fin m,
          w r * eventLabelMass (S r).mass (S r).eta
            (fun x : (S r).X => (S r).pred i x = q))
          =
        ∑ r : Fin m,
          w r * (q * eventMass (S r).mass
            (fun x : (S r).X => (S r).pred i x = q)) := by
            refine Finset.sum_congr rfl ?_
            intro r _hr
            rw [calibrated_unconditional (S r) i q]
      _ = q *
        ∑ r : Fin m,
          w r * eventMass (S r).mass
            (fun x : (S r).X => (S r).pred i x = q) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro r _hr
            ring

theorem strategyAccuracy_mix {n m : ℕ} (S : Fin m → FiniteCollaborationSetting n)
    (w : Fin m → ℝ) (hw_nonneg : ∀ r, 0 ≤ w r) (hw_sum : ∑ r : Fin m, w r = 1)
    (C : CollaborationStrategy n) :
    (mix S w hw_nonneg hw_sum).strategyAccuracy C =
      ∑ r : Fin m, w r * (S r).strategyAccuracy C := by
  classical
  unfold strategyAccuracy mix
  change
    (∑ z : Sigma fun r : Fin m => (S r).X,
      w z.1 * (S z.1).mass z.2 *
        pointAccuracy ((S z.1).strategyClassifier C z.2) ((S z.1).eta z.2))
      =
    ∑ r : Fin m, w r *
      (∑ x : (S r).X,
        (S r).mass x * pointAccuracy ((S r).strategyClassifier C x) ((S r).eta x))
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  ring

theorem agentAccuracy_mix {n m : ℕ} (S : Fin m → FiniteCollaborationSetting n)
    (w : Fin m → ℝ) (hw_nonneg : ∀ r, 0 ≤ w r) (hw_sum : ∑ r : Fin m, w r = 1)
    (i : Fin n) :
    (mix S w hw_nonneg hw_sum).agentAccuracy i =
      ∑ r : Fin m, w r * (S r).agentAccuracy i := by
  classical
  unfold agentAccuracy mix
  change
    (∑ z : Sigma fun r : Fin m => (S r).X,
      w z.1 * (S z.1).mass z.2 *
        pointAccuracy ((S z.1).agentClassifier i z.2) ((S z.1).eta z.2))
      =
    ∑ r : Fin m, w r *
      (∑ x : (S r).X,
        (S r).mass x * pointAccuracy ((S r).agentClassifier i x) ((S r).eta x))
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  ring

theorem strategyAccuracy_range {n : ℕ} (S : FiniteCollaborationSetting n)
    (C : CollaborationStrategy n) :
    0 ≤ S.strategyAccuracy C ∧ S.strategyAccuracy C ≤ 1 := by
  classical
  unfold strategyAccuracy
  constructor
  · exact Finset.sum_nonneg (by
      intro x _hx
      exact mul_nonneg (S.mass_nonneg x) (pointAccuracy_range (S.eta_range x)).1)
  · calc
      (∑ x : S.X, S.mass x * pointAccuracy (S.strategyClassifier C x) (S.eta x))
          ≤ ∑ x : S.X, S.mass x * 1 := by
            exact Finset.sum_le_sum (by
              intro x _hx
              exact mul_le_mul_of_nonneg_left
                (pointAccuracy_range (S.eta_range x)).2 (S.mass_nonneg x))
      _ = 1 := by simpa [S.mass_sum]

theorem agentAccuracy_range {n : ℕ} (S : FiniteCollaborationSetting n) (i : Fin n) :
    0 ≤ S.agentAccuracy i ∧ S.agentAccuracy i ≤ 1 := by
  classical
  unfold agentAccuracy
  constructor
  · exact Finset.sum_nonneg (by
      intro x _hx
      exact mul_nonneg (S.mass_nonneg x) (pointAccuracy_range (S.eta_range x)).1)
  · calc
      (∑ x : S.X, S.mass x * pointAccuracy (S.agentClassifier i x) (S.eta x))
          ≤ ∑ x : S.X, S.mass x * 1 := by
            exact Finset.sum_le_sum (by
              intro x _hx
              exact mul_le_mul_of_nonneg_left
                (pointAccuracy_range (S.eta_range x)).2 (S.mass_nonneg x))
      _ = 1 := by simpa [S.mass_sum]

end FiniteCollaborationSetting

/--
Reliability in the paper means the strategy is at least as accurate as the
least accurate agent.  On a nonempty finite agent set this is equivalent to:
for every setting, some agent's accuracy is no larger than the strategy's
accuracy.
-/
def ReliableOn (n : ℕ) (Settings : Type*) (strategyAcc : Settings → ℝ)
    (agentAcc : Settings → Fin n → ℝ) : Prop :=
  ∀ S : Settings, ∃ i : Fin n, agentAcc S i ≤ strategyAcc S

/--
Source-style collaboration-setting accuracy surface.  This abstracts the
paper's general probability-space definition down to the two accuracy
quantities used by reliability.  Finite settings constructed in the proof embed
into this surface below.
-/
structure CollaborationSetting (n : ℕ) where
  strategyAccuracy : CollaborationStrategy n → ℝ
  agentAccuracy : Fin n → ℝ

/-- Embed one of the finite proof settings into the source-style setting surface. -/
noncomputable def FiniteCollaborationSetting.toCollaborationSetting {n : ℕ}
    (S : FiniteCollaborationSetting n) : CollaborationSetting n where
  strategyAccuracy := fun C => S.strategyAccuracy C
  agentAccuracy := fun i => S.agentAccuracy i

/-- Source-style reliability: the strategy beats the least accurate agent in every setting. -/
def Reliable {n : ℕ} (C : CollaborationStrategy n) : Prop :=
  ReliableOn n (CollaborationSetting n)
    (fun S => S.strategyAccuracy C)
    (fun S i => S.agentAccuracy i)

/-- Reliability over the finite collaboration settings used by the source proof. -/
def ReliableFinite {n : ℕ} (C : CollaborationStrategy n) : Prop :=
  ReliableOn n (FiniteCollaborationSetting n)
    (fun S => S.strategyAccuracy C)
    (fun S i => S.agentAccuracy i)

/--
Source-style reliability implies reliability on the finite witness settings.
This is the bridge that lets the finite counterexample proof prove the paper's
general reliability theorem.
-/
theorem reliableFinite_of_reliable {n : ℕ} {C : CollaborationStrategy n}
    (hrel : Reliable C) : ReliableFinite C := by
  intro S
  exact hrel (S.toCollaborationSetting)

/-! ## Proposition 1 finite counterexample construction -/

/--
The odds ratio used for the source's Proposition 1 counterexample.  If the
collaboration strategy outputs `0`, the source uses `(1-p_i)/p_i`; if it
outputs `1`, it uses `p_i/(1-p_i)`.
-/
noncomputable def part1Odds (b : Label) (p : ℝ) : ℝ :=
  if b then p / (1 - p) else (1 - p) / p

theorem part1Odds_pos {b : Label} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < part1Odds b p := by
  by_cases hb : b
  · simp [part1Odds, hb, div_pos hp0 (sub_pos.mpr hp1)]
  · simp [part1Odds, hb, div_pos (sub_pos.mpr hp1) hp0]

theorem part1Odds_le_one_of_round_ne {b : Label} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hne : roundProb p ≠ b) :
    part1Odds b p ≤ 1 := by
  cases b
  · have hround : roundProb p = true := by
      cases h : roundProb p
      · exact (hne h).elim
      · rfl
    have hhalf : (1 : ℝ) / 2 ≤ p := roundProb_eq_true_iff.mp hround
    rw [part1Odds]
    simp
    exact (div_le_one hp0).mpr (by linarith)
  · have hround : roundProb p = false := by
      cases h : roundProb p
      · rfl
      · exact (hne h).elim
    have hhalf : p < (1 : ℝ) / 2 := roundProb_eq_false_iff.mp hround
    rw [part1Odds]
    simp
    exact (div_le_one (sub_pos.mpr hp1)).mpr (by linarith)

theorem part1Odds_lt_one_of_round_ne_of_ne_half {b : Label} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hne : roundProb p ≠ b)
    (hhalf_ne : p ≠ (1 : ℝ) / 2) :
    part1Odds b p < 1 := by
  cases b
  · have hround : roundProb p = true := by
      cases h : roundProb p
      · exact (hne h).elim
      · rfl
    have hhalf : (1 : ℝ) / 2 < p := by
      have hle : (1 : ℝ) / 2 ≤ p := roundProb_eq_true_iff.mp hround
      exact lt_of_le_of_ne hle (Ne.symm hhalf_ne)
    rw [part1Odds]
    simp
    exact (div_lt_one hp0).mpr (by linarith)
  · have hround : roundProb p = false := by
      cases h : roundProb p
      · rfl
      · exact (hne h).elim
    have hhalf : p < (1 : ℝ) / 2 := roundProb_eq_false_iff.mp hround
    rw [part1Odds]
    simp
    exact (div_lt_one (sub_pos.mpr hp1)).mpr (by linarith)

/-- Denominator for the finite source masses in the Proposition 1 witness. -/
noncomputable def part1Denom {n : ℕ} (b : Label) (p : Fin n → ℝ) : ℝ :=
  1 + ∑ i : Fin n, part1Odds b (p i)

theorem part1Denom_pos {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (hp : Interior p) : 0 < part1Denom b p := by
  have hnonneg : 0 ≤ ∑ i : Fin n, part1Odds b (p i) := by
    exact Finset.sum_nonneg (by
      intro i _hi
      exact le_of_lt (part1Odds_pos (hp i).1 (hp i).2))
  unfold part1Denom
  exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right hnonneg)

/-- Source domain for the Proposition 1 witness: `none` is `0`, `some i` is `i`. -/
abbrev Part1Point (n : ℕ) := Option (Fin n)

/-- Mass function for the Proposition 1 finite witness. -/
noncomputable def part1Mass {n : ℕ} (b : Label) (p : Fin n → ℝ) :
    Part1Point n → ℝ
  | none => 1 / part1Denom b p
  | some i => part1Odds b (p i) / part1Denom b p

/-- Conditional label probability for the Proposition 1 finite witness. -/
def part1Eta {n : ℕ} (b : Label) : Part1Point n → ℝ
  | none => labelReal (!b)
  | some _ => labelReal b

/-- Predictor induced by the source partition `{0,i}` plus singleton cells. -/
def part1Pred {n : ℕ} (b : Label) (p : Fin n → ℝ) (i : Fin n) :
    Part1Point n → ℝ
  | none => p i
  | some j => if j = i then p i else labelReal b

theorem part1Mass_nonneg {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (hp : Interior p) (x : Part1Point n) :
    0 ≤ part1Mass b p x := by
  cases x with
  | none =>
      exact div_nonneg zero_le_one (le_of_lt (part1Denom_pos (b := b) hp))
  | some i =>
      exact div_nonneg
        (le_of_lt (part1Odds_pos (hp i).1 (hp i).2))
        (le_of_lt (part1Denom_pos (b := b) hp))

theorem part1Mass_none_pos {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (hp : Interior p) :
    0 < part1Mass b p (none : Part1Point n) := by
  exact div_pos zero_lt_one (part1Denom_pos (b := b) hp)

theorem part1Mass_some_pos {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (hp : Interior p) (i : Fin n) :
    0 < part1Mass b p (some i : Part1Point n) := by
  exact div_pos (part1Odds_pos (hp i).1 (hp i).2) (part1Denom_pos (b := b) hp)

theorem part1Mass_some_le_none_of_round_ne {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (hp : Interior p) {i : Fin n} (hne : roundProb (p i) ≠ b) :
    part1Mass b p (some i : Part1Point n) ≤ part1Mass b p none := by
  unfold part1Mass
  exact div_le_div_of_nonneg_right
    (part1Odds_le_one_of_round_ne (hp i).1 (hp i).2 hne)
    (le_of_lt (part1Denom_pos (b := b) hp))

theorem part1Mass_some_lt_none_of_round_ne_of_ne_half {n : ℕ} {b : Label}
    {p : Fin n → ℝ} (hp : Interior p) {i : Fin n}
    (hne : roundProb (p i) ≠ b) (hhalf_ne : p i ≠ (1 : ℝ) / 2) :
    part1Mass b p (some i : Part1Point n) < part1Mass b p none := by
  unfold part1Mass
  exact div_lt_div_of_pos_right
    (part1Odds_lt_one_of_round_ne_of_ne_half (hp i).1 (hp i).2 hne hhalf_ne)
    (part1Denom_pos (b := b) hp)

theorem part1Mass_sum {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (hp : Interior p) :
    (∑ x : Part1Point n, part1Mass b p x) = 1 := by
  classical
  rw [Fintype.sum_option]
  unfold part1Mass part1Denom
  have hden : (1 + ∑ i : Fin n, part1Odds b (p i)) ≠ 0 :=
    ne_of_gt (part1Denom_pos (b := b) hp)
  rw [← Finset.sum_div]
  calc
    1 / (1 + ∑ i : Fin n, part1Odds b (p i)) +
        (∑ x : Fin n, part1Odds b (p x)) /
          (1 + ∑ i : Fin n, part1Odds b (p i))
        = (1 + ∑ i : Fin n, part1Odds b (p i)) /
          (1 + ∑ i : Fin n, part1Odds b (p i)) := by ring
    _ = 1 := by exact div_self hden

theorem labelReal_range (b : Label) : 0 ≤ labelReal b ∧ labelReal b ≤ 1 := by
  cases b <;> simp [labelReal]

theorem part1Eta_range {n : ℕ} (b : Label) (x : Part1Point n) :
    0 ≤ part1Eta b x ∧ part1Eta b x ≤ 1 := by
  cases x <;> simp [part1Eta, labelReal_range]

theorem part1Pred_range {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (hp : Interior p) (i : Fin n) (x : Part1Point n) :
    0 ≤ part1Pred b p i x ∧ part1Pred b p i x ≤ 1 := by
  cases x with
  | none => exact ⟨le_of_lt (hp i).1, le_of_lt (hp i).2⟩
  | some j =>
      by_cases hji : j = i
      · simp [part1Pred, hji, le_of_lt (hp i).1, le_of_lt (hp i).2]
      · simp [part1Pred, hji, labelReal_range]

theorem labelReal_ne_interior {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (hp : Interior p) (i : Fin n) : labelReal b ≠ p i := by
  cases b
  · simp [labelReal]
    exact ne_of_lt (hp i).1
  · simp [labelReal]
    exact ne_of_gt (hp i).2

theorem part1_pair_labelMass_eq {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (hp : Interior p) (i : Fin n) :
    part1Mass b p (none : Part1Point n) * part1Eta b (none : Part1Point n) +
        part1Mass b p (some i) * part1Eta b (some i)
      =
    p i * (part1Mass b p (none : Part1Point n) + part1Mass b p (some i)) := by
  have hden : part1Denom b p ≠ 0 := ne_of_gt (part1Denom_pos (b := b) hp)
  have hp0 : p i ≠ 0 := ne_of_gt (hp i).1
  have hp1 : 1 - p i ≠ 0 := ne_of_gt (sub_pos.mpr (hp i).2)
  cases b
  · simp [part1Mass, part1Eta, part1Odds, labelReal]
    field_simp [hden, hp0]
    ring
  · simp [part1Mass, part1Eta, part1Odds, labelReal]
    field_simp [hden, hp1]
    ring

theorem part1_eventMass_pi {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (hp : Interior p) (i : Fin n) :
    eventMass (part1Mass b p)
        (fun x : Part1Point n => part1Pred b p i x = p i)
      =
    part1Mass b p (none : Part1Point n) + part1Mass b p (some i) := by
  classical
  have hlabel : labelReal b ≠ p i := labelReal_ne_interior hp i
  unfold eventMass
  rw [Fintype.sum_option]
  calc
    (if (fun x : Part1Point n => part1Pred b p i x = p i) none
        then part1Mass b p none else 0) +
        (∑ x : Fin n,
          if part1Pred b p i (some x) = p i then part1Mass b p (some x) else 0)
        =
        part1Mass b p (none : Part1Point n) +
          ∑ x : Fin n, if x = i then part1Mass b p (some x) else 0 := by
          congr 1
          · simp [part1Pred]
          refine Finset.sum_congr rfl ?_
          intro x _hx
          by_cases hxi : x = i
          · simp [part1Pred, hxi]
          · simp [part1Pred, hxi, hlabel]
    _ = part1Mass b p (none : Part1Point n) + part1Mass b p (some i) := by
          rw [Finset.sum_ite_eq']
          simp

theorem part1_eventLabelMass_pi {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (hp : Interior p) (i : Fin n) :
    eventLabelMass (part1Mass b p) (part1Eta b)
        (fun x : Part1Point n => part1Pred b p i x = p i)
      =
    part1Mass b p (none : Part1Point n) * part1Eta b (none : Part1Point n) +
      part1Mass b p (some i) * part1Eta b (some i) := by
  classical
  have hlabel : labelReal b ≠ p i := labelReal_ne_interior hp i
  unfold eventLabelMass
  rw [Fintype.sum_option]
  calc
    (if (fun x : Part1Point n => part1Pred b p i x = p i) none
        then part1Mass b p none * part1Eta b none else 0) +
        (∑ x : Fin n,
          if part1Pred b p i (some x) = p i
          then part1Mass b p (some x) * part1Eta b (some x) else 0)
        =
        part1Mass b p (none : Part1Point n) * part1Eta b (none : Part1Point n) +
          ∑ x : Fin n,
            if x = i then part1Mass b p (some x) * part1Eta b (some x) else 0 := by
          congr 1
          · simp [part1Pred]
          refine Finset.sum_congr rfl ?_
          intro x _hx
          by_cases hxi : x = i
          · simp [part1Pred, hxi]
          · simp [part1Pred, hxi, hlabel]
    _ = part1Mass b p (none : Part1Point n) * part1Eta b (none : Part1Point n) +
        part1Mass b p (some i) * part1Eta b (some i) := by
          rw [Finset.sum_ite_eq']
          simp

theorem part1_eventLabelMass_labelReal {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (hp : Interior p) (i : Fin n) :
    eventLabelMass (part1Mass b p) (part1Eta b)
        (fun x : Part1Point n => part1Pred b p i x = labelReal b)
      =
    labelReal b *
      eventMass (part1Mass b p)
        (fun x : Part1Point n => part1Pred b p i x = labelReal b) := by
  classical
  have hlabel : labelReal b ≠ p i := labelReal_ne_interior hp i
  unfold eventMass eventLabelMass
  rw [Fintype.sum_option, Fintype.sum_option]
  simp [part1Pred, hlabel, hlabel.symm, eq_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  by_cases hix : x = i
  · simp [hix]
  · simp [part1Eta, mul_comm]

theorem part1_eventMass_empty {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (hp : Interior p) (i : Fin n) {r : ℝ}
    (hrp : r ≠ p i) (hrl : r ≠ labelReal b) :
    eventMass (part1Mass b p)
        (fun x : Part1Point n => part1Pred b p i x = r)
      = 0 := by
  classical
  have hlabel : labelReal b ≠ p i := labelReal_ne_interior hp i
  unfold eventMass
  rw [Fintype.sum_option]
  simp [part1Pred, hrp, eq_comm]
  symm
  refine Finset.sum_eq_zero ?_
  intro x _hx
  by_cases hix : i = x
  · subst x
    simp [hrp]
  · simp [hix, hrl]

theorem part1_calibrated {n : ℕ} {b : Label} {p : Fin n → ℝ}
    (hp : Interior p) :
    ∀ i : Fin n, ∀ r : ℝ,
      eventMass (part1Mass b p) (fun x : Part1Point n => part1Pred b p i x = r) > 0 →
        eventLabelMass (part1Mass b p) (part1Eta b)
            (fun x : Part1Point n => part1Pred b p i x = r) =
          r * eventMass (part1Mass b p)
    (fun x : Part1Point n => part1Pred b p i x = r) := by
  intro i r hpos
  classical
  by_cases hrp : r = p i
  · subst r
    rw [part1_eventLabelMass_pi hp i, part1_eventMass_pi hp i]
    exact part1_pair_labelMass_eq hp i
  · by_cases hrl : r = labelReal b
    · subst r
      exact (part1_eventLabelMass_labelReal hp i).trans (by ring)
    · have hempty :
          eventMass (part1Mass b p)
            (fun x : Part1Point n => part1Pred b p i x = r) = 0 := by
        exact part1_eventMass_empty hp i hrp hrl
      rw [hempty] at hpos
      exact (lt_irrefl (0 : ℝ) hpos).elim

/-- The explicit finite collaboration setting used in Proposition 1. -/
noncomputable def part1Setting {n : ℕ} (b : Label) (p : Fin n → ℝ)
    (hp : Interior p) : FiniteCollaborationSetting n where
  X := Part1Point n
  mass := part1Mass b p
  mass_nonneg := part1Mass_nonneg hp
  mass_sum := part1Mass_sum hp
  eta := part1Eta b
  eta_range := part1Eta_range b
  pred := part1Pred b p
  pred_range := part1Pred_range hp
  calibrated := part1_calibrated hp

theorem part1_strategy_none_accuracy_zero {n : ℕ} {C : CollaborationStrategy n}
    {b : Label} {p : Fin n → ℝ} {hp : Interior p} (hb : C p = b) :
    pointAccuracy
        (FiniteCollaborationSetting.strategyClassifier C (part1Setting b p hp)
          (none : Part1Point n))
        (part1Eta b (none : Part1Point n)) = 0 := by
  cases b <;>
    simp [FiniteCollaborationSetting.strategyClassifier, part1Setting, part1Pred, part1Eta,
      hb, pointAccuracy, labelReal]

theorem part1_agent_some_ne_accuracy_one {n : ℕ} {b : Label} {p : Fin n → ℝ}
    {hp : Interior p} {i j : Fin n} (hji : j ≠ i) :
    pointAccuracy
        (FiniteCollaborationSetting.agentClassifier (part1Setting b p hp) i
          (some j : Part1Point n))
        (part1Eta b (some j : Part1Point n)) = 1 := by
  cases b <;>
    simp [FiniteCollaborationSetting.agentClassifier, part1Setting, part1Pred, part1Eta,
      hji, roundProb_zero, roundProb_one, pointAccuracy, labelReal]

theorem part1_strategy_some_le_mass {n : ℕ} {C : CollaborationStrategy n}
    {b : Label} {p : Fin n → ℝ} {hp : Interior p} (i : Fin n) :
    part1Mass b p (some i : Part1Point n) *
        pointAccuracy
          (FiniteCollaborationSetting.strategyClassifier C (part1Setting b p hp)
            (some i : Part1Point n))
          (part1Eta b (some i : Part1Point n))
      ≤ part1Mass b p (some i : Part1Point n) := by
  have hacc :
      pointAccuracy
          (FiniteCollaborationSetting.strategyClassifier C (part1Setting b p hp)
            (some i : Part1Point n))
          (part1Eta b (some i : Part1Point n)) ≤ 1 :=
    pointAccuracy_le_one (part1Eta_range b (some i : Part1Point n))
  simpa [mul_one] using
    mul_le_mul_of_nonneg_left hacc (part1Mass_nonneg hp (some i : Part1Point n))

theorem part1_strategy_some_le_agent_some_ne {n : ℕ} {C : CollaborationStrategy n}
    {b : Label} {p : Fin n → ℝ} {hp : Interior p} {i j : Fin n}
    (hji : j ≠ i) :
    part1Mass b p (some j : Part1Point n) *
        pointAccuracy
          (FiniteCollaborationSetting.strategyClassifier C (part1Setting b p hp)
            (some j : Part1Point n))
          (part1Eta b (some j : Part1Point n))
      ≤
      part1Mass b p (some j : Part1Point n) *
        pointAccuracy
          (FiniteCollaborationSetting.agentClassifier (part1Setting b p hp) i
            (some j : Part1Point n))
          (part1Eta b (some j : Part1Point n)) := by
  rw [part1_agent_some_ne_accuracy_one (b := b) (p := p) (hp := hp) hji]
  simpa [mul_one] using
    part1_strategy_some_le_mass (C := C) (b := b) (p := p) (hp := hp) j

theorem part1_agent_pair_accuracy_eq_same {n : ℕ} {b : Label} {p : Fin n → ℝ}
    {hp : Interior p} {i : Fin n} (hsame : roundProb (p i) = b) :
    part1Mass b p (none : Part1Point n) *
        pointAccuracy
          (FiniteCollaborationSetting.agentClassifier (part1Setting b p hp) i
            (none : Part1Point n))
          (part1Eta b (none : Part1Point n)) +
      part1Mass b p (some i : Part1Point n) *
        pointAccuracy
          (FiniteCollaborationSetting.agentClassifier (part1Setting b p hp) i
            (some i : Part1Point n))
          (part1Eta b (some i : Part1Point n))
      = part1Mass b p (some i : Part1Point n) := by
  cases b <;>
    simp [FiniteCollaborationSetting.agentClassifier, part1Setting, part1Pred, part1Eta,
      hsame, pointAccuracy, labelReal]

theorem part1_agent_pair_accuracy_eq_ne {n : ℕ} {b : Label} {p : Fin n → ℝ}
    {hp : Interior p} {i : Fin n} (hne : roundProb (p i) ≠ b) :
    part1Mass b p (none : Part1Point n) *
        pointAccuracy
          (FiniteCollaborationSetting.agentClassifier (part1Setting b p hp) i
            (none : Part1Point n))
          (part1Eta b (none : Part1Point n)) +
      part1Mass b p (some i : Part1Point n) *
        pointAccuracy
          (FiniteCollaborationSetting.agentClassifier (part1Setting b p hp) i
            (some i : Part1Point n))
          (part1Eta b (some i : Part1Point n))
      = part1Mass b p (none : Part1Point n) := by
  have hround : roundProb (p i) = !b := label_eq_not_of_ne hne
  cases b <;>
    simp [FiniteCollaborationSetting.agentClassifier, part1Setting, part1Pred, part1Eta,
      hround, pointAccuracy, labelReal]

theorem part1_pair_strategy_le_agent {n : ℕ} {C : CollaborationStrategy n}
    {b : Label} {p : Fin n → ℝ} {hp : Interior p} (hb : C p = b)
    (i : Fin n) :
    part1Mass b p (none : Part1Point n) *
        pointAccuracy
          (FiniteCollaborationSetting.strategyClassifier C (part1Setting b p hp)
            (none : Part1Point n))
          (part1Eta b (none : Part1Point n)) +
      part1Mass b p (some i : Part1Point n) *
        pointAccuracy
          (FiniteCollaborationSetting.strategyClassifier C (part1Setting b p hp)
            (some i : Part1Point n))
          (part1Eta b (some i : Part1Point n))
      ≤
      part1Mass b p (none : Part1Point n) *
        pointAccuracy
          (FiniteCollaborationSetting.agentClassifier (part1Setting b p hp) i
            (none : Part1Point n))
          (part1Eta b (none : Part1Point n)) +
      part1Mass b p (some i : Part1Point n) *
        pointAccuracy
          (FiniteCollaborationSetting.agentClassifier (part1Setting b p hp) i
            (some i : Part1Point n))
          (part1Eta b (some i : Part1Point n)) := by
  have hzero := part1_strategy_none_accuracy_zero (C := C) (b := b) (p := p) (hp := hp) hb
  have hsome := part1_strategy_some_le_mass (C := C) (b := b) (p := p) (hp := hp) i
  by_cases hsame : roundProb (p i) = b
  · rw [part1_agent_pair_accuracy_eq_same (b := b) (p := p) (hp := hp) hsame]
    rw [hzero]
    simpa using hsome
  · rw [part1_agent_pair_accuracy_eq_ne (b := b) (p := p) (hp := hp) hsame]
    rw [hzero]
    exact le_trans (by simpa using hsome) (part1Mass_some_le_none_of_round_ne hp hsame)

theorem part1_pair_strategy_lt_agent {n : ℕ} {C : CollaborationStrategy n}
    {b : Label} {p : Fin n → ℝ} {hp : Interior p} (hb : C p = b)
    {i : Fin n} (hne : roundProb (p i) ≠ b) (hhalf_ne : p i ≠ (1 : ℝ) / 2) :
    part1Mass b p (none : Part1Point n) *
        pointAccuracy
          (FiniteCollaborationSetting.strategyClassifier C (part1Setting b p hp)
            (none : Part1Point n))
          (part1Eta b (none : Part1Point n)) +
      part1Mass b p (some i : Part1Point n) *
        pointAccuracy
          (FiniteCollaborationSetting.strategyClassifier C (part1Setting b p hp)
            (some i : Part1Point n))
          (part1Eta b (some i : Part1Point n))
      <
      part1Mass b p (none : Part1Point n) *
        pointAccuracy
          (FiniteCollaborationSetting.agentClassifier (part1Setting b p hp) i
            (none : Part1Point n))
          (part1Eta b (none : Part1Point n)) +
      part1Mass b p (some i : Part1Point n) *
        pointAccuracy
          (FiniteCollaborationSetting.agentClassifier (part1Setting b p hp) i
            (some i : Part1Point n))
          (part1Eta b (some i : Part1Point n)) := by
  have hzero := part1_strategy_none_accuracy_zero (C := C) (b := b) (p := p) (hp := hp) hb
  have hsome := part1_strategy_some_le_mass (C := C) (b := b) (p := p) (hp := hp) i
  rw [part1_agent_pair_accuracy_eq_ne (b := b) (p := p) (hp := hp) hne]
  rw [hzero]
  exact lt_of_le_of_lt (by simpa using hsome)
    (part1Mass_some_lt_none_of_round_ne_of_ne_half hp hne hhalf_ne)

theorem part1Setting_strategyAccuracy_le_agentAccuracy {n : ℕ}
    {C : CollaborationStrategy n} {b : Label} {p : Fin n → ℝ} {hp : Interior p}
    (hb : C p = b) (i : Fin n) :
    (part1Setting b p hp).strategyAccuracy C ≤
      (part1Setting b p hp).agentAccuracy i := by
  classical
  unfold FiniteCollaborationSetting.strategyAccuracy FiniteCollaborationSetting.agentAccuracy
  change
    (∑ x : Part1Point n,
      part1Mass b p x *
        pointAccuracy
          (FiniteCollaborationSetting.strategyClassifier C (part1Setting b p hp) x)
          (part1Eta b x))
      ≤
    (∑ x : Part1Point n,
      part1Mass b p x *
        pointAccuracy
          (FiniteCollaborationSetting.agentClassifier (part1Setting b p hp) i x)
          (part1Eta b x))
  rw [Fintype.sum_option, Fintype.sum_option]
  let fs : Fin n → ℝ := fun j =>
    part1Mass b p (some j : Part1Point n) *
      pointAccuracy
        (FiniteCollaborationSetting.strategyClassifier C (part1Setting b p hp)
          (some j : Part1Point n))
        (part1Eta b (some j : Part1Point n))
  let gs : Fin n → ℝ := fun j =>
    part1Mass b p (some j : Part1Point n) *
      pointAccuracy
        (FiniteCollaborationSetting.agentClassifier (part1Setting b p hp) i
          (some j : Part1Point n))
        (part1Eta b (some j : Part1Point n))
  let f0 : ℝ :=
    part1Mass b p (none : Part1Point n) *
      pointAccuracy
        (FiniteCollaborationSetting.strategyClassifier C (part1Setting b p hp)
          (none : Part1Point n))
        (part1Eta b (none : Part1Point n))
  let g0 : ℝ :=
    part1Mass b p (none : Part1Point n) *
      pointAccuracy
        (FiniteCollaborationSetting.agentClassifier (part1Setting b p hp) i
          (none : Part1Point n))
        (part1Eta b (none : Part1Point n))
  change f0 + ∑ j : Fin n, fs j ≤ g0 + ∑ j : Fin n, gs j
  rw [← Finset.add_sum_erase Finset.univ fs (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ gs (Finset.mem_univ i)]
  rw [← add_assoc, ← add_assoc]
  exact add_le_add
    (part1_pair_strategy_le_agent (C := C) (b := b) (p := p) (hp := hp) hb i)
    (Finset.sum_le_sum (by
      intro j hj
      have hji : j ≠ i := by
        exact (Finset.mem_erase.mp hj).1
      exact part1_strategy_some_le_agent_some_ne (C := C) (b := b) (p := p)
        (hp := hp) hji))

theorem part1Setting_strategyAccuracy_lt_agentAccuracy {n : ℕ}
    {C : CollaborationStrategy n} {b : Label} {p : Fin n → ℝ} {hp : Interior p}
    (hb : C p = b) {i : Fin n} (hne : roundProb (p i) ≠ b)
    (hhalf_ne : p i ≠ (1 : ℝ) / 2) :
    (part1Setting b p hp).strategyAccuracy C <
      (part1Setting b p hp).agentAccuracy i := by
  classical
  unfold FiniteCollaborationSetting.strategyAccuracy FiniteCollaborationSetting.agentAccuracy
  change
    (∑ x : Part1Point n,
      part1Mass b p x *
        pointAccuracy
          (FiniteCollaborationSetting.strategyClassifier C (part1Setting b p hp) x)
          (part1Eta b x))
      <
    (∑ x : Part1Point n,
      part1Mass b p x *
        pointAccuracy
          (FiniteCollaborationSetting.agentClassifier (part1Setting b p hp) i x)
          (part1Eta b x))
  rw [Fintype.sum_option, Fintype.sum_option]
  let fs : Fin n → ℝ := fun j =>
    part1Mass b p (some j : Part1Point n) *
      pointAccuracy
        (FiniteCollaborationSetting.strategyClassifier C (part1Setting b p hp)
          (some j : Part1Point n))
        (part1Eta b (some j : Part1Point n))
  let gs : Fin n → ℝ := fun j =>
    part1Mass b p (some j : Part1Point n) *
      pointAccuracy
        (FiniteCollaborationSetting.agentClassifier (part1Setting b p hp) i
          (some j : Part1Point n))
        (part1Eta b (some j : Part1Point n))
  let f0 : ℝ :=
    part1Mass b p (none : Part1Point n) *
      pointAccuracy
        (FiniteCollaborationSetting.strategyClassifier C (part1Setting b p hp)
          (none : Part1Point n))
        (part1Eta b (none : Part1Point n))
  let g0 : ℝ :=
    part1Mass b p (none : Part1Point n) *
      pointAccuracy
        (FiniteCollaborationSetting.agentClassifier (part1Setting b p hp) i
          (none : Part1Point n))
        (part1Eta b (none : Part1Point n))
  change f0 + ∑ j : Fin n, fs j < g0 + ∑ j : Fin n, gs j
  rw [← Finset.add_sum_erase Finset.univ fs (Finset.mem_univ i),
    ← Finset.add_sum_erase Finset.univ gs (Finset.mem_univ i)]
  rw [← add_assoc, ← add_assoc]
  exact add_lt_add_of_lt_of_le
    (part1_pair_strategy_lt_agent (C := C) (b := b) (p := p) (hp := hp) hb hne hhalf_ne)
    (Finset.sum_le_sum (by
      intro j hj
      have hji : j ≠ i := by
        exact (Finset.mem_erase.mp hj).1
      exact part1_strategy_some_le_agent_some_ne (C := C) (b := b) (p := p)
        (hp := hp) hji))

theorem part1Setting_weakCounterexample {n : ℕ} {C : CollaborationStrategy n}
    {p : Fin n → ℝ} (hp : Interior p) {k : Fin n}
    (hhalf_ne : p k ≠ (1 : ℝ) / 2) (hbad : C p ≠ roundProb (p k)) :
    WeakCounterexampleFor
      (FiniteCollaborationSetting.toAccuracySurface C (part1Setting (C p) p hp)) k := by
  constructor
  · exact part1Setting_strategyAccuracy_lt_agentAccuracy
      (C := C) (b := C p) (p := p) (hp := hp) rfl
      (by
        intro h
        exact hbad h.symm)
      hhalf_ne
  · intro i
    exact part1Setting_strategyAccuracy_le_agentAccuracy
      (C := C) (b := C p) (p := p) (hp := hp) rfl i

theorem reliableFinite_exists_defers_away {n : ℕ} [Nonempty (Fin n)]
    {C : CollaborationStrategy n} (hrel : ReliableFinite C) :
    ∃ k : Fin n, DefersAwayFromHalf C k := by
  classical
  by_contra hnone
  have hbad_exists :
      ∀ k : Fin n,
        ∃ p : Fin n → ℝ,
          Interior p ∧ p k ≠ (1 : ℝ) / 2 ∧ C p ≠ roundProb (p k) := by
    intro k
    have hk : ¬ DefersAwayFromHalf C k := by
      intro hk
      exact hnone ⟨k, hk⟩
    simpa [DefersAwayFromHalf] using hk
  choose pbad hprops using hbad_exists
  let S : Fin n → FiniteCollaborationSetting n := fun k =>
    part1Setting (C (pbad k)) (pbad k) (hprops k).1
  have hS : ∀ k : Fin n, WeakCounterexampleFor
      (FiniteCollaborationSetting.toAccuracySurface C (S k)) k := by
    intro k
    exact part1Setting_weakCounterexample (C := C) ((hprops k).1)
      ((hprops k).2.1) ((hprops k).2.2)
  have hnpos_nat : 0 < n := Fin.size_positive'
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos_nat
  let w : Fin n → ℝ := fun _ => (1 : ℝ) / (n : ℝ)
  have hw_nonneg : ∀ k : Fin n, 0 ≤ w k := by
    intro k
    dsimp [w]
    exact div_nonneg zero_le_one (le_of_lt hnpos)
  have hw_pos : ∀ k : Fin n, 0 < w k := by
    intro k
    dsimp [w]
    exact div_pos zero_lt_one hnpos
  have hw_sum : ∑ k : Fin n, w k = 1 := by
    dsimp [w]
    rw [Finset.sum_const, Finset.card_univ]
    simp
    field_simp [ne_of_gt hnpos]
  let Smix := FiniteCollaborationSetting.mix S w hw_nonneg hw_sum
  have hstrict : ∀ i : Fin n, Smix.strategyAccuracy C < Smix.agentAccuracy i := by
    intro i
    dsimp [Smix]
    rw [FiniteCollaborationSetting.strategyAccuracy_mix S w hw_nonneg hw_sum C,
      FiniteCollaborationSetting.agentAccuracy_mix S w hw_nonneg hw_sum i]
    exact Finset.sum_lt_sum
      (by
        intro k _hk
        exact mul_le_mul_of_nonneg_left ((hS k).2 i) (hw_nonneg k))
      ⟨i, Finset.mem_univ i, by
        exact mul_lt_mul_of_pos_left (hS i).1 (hw_pos i)⟩
  rcases hrel Smix with ⟨i, hi⟩
  exact (not_lt_of_ge hi) (hstrict i)

/-! ## Proposition 2 first auxiliary setting -/

abbrev Part2S1Point := Bool

noncomputable def part2S1Mass : Part2S1Point → ℝ
  | false => (1 : ℝ) / 3
  | true => (2 : ℝ) / 3

noncomputable def part2S1Eta : Part2S1Point → ℝ
  | false => (1 : ℝ) / 4
  | true => (3 : ℝ) / 4

noncomputable def part2S1KPred : ℝ := (7 : ℝ) / 12

noncomputable def part2S1Pred {n : ℕ} (k i : Fin n) (x : Part2S1Point) : ℝ :=
  if i = k then part2S1KPred else part2S1Eta x

theorem part2S1Mass_nonneg (x : Part2S1Point) : 0 ≤ part2S1Mass x := by
  cases x <;> norm_num [part2S1Mass]

theorem part2S1Mass_sum : (∑ x : Part2S1Point, part2S1Mass x) = 1 := by
  norm_num [part2S1Mass]

theorem part2S1Eta_range (x : Part2S1Point) :
    0 ≤ part2S1Eta x ∧ part2S1Eta x ≤ 1 := by
  cases x <;> norm_num [part2S1Eta]

theorem part2S1Pred_range {n : ℕ} (k i : Fin n) (x : Part2S1Point) :
    0 ≤ part2S1Pred k i x ∧ part2S1Pred k i x ≤ 1 := by
  by_cases hik : i = k
  · norm_num [part2S1Pred, hik, part2S1KPred]
  · simpa [part2S1Pred, hik] using part2S1Eta_range x

theorem part2S1_calibrated {n : ℕ} (k : Fin n) :
    ∀ i : Fin n, ∀ r : ℝ,
      eventMass part2S1Mass (fun x : Part2S1Point => part2S1Pred k i x = r) > 0 →
        eventLabelMass part2S1Mass part2S1Eta
            (fun x : Part2S1Point => part2S1Pred k i x = r) =
          r * eventMass part2S1Mass
            (fun x : Part2S1Point => part2S1Pred k i x = r) := by
  intro i r _hpos
  by_cases hik : i = k
  · by_cases hr : r = part2S1KPred
    · subst r
      norm_num [eventMass, eventLabelMass, part2S1Pred, hik, part2S1Mass, part2S1Eta,
        part2S1KPred]
    · have hempty :
          eventMass part2S1Mass (fun x : Part2S1Point => part2S1Pred k i x = r) = 0 := by
        have hr' : (7 : ℝ) / 12 ≠ r := by
          intro h
          exact hr (by simpa [part2S1KPred] using h.symm)
        norm_num [eventMass, part2S1Pred, hik, hr', part2S1Mass, part2S1KPred]
      have hlabel :
          eventLabelMass part2S1Mass part2S1Eta
              (fun x : Part2S1Point => part2S1Pred k i x = r) = 0 := by
        have hr' : (7 : ℝ) / 12 ≠ r := by
          intro h
          exact hr (by simpa [part2S1KPred] using h.symm)
        norm_num [eventLabelMass, part2S1Pred, hik, hr', part2S1Mass, part2S1Eta,
          part2S1KPred]
      rw [hempty, hlabel, mul_zero]
  · by_cases hr0 : r = (1 : ℝ) / 4
    · subst r
      norm_num [eventMass, eventLabelMass, part2S1Pred, hik, part2S1Mass, part2S1Eta]
    · by_cases hr1 : r = (3 : ℝ) / 4
      · subst r
        norm_num [eventMass, eventLabelMass, part2S1Pred, hik, part2S1Mass, part2S1Eta]
      · have hempty :
            eventMass part2S1Mass (fun x : Part2S1Point => part2S1Pred k i x = r) = 0 := by
          have hr0' : (1 : ℝ) / 4 ≠ r := by
            intro h
            exact hr0 h.symm
          have hr1' : (3 : ℝ) / 4 ≠ r := by
            intro h
            exact hr1 h.symm
          norm_num [eventMass, part2S1Pred, hik, hr0', hr1', part2S1Mass, part2S1Eta]
        have hlabel :
            eventLabelMass part2S1Mass part2S1Eta
                (fun x : Part2S1Point => part2S1Pred k i x = r) = 0 := by
          have hr0' : (1 : ℝ) / 4 ≠ r := by
            intro h
            exact hr0 h.symm
          have hr1' : (3 : ℝ) / 4 ≠ r := by
            intro h
            exact hr1 h.symm
          norm_num [eventLabelMass, part2S1Pred, hik, hr0', hr1', part2S1Mass, part2S1Eta]
        rw [hempty, hlabel, mul_zero]

noncomputable def part2S1Setting {n : ℕ} (k : Fin n) : FiniteCollaborationSetting n where
  X := Part2S1Point
  mass := part2S1Mass
  mass_nonneg := part2S1Mass_nonneg
  mass_sum := part2S1Mass_sum
  eta := part2S1Eta
  eta_range := part2S1Eta_range
  pred := part2S1Pred k
  pred_range := part2S1Pred_range k
  calibrated := part2S1_calibrated k

theorem part2S1_profile_interior {n : ℕ} (k : Fin n) (x : Part2S1Point) :
    Interior (fun i : Fin n => part2S1Pred k i x) := by
  intro i
  by_cases hik : i = k
  · norm_num [part2S1Pred, hik, part2S1KPred]
  · cases x <;> norm_num [part2S1Pred, hik, part2S1Eta]

theorem part2S1_k_pred_ne_half {n : ℕ} (k : Fin n) (x : Part2S1Point) :
    part2S1Pred k k x ≠ (1 : ℝ) / 2 := by
  norm_num [part2S1Pred, part2S1KPred]

theorem part2S1_agentAccuracy_k {n : ℕ} (k : Fin n) :
    (part2S1Setting k).agentAccuracy k = (7 : ℝ) / 12 := by
  unfold FiniteCollaborationSetting.agentAccuracy
  change
    (∑ x : Part2S1Point,
      part2S1Mass x *
        pointAccuracy (roundProb (part2S1Pred k k x)) (part2S1Eta x)) = (7 : ℝ) / 12
  rw [Fintype.sum_bool]
  norm_num [part2S1Mass, part2S1Eta, part2S1Pred, part2S1KPred, pointAccuracy, roundProb]

theorem part2S1_agentAccuracy_ne {n : ℕ} {k i : Fin n} (hik : i ≠ k) :
    (part2S1Setting k).agentAccuracy i = (3 : ℝ) / 4 := by
  unfold FiniteCollaborationSetting.agentAccuracy
  change
    (∑ x : Part2S1Point,
      part2S1Mass x *
        pointAccuracy (roundProb (part2S1Pred k i x)) (part2S1Eta x)) = (3 : ℝ) / 4
  rw [Fintype.sum_bool]
  norm_num [part2S1Mass, part2S1Eta, part2S1Pred, hik, pointAccuracy, roundProb]

theorem part2S1_strategyAccuracy {n : ℕ} {C : CollaborationStrategy n} {k : Fin n}
    (hk : DefersAwayFromHalf C k) :
    (part2S1Setting k).strategyAccuracy C = (7 : ℝ) / 12 := by
  have hCfalse :
      C (fun i : Fin n => part2S1Pred k i false) = true := by
    have h := hk (fun i : Fin n => part2S1Pred k i false)
      (part2S1_profile_interior k false) (part2S1_k_pred_ne_half k false)
    have hround : roundProb (part2S1Pred k k false) = true := by
      norm_num [part2S1Pred, part2S1KPred, roundProb]
    simpa [hround] using h
  have hCtrue :
      C (fun i : Fin n => part2S1Pred k i true) = true := by
    have h := hk (fun i : Fin n => part2S1Pred k i true)
      (part2S1_profile_interior k true) (part2S1_k_pred_ne_half k true)
    have hround : roundProb (part2S1Pred k k true) = true := by
      norm_num [part2S1Pred, part2S1KPred, roundProb]
    simpa [hround] using h
  unfold FiniteCollaborationSetting.strategyAccuracy
  change
    (∑ x : Part2S1Point,
      part2S1Mass x *
        pointAccuracy (C (fun i : Fin n => part2S1Pred k i x)) (part2S1Eta x))
      = (7 : ℝ) / 12
  rw [Fintype.sum_bool]
  norm_num [part2S1Mass, part2S1Eta, hCfalse, hCtrue, pointAccuracy]

/-! ## Proposition 2 second auxiliary setting -/

abbrev Part2S2Point (n : ℕ) := Bool × Part1Point n

noncomputable def part2S2Denom {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  part1Denom true p + part1Denom false q

theorem part2S2Denom_pos {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) :
    0 < part2S2Denom p q := by
  exact add_pos (part1Denom_pos (b := true) hp) (part1Denom_pos (b := false) hq)

noncomputable def part2S2WeightP {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  part1Denom true p / part2S2Denom p q

noncomputable def part2S2WeightQ {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  part1Denom false q / part2S2Denom p q

noncomputable def part2S2Mass {n : ℕ} (p q : Fin n → ℝ) : Part2S2Point n → ℝ
  | (false, x) => part2S2WeightP p q * part1Mass true p x
  | (true, x) => part2S2WeightQ p q * part1Mass false q x

noncomputable def part2S2Eta {n : ℕ} : Part2S2Point n → ℝ
  | (false, x) => part1Eta true x
  | (true, x) => part1Eta false x

noncomputable def part2S2Pred {n : ℕ} (k : Fin n) (p q : Fin n → ℝ)
    (i : Fin n) : Part2S2Point n → ℝ
  | (false, x) =>
      if i = k then
        match x with
        | none => (1 : ℝ) / 2
        | some _ => part1Eta true x
      else part1Pred true p i x
  | (true, x) =>
      if i = k then
        match x with
        | none => (1 : ℝ) / 2
        | some _ => part1Eta false x
      else part1Pred false q i x

theorem part2S2WeightP_nonneg {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) : 0 ≤ part2S2WeightP p q := by
  exact div_nonneg (le_of_lt (part1Denom_pos (b := true) hp))
    (le_of_lt (part2S2Denom_pos hp hq))

theorem part2S2WeightQ_nonneg {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) : 0 ≤ part2S2WeightQ p q := by
  exact div_nonneg (le_of_lt (part1Denom_pos (b := false) hq))
    (le_of_lt (part2S2Denom_pos hp hq))

theorem part2S2WeightP_pos {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) : 0 < part2S2WeightP p q := by
  exact div_pos (part1Denom_pos (b := true) hp) (part2S2Denom_pos hp hq)

theorem part2S2WeightQ_pos {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) : 0 < part2S2WeightQ p q := by
  exact div_pos (part1Denom_pos (b := false) hq) (part2S2Denom_pos hp hq)

theorem part2S2Weight_sum {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) :
    part2S2WeightP p q + part2S2WeightQ p q = 1 := by
  unfold part2S2WeightP part2S2WeightQ part2S2Denom
  have hden : part1Denom true p + part1Denom false q ≠ 0 :=
    ne_of_gt (part2S2Denom_pos hp hq)
  field_simp [hden]

theorem part2S2Mass_nonneg {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) (x : Part2S2Point n) :
    0 ≤ part2S2Mass p q x := by
  rcases x with ⟨b, x⟩
  cases b
  · exact mul_nonneg (part2S2WeightP_nonneg hp hq) (part1Mass_nonneg hp x)
  · exact mul_nonneg (part2S2WeightQ_nonneg hp hq) (part1Mass_nonneg hq x)

theorem part2S2Mass_sum {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) :
    (∑ x : Part2S2Point n, part2S2Mass p q x) = 1 := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [part2S2Mass]
  rw [← Finset.mul_sum, ← Finset.mul_sum, part1Mass_sum hp, part1Mass_sum hq]
  simpa [mul_one, add_comm] using part2S2Weight_sum hp hq

theorem part2S2Eta_range {n : ℕ} (x : Part2S2Point n) :
    0 ≤ part2S2Eta x ∧ part2S2Eta x ≤ 1 := by
  rcases x with ⟨b, x⟩
  cases b <;> exact part1Eta_range _ x

theorem part2S2Pred_range {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) (k i : Fin n) (x : Part2S2Point n) :
    0 ≤ part2S2Pred k p q i x ∧ part2S2Pred k p q i x ≤ 1 := by
  rcases x with ⟨b, x⟩
  cases b
  · by_cases hik : i = k
    · cases x with
      | none => norm_num [part2S2Pred, hik]
      | some j => simpa [part2S2Pred, hik] using part1Eta_range true (some j)
    · simpa [part2S2Pred, hik] using part1Pred_range hp i x
  · by_cases hik : i = k
    · cases x with
      | none => norm_num [part2S2Pred, hik]
      | some j => simpa [part2S2Pred, hik] using part1Eta_range false (some j)
    · simpa [part2S2Pred, hik] using part1Pred_range hq i x

theorem part2S2_calibrated_ne {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) {k i : Fin n} (hik : i ≠ k) (r : ℝ) :
    eventLabelMass (part2S2Mass p q) part2S2Eta
        (fun x : Part2S2Point n => part2S2Pred k p q i x = r)
      =
    r * eventMass (part2S2Mass p q)
        (fun x : Part2S2Point n => part2S2Pred k p q i x = r) := by
  classical
  have hlabel :
      eventLabelMass (part2S2Mass p q) part2S2Eta
          (fun x : Part2S2Point n => part2S2Pred k p q i x = r)
        =
      part2S2WeightQ p q *
          eventLabelMass (part1Mass false q) (part1Eta false)
            (fun x : Part1Point n => part1Pred false q i x = r) +
        part2S2WeightP p q *
          eventLabelMass (part1Mass true p) (part1Eta true)
            (fun x : Part1Point n => part1Pred true p i x = r) := by
    unfold eventLabelMass
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    change
      (∑ x : Part1Point n,
          if part2S2Pred k p q i (true, x) = r
          then part2S2Mass p q (true, x) * part2S2Eta (true, x) else 0) +
        (∑ x : Part1Point n,
          if part2S2Pred k p q i (false, x) = r
          then part2S2Mass p q (false, x) * part2S2Eta (false, x) else 0)
        =
      part2S2WeightQ p q *
          (∑ x : Part1Point n,
            if part1Pred false q i x = r then part1Mass false q x * part1Eta false x else 0) +
        part2S2WeightP p q *
          (∑ x : Part1Point n,
            if part1Pred true p i x = r then part1Mass true p x * part1Eta true x else 0)
    congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x _hx
      by_cases hx : part1Pred false q i x = r
      · simp [part2S2Pred, part2S2Mass, part2S2Eta, hik, hx, mul_assoc]
      · simp [part2S2Pred, hik, hx]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x _hx
      by_cases hx : part1Pred true p i x = r
      · simp [part2S2Pred, part2S2Mass, part2S2Eta, hik, hx, mul_assoc]
      · simp [part2S2Pred, hik, hx]
  have hmass :
      eventMass (part2S2Mass p q)
          (fun x : Part2S2Point n => part2S2Pred k p q i x = r)
        =
      part2S2WeightQ p q *
          eventMass (part1Mass false q)
            (fun x : Part1Point n => part1Pred false q i x = r) +
        part2S2WeightP p q *
          eventMass (part1Mass true p)
            (fun x : Part1Point n => part1Pred true p i x = r) := by
    unfold eventMass
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    change
      (∑ x : Part1Point n,
          if part2S2Pred k p q i (true, x) = r
          then part2S2Mass p q (true, x) else 0) +
        (∑ x : Part1Point n,
          if part2S2Pred k p q i (false, x) = r
          then part2S2Mass p q (false, x) else 0)
        =
      part2S2WeightQ p q *
          (∑ x : Part1Point n,
            if part1Pred false q i x = r then part1Mass false q x else 0) +
        part2S2WeightP p q *
          (∑ x : Part1Point n,
            if part1Pred true p i x = r then part1Mass true p x else 0)
    congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x _hx
      by_cases hx : part1Pred false q i x = r
      · simp [part2S2Pred, part2S2Mass, hik, hx]
      · simp [part2S2Pred, hik, hx]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x _hx
      by_cases hx : part1Pred true p i x = r
      · simp [part2S2Pred, part2S2Mass, hik, hx]
      · simp [part2S2Pred, hik, hx]
  rw [hlabel, hmass]
  have hqcal := FiniteCollaborationSetting.calibrated_unconditional
    (part1Setting false q hq) i r
  have hpcal := FiniteCollaborationSetting.calibrated_unconditional
    (part1Setting true p hp) i r
  dsimp [part1Setting] at hqcal hpcal
  have hqcal' :
      part2S2WeightQ p q *
          eventLabelMass (part1Mass false q) (part1Eta false)
            (fun x : Part1Point n => part1Pred false q i x = r)
        =
      part2S2WeightQ p q *
          (r * eventMass (part1Mass false q)
            (fun x : Part1Point n => part1Pred false q i x = r)) := by
    exact congrArg (fun z => part2S2WeightQ p q * z) hqcal
  have hpcal' :
      part2S2WeightP p q *
          eventLabelMass (part1Mass true p) (part1Eta true)
            (fun x : Part1Point n => part1Pred true p i x = r)
        =
      part2S2WeightP p q *
          (r * eventMass (part1Mass true p)
            (fun x : Part1Point n => part1Pred true p i x = r)) := by
    exact congrArg (fun z => part2S2WeightP p q * z) hpcal
  change
      part2S2WeightQ p q *
          eventLabelMass (part1Mass false q) (part1Eta false)
            (fun x : Part1Point n => part1Pred false q i x = r) +
        part2S2WeightP p q *
          eventLabelMass (part1Mass true p) (part1Eta true)
            (fun x : Part1Point n => part1Pred true p i x = r)
      =
      r *
        (part2S2WeightQ p q *
            eventMass (part1Mass false q)
              (fun x : Part1Point n => part1Pred false q i x = r) +
          part2S2WeightP p q *
            eventMass (part1Mass true p)
              (fun x : Part1Point n => part1Pred true p i x = r))
  rw [hqcal', hpcal']
  ring

theorem part2S2_center_masses_equal {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) :
    part2S2Mass p q (true, (none : Part1Point n)) =
      part2S2Mass p q (false, (none : Part1Point n)) := by
  unfold part2S2Mass part2S2WeightP part2S2WeightQ part1Mass
  have hpden : part1Denom true p ≠ 0 := ne_of_gt (part1Denom_pos (b := true) hp)
  have hqden : part1Denom false q ≠ 0 := ne_of_gt (part1Denom_pos (b := false) hq)
  have hden : part2S2Denom p q ≠ 0 := ne_of_gt (part2S2Denom_pos hp hq)
  field_simp [hpden, hqden, hden]

theorem part2S2_calibrated_k {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) (k : Fin n) (r : ℝ) :
    eventLabelMass (part2S2Mass p q) part2S2Eta
        (fun x : Part2S2Point n => part2S2Pred k p q k x = r)
      =
    r * eventMass (part2S2Mass p q)
        (fun x : Part2S2Point n => part2S2Pred k p q k x = r) := by
  classical
  by_cases hrh : r = (1 : ℝ) / 2
  · subst r
    unfold eventLabelMass eventMass
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
    simp [part2S2Pred, part2S2Eta, part1Eta, labelReal]
    have hcenter := part2S2_center_masses_equal (p := p) (q := q) hp hq
    nlinarith
  · by_cases hr1 : r = (1 : ℝ)
    · subst r
      unfold eventLabelMass eventMass
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
      simp [part2S2Pred, part2S2Eta, part1Eta, labelReal]
    · by_cases hr0 : r = (0 : ℝ)
      · subst r
        unfold eventLabelMass eventMass
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
        simp [part2S2Pred, part2S2Eta, part1Eta, labelReal]
      · have hrh' : (1 : ℝ) / 2 ≠ r := by
          intro h
          exact hrh h.symm
        have hr1' : (1 : ℝ) ≠ r := by
          intro h
          exact hr1 h.symm
        have hr0' : (0 : ℝ) ≠ r := by
          intro h
          exact hr0 h.symm
        have hrh_inv : (2⁻¹ : ℝ) ≠ r := by
          norm_num
          exact hrh'
        unfold eventLabelMass eventMass
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]
        simp [part2S2Pred, part2S2Eta, part1Eta, labelReal, hrh_inv, hr1', hr0']

theorem part2S2_calibrated {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) (k : Fin n) :
    ∀ i : Fin n, ∀ r : ℝ,
      eventMass (part2S2Mass p q) (fun x : Part2S2Point n => part2S2Pred k p q i x = r) > 0 →
        eventLabelMass (part2S2Mass p q) part2S2Eta
            (fun x : Part2S2Point n => part2S2Pred k p q i x = r) =
          r * eventMass (part2S2Mass p q)
            (fun x : Part2S2Point n => part2S2Pred k p q i x = r) := by
  intro i r _hpos
  by_cases hik : i = k
  · subst i
    exact part2S2_calibrated_k hp hq k r
  · exact part2S2_calibrated_ne hp hq hik r

noncomputable def part2S2Setting {n : ℕ} (k : Fin n) (p q : Fin n → ℝ)
    (hp : Interior p) (hq : Interior q) : FiniteCollaborationSetting n where
  X := Part2S2Point n
  mass := part2S2Mass p q
  mass_nonneg := part2S2Mass_nonneg hp hq
  mass_sum := part2S2Mass_sum hp hq
  eta := part2S2Eta
  eta_range := part2S2Eta_range
  pred := part2S2Pred k p q
  pred_range := part2S2Pred_range hp hq k
  calibrated := part2S2_calibrated hp hq k

theorem part2S2_profile_false_none {n : ℕ} {k : Fin n} {p q : Fin n → ℝ}
    (hpk : p k = (1 : ℝ) / 2) :
    (fun i : Fin n => part2S2Pred k p q i (false, (none : Part1Point n))) = p := by
  funext i
  by_cases hik : i = k
  · subst i
    simp [part2S2Pred, hpk]
  · simp [part2S2Pred, part1Pred, hik]

theorem part2S2_profile_true_none {n : ℕ} {k : Fin n} {p q : Fin n → ℝ}
    (hqk : q k = (1 : ℝ) / 2) :
    (fun i : Fin n => part2S2Pred k p q i (true, (none : Part1Point n))) = q := by
  funext i
  by_cases hik : i = k
  · subst i
    simp [part2S2Pred, hqk]
  · simp [part2S2Pred, part1Pred, hik]

theorem part2S2Mass_true_none_pos {n : ℕ} {p q : Fin n → ℝ}
    (hp : Interior p) (hq : Interior q) :
    0 < part2S2Mass p q (true, (none : Part1Point n)) := by
  exact mul_pos (part2S2WeightQ_pos hp hq) (part1Mass_none_pos hq)

theorem part2S2_strategyAccuracy_lt_agentK {n : ℕ} {C : CollaborationStrategy n}
    {k : Fin n} {p q : Fin n → ℝ} (hp : Interior p) (hq : Interior q)
    (hpk : p k = (1 : ℝ) / 2) (hqk : q k = (1 : ℝ) / 2)
    (hCp : C p = true) (hCq : C q = false) :
    (part2S2Setting k p q hp hq).strategyAccuracy C <
      (part2S2Setting k p q hp hq).agentAccuracy k := by
  classical
  unfold FiniteCollaborationSetting.strategyAccuracy FiniteCollaborationSetting.agentAccuracy
  change
    (∑ x : Part2S2Point n,
      part2S2Mass p q x *
        pointAccuracy
          (FiniteCollaborationSetting.strategyClassifier C (part2S2Setting k p q hp hq) x)
          (part2S2Eta x))
      <
    (∑ x : Part2S2Point n,
      part2S2Mass p q x *
        pointAccuracy
          (FiniteCollaborationSetting.agentClassifier (part2S2Setting k p q hp hq) k x)
          (part2S2Eta x))
  refine Finset.sum_lt_sum ?hle ?hstrict
  · intro x _hx
    rcases x with ⟨b, x⟩
    cases b
    · cases x with
      | none =>
          have hprof := part2S2_profile_false_none (k := k) (p := p) (q := q) hpk
          have hCcenter :
              C (fun i : Fin n => part2S2Pred k p q i (false, (none : Part1Point n))) = true := by
            rw [hprof]
            exact hCp
          have hCcenter' :
              C (fun i : Fin n => if i = k then 2⁻¹ else part1Pred true p i none) = true := by
            simpa [part2S2Pred] using hCcenter
          simp [FiniteCollaborationSetting.strategyClassifier,
            FiniteCollaborationSetting.agentClassifier, part2S2Setting, part2S2Pred,
            part2S2Eta, part1Eta, labelReal, hCcenter', pointAccuracy, roundProb]
      | some j =>
          have hacc :
                pointAccuracy
                    (FiniteCollaborationSetting.strategyClassifier C
                      (part2S2Setting k p q hp hq) (false, some j))
                    (part2S2Eta ((false, some j) : Part2S2Point n)) ≤ 1 :=
              pointAccuracy_le_one (part2S2Eta_range ((false, some j) : Part2S2Point n))
          simpa [FiniteCollaborationSetting.agentClassifier, part2S2Setting, part2S2Pred,
            part2S2Eta, part1Eta, labelReal, pointAccuracy, roundProb_one] using
              mul_le_mul_of_nonneg_left hacc
                (part2S2Mass_nonneg hp hq ((false, some j) : Part2S2Point n))
    · cases x with
      | none =>
          have hprof := part2S2_profile_true_none (k := k) (p := p) (q := q) hqk
          have hmass_nonneg := part2S2Mass_nonneg hp hq ((true, none) : Part2S2Point n)
          have hCcenter :
              C (fun i : Fin n => part2S2Pred k p q i (true, (none : Part1Point n))) = false := by
            rw [hprof]
            exact hCq
          have hCcenter' :
              C (fun i : Fin n => if i = k then 2⁻¹ else part1Pred false q i none) = false := by
            simpa [part2S2Pred] using hCcenter
          simp [FiniteCollaborationSetting.strategyClassifier,
            FiniteCollaborationSetting.agentClassifier, part2S2Setting, part2S2Pred,
            part2S2Eta, part1Eta, labelReal, hCcenter', pointAccuracy, roundProb,
            hmass_nonneg]
      | some j =>
          have hacc :
                pointAccuracy
                    (FiniteCollaborationSetting.strategyClassifier C
                      (part2S2Setting k p q hp hq) (true, some j))
                    (part2S2Eta ((true, some j) : Part2S2Point n)) ≤ 1 :=
              pointAccuracy_le_one (part2S2Eta_range ((true, some j) : Part2S2Point n))
          simpa [FiniteCollaborationSetting.agentClassifier, part2S2Setting, part2S2Pred,
            part2S2Eta, part1Eta, labelReal, pointAccuracy, roundProb_zero] using
              mul_le_mul_of_nonneg_left hacc
                (part2S2Mass_nonneg hp hq ((true, some j) : Part2S2Point n))
  · refine ⟨(true, (none : Part1Point n)), Finset.mem_univ _, ?_⟩
    have hprof := part2S2_profile_true_none (k := k) (p := p) (q := q) hqk
    have hCcenter :
        C (fun i : Fin n => part2S2Pred k p q i (true, (none : Part1Point n))) = false := by
      rw [hprof]
      exact hCq
    have hCcenter' :
        C (fun i : Fin n => if i = k then 2⁻¹ else part1Pred false q i none) = false := by
      simpa [part2S2Pred] using hCcenter
    have hmass_pos := part2S2Mass_true_none_pos (p := p) (q := q) hp hq
    simpa [FiniteCollaborationSetting.strategyClassifier,
      FiniteCollaborationSetting.agentClassifier, part2S2Setting, part2S2Pred,
      part2S2Eta, part1Eta, labelReal, hCcenter', pointAccuracy, roundProb] using
      hmass_pos

theorem reliableFinite_constant_on_half {n : ℕ} [Nonempty (Fin n)]
    {C : CollaborationStrategy n} {k : Fin n}
    (hrel : ReliableFinite C) (hk : DefersAwayFromHalf C k) :
    ∃ α : Label, ConstantOnHalfSlice C k α := by
  classical
  by_contra hnone
  have hnot_false : ¬ ConstantOnHalfSlice C k false := by
    intro h
    exact hnone ⟨false, h⟩
  have hnot_true : ¬ ConstantOnHalfSlice C k true := by
    intro h
    exact hnone ⟨true, h⟩
  have hfalse_witness :
      ∃ p : Fin n → ℝ, Interior p ∧ p k = (1 : ℝ) / 2 ∧ C p ≠ false := by
    simpa [ConstantOnHalfSlice] using hnot_false
  have htrue_witness :
      ∃ q : Fin n → ℝ, Interior q ∧ q k = (1 : ℝ) / 2 ∧ C q ≠ true := by
    simpa [ConstantOnHalfSlice] using hnot_true
  rcases hfalse_witness with ⟨p, hp, hpk, hCp_ne⟩
  rcases htrue_witness with ⟨q, hq, hqk, hCq_ne⟩
  have hCp : C p = true := by
    cases h : C p <;> simp [h] at hCp_ne ⊢
  have hCq : C q = false := by
    cases h : C q <;> simp [h] at hCq_ne ⊢
  let S1 : FiniteCollaborationSetting n := part2S1Setting k
  let S2 : FiniteCollaborationSetting n := part2S2Setting k p q hp hq
  let T : Fin 2 → FiniteCollaborationSetting n := fun r =>
    if r = 0 then S1 else S2
  let w : Fin 2 → ℝ := fun r => if r = 0 then (7 : ℝ) / 8 else (1 : ℝ) / 8
  have hw_nonneg : ∀ r : Fin 2, 0 ≤ w r := by
    intro r
    fin_cases r <;> norm_num [w]
  have hw_sum : ∑ r : Fin 2, w r = 1 := by
    norm_num [w]
  let Smix := FiniteCollaborationSetting.mix T w hw_nonneg hw_sum
  have hstrict : ∀ i : Fin n, Smix.strategyAccuracy C < Smix.agentAccuracy i := by
    intro i
    dsimp [Smix]
    rw [FiniteCollaborationSetting.strategyAccuracy_mix T w hw_nonneg hw_sum C,
      FiniteCollaborationSetting.agentAccuracy_mix T w hw_nonneg hw_sum i]
    by_cases hik : i = k
    · subst i
      have hS1s : S1.strategyAccuracy C = (7 : ℝ) / 12 := by
        exact part2S1_strategyAccuracy (C := C) (k := k) hk
      have hS1a : S1.agentAccuracy k = (7 : ℝ) / 12 := by
        exact part2S1_agentAccuracy_k k
      have hS2 : S2.strategyAccuracy C < S2.agentAccuracy k := by
        exact part2S2_strategyAccuracy_lt_agentK (C := C) hp hq hpk hqk hCp hCq
      norm_num [T, w, S1, S2, hS1s, hS1a]
      nlinarith
    · have hS1s : S1.strategyAccuracy C = (7 : ℝ) / 12 := by
        exact part2S1_strategyAccuracy (C := C) (k := k) hk
      have hS1a : S1.agentAccuracy i = (3 : ℝ) / 4 := by
        exact part2S1_agentAccuracy_ne (k := k) (i := i) hik
      have hS2s_le : S2.strategyAccuracy C ≤ 1 :=
        (FiniteCollaborationSetting.strategyAccuracy_range S2 C).2
      have hS2a_nonneg : 0 ≤ S2.agentAccuracy i :=
        (FiniteCollaborationSetting.agentAccuracy_range S2 i).1
      norm_num [T, w, S1, S2, hS1s, hS1a]
      nlinarith
  rcases hrel Smix with ⟨i, hi⟩
  exact (not_lt_of_ge hi) (hstrict i)

/-- Main finite no-free-lunch theorem proved from the two adversarial constructions. -/
theorem main_no_free_lunch_finite {n : ℕ} [Nonempty (Fin n)]
    (C : CollaborationStrategy n) :
    ReliableFinite C → NonCollaborative C := by
  intro hrel
  rcases reliableFinite_exists_defers_away (C := C) hrel with ⟨k, hk⟩
  rcases reliableFinite_constant_on_half (C := C) hrel hk with ⟨α, hα⟩
  exact ⟨k, α, hk, hα⟩

/--
Main source-style no-free-lunch theorem.  The proof restricts the paper's
all-setting reliability premise to the finite adversarial settings constructed
in the source proof.
-/
theorem main_no_free_lunch {n : ℕ} [Nonempty (Fin n)]
    (C : CollaborationStrategy n) :
    Reliable C → NonCollaborative C := by
  intro hrel
  exact main_no_free_lunch_finite C (reliableFinite_of_reliable hrel)

/--
Pure proof assembly for the main theorem from the two source propositions.
This theorem has no mathematical content beyond combining the two propositions;
the hard work is proving `part1` and `part2` for the finite collaboration
settings constructed below.
-/
theorem main_no_free_lunch_from_parts {n : ℕ} [Nonempty (Fin n)]
    (C : CollaborationStrategy n) (Reliable : Prop)
    (part1 : Reliable → ∃ k : Fin n, DefersAwayFromHalf C k)
    (part2 : ∀ k : Fin n, Reliable → DefersAwayFromHalf C k →
      ∃ α : Label, ConstantOnHalfSlice C k α) :
    Reliable → NonCollaborative C := by
  intro hrel
  rcases part1 hrel with ⟨k, hk⟩
  rcases part2 k hrel hk with ⟨α, hα⟩
  exact ⟨k, α, hk, hα⟩

end PKG25NoFreeLunch
