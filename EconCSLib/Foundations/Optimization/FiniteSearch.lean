import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import EconCSLib.Foundations.Optimization.Certificate

namespace EconCSLib
namespace Optimization

/-!
# Finite Feasible Search

Reusable existence lemmas for optimization over finite feasible regions and
finite encodings of feasible regions.

## Main declarations

- `exists_isMaximizerOn_of_fintype_subtype`
- `exists_isMinimizerOn_of_fintype_subtype`
- `exists_isMaximizerOn_of_finite`
- `exists_isMinimizerOn_of_finite`
- `exists_isMaximizerOn_of_finite_code`
- `exists_isMinimizerOn_of_finite_code`
-/

/-- A real objective has a maximizer over any nonempty finite feasible subtype. -/
theorem exists_isMaximizerOn_of_fintype_subtype
    {α : Type*} (feasible : α → Prop) [Fintype {x : α // feasible x}]
    [Nonempty {x : α // feasible x}] (objective : α → ℝ) :
    ∃ opt : α, IsMaximizerOn feasible objective opt := by
  classical
  let defaultFeasible : {x : α // feasible x} := Classical.choice inferInstance
  have hnonempty : (Finset.univ : Finset {x : α // feasible x}).Nonempty :=
    ⟨defaultFeasible, by simp⟩
  obtain ⟨opt, _hmem, hopt⟩ :=
    Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset {x : α // feasible x}))
      (H := hnonempty) (f := fun x : {x : α // feasible x} => objective x.1)
  refine ⟨opt.1, ?_⟩
  constructor
  · exact opt.2
  · intro y hy
    have hle_sub :
        (fun x : {x : α // feasible x} => objective x.1) ⟨y, hy⟩ ≤
          (Finset.univ : Finset {x : α // feasible x}).sup' hnonempty
            (fun x : {x : α // feasible x} => objective x.1) :=
      Finset.le_sup'
        (s := (Finset.univ : Finset {x : α // feasible x}))
        (f := fun x : {x : α // feasible x} => objective x.1)
        (by simp)
    have hle :
        objective y ≤
          (Finset.univ : Finset {x : α // feasible x}).sup' hnonempty
            (fun x : {x : α // feasible x} => objective x.1) := by
      simpa using hle_sub
    rwa [hopt] at hle

/-- A real objective has a minimizer over any nonempty finite feasible subtype. -/
theorem exists_isMinimizerOn_of_fintype_subtype
    {α : Type*} (feasible : α → Prop) [Fintype {x : α // feasible x}]
    [Nonempty {x : α // feasible x}] (objective : α → ℝ) :
    ∃ opt : α, IsMinimizerOn feasible objective opt := by
  classical
  obtain ⟨opt, hopt⟩ :=
    exists_isMaximizerOn_of_fintype_subtype feasible (fun x => -objective x)
  refine ⟨opt, ?_⟩
  constructor
  · exact hopt.isFeasible
  · intro y hy
    exact neg_le_neg_iff.mp (hopt.le hy)

/-- A real objective has a maximizer over any nonempty decidable finite feasible set. -/
theorem exists_isMaximizerOn_of_finite
    {α : Type*} [Fintype α] (feasible : α → Prop) [DecidablePred feasible]
    (objective : α → ℝ) (hnonempty : ∃ x, feasible x) :
    ∃ opt : α, IsMaximizerOn feasible objective opt := by
  classical
  haveI : Nonempty {x : α // feasible x} :=
    ⟨⟨Classical.choose hnonempty, Classical.choose_spec hnonempty⟩⟩
  exact exists_isMaximizerOn_of_fintype_subtype feasible objective

/-- A real objective has a minimizer over any nonempty decidable finite feasible set. -/
theorem exists_isMinimizerOn_of_finite
    {α : Type*} [Fintype α] (feasible : α → Prop) [DecidablePred feasible]
    (objective : α → ℝ) (hnonempty : ∃ x, feasible x) :
    ∃ opt : α, IsMinimizerOn feasible objective opt := by
  classical
  haveI : Nonempty {x : α // feasible x} :=
    ⟨⟨Classical.choose hnonempty, Classical.choose_spec hnonempty⟩⟩
  exact exists_isMinimizerOn_of_fintype_subtype feasible objective

/--
Finite-code maximizer existence.

Use this when the feasible objects are not themselves convenient finite
data, but every feasible object is represented by a feasible finite code.
-/
theorem exists_isMaximizerOn_of_finite_code
    {Code α : Type*} [Fintype Code]
    (codeFeasible : Code → Prop) [DecidablePred codeFeasible]
    (decode : Code → α) (feasible : α → Prop) (objective : α → ℝ)
    (hdecode_feasible : ∀ c, codeFeasible c → feasible (decode c))
    (hcover : ∀ x, feasible x → ∃ c, codeFeasible c ∧ decode c = x)
    (hnonempty : ∃ x, feasible x) :
    ∃ opt : α, IsMaximizerOn feasible objective opt := by
  classical
  have hcode_nonempty : ∃ c, codeFeasible c := by
    rcases hnonempty with ⟨x, hx⟩
    rcases hcover x hx with ⟨c, hc, _⟩
    exact ⟨c, hc⟩
  obtain ⟨copt, hcopt⟩ :=
    exists_isMaximizerOn_of_finite codeFeasible
      (fun c => objective (decode c)) hcode_nonempty
  refine ⟨decode copt, ?_⟩
  constructor
  · exact hdecode_feasible copt hcopt.isFeasible
  · intro y hy
    rcases hcover y hy with ⟨c, hc, rfl⟩
    exact hcopt.le hc

/--
Finite-code minimizer existence.

This is the minimization analogue of `exists_isMaximizerOn_of_finite_code`.
-/
theorem exists_isMinimizerOn_of_finite_code
    {Code α : Type*} [Fintype Code]
    (codeFeasible : Code → Prop) [DecidablePred codeFeasible]
    (decode : Code → α) (feasible : α → Prop) (objective : α → ℝ)
    (hdecode_feasible : ∀ c, codeFeasible c → feasible (decode c))
    (hcover : ∀ x, feasible x → ∃ c, codeFeasible c ∧ decode c = x)
    (hnonempty : ∃ x, feasible x) :
    ∃ opt : α, IsMinimizerOn feasible objective opt := by
  classical
  have hcode_nonempty : ∃ c, codeFeasible c := by
    rcases hnonempty with ⟨x, hx⟩
    rcases hcover x hx with ⟨c, hc, _⟩
    exact ⟨c, hc⟩
  obtain ⟨copt, hcopt⟩ :=
    exists_isMinimizerOn_of_finite codeFeasible
      (fun c => objective (decode c)) hcode_nonempty
  refine ⟨decode copt, ?_⟩
  constructor
  · exact hdecode_feasible copt hcopt.isFeasible
  · intro y hy
    rcases hcover y hy with ⟨c, hc, rfl⟩
    exact hcopt.le hc

end Optimization
end EconCSLib
