import EconCSLib.Foundations.Probability.FiniteExpectation

open scoped BigOperators

namespace EconCSLib

/-!
# Independent Products of Finite PMFs

Small reusable constructors for independent products of two finite PMFs with
possibly different sample spaces.
-/

/-- Independent product PMF on `α × β`. -/
noncomputable def pmfProd {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (ν : PMF β) : PMF (α × β) :=
  PMF.ofFintype (fun p : α × β => μ p.1 * ν p.2) (by
    classical
    have hμ : ∑ a : α, μ a = 1 := by
      rw [← PMF.tsum_coe μ, tsum_fintype]
    have hν : ∑ b : β, ν b = 1 := by
      rw [← PMF.tsum_coe ν, tsum_fintype]
    calc
      ∑ p : α × β, μ p.1 * ν p.2
          = ∑ a : α, ∑ b : β, μ a * ν b := by
            rw [Fintype.sum_prod_type]
      _ = ∑ a : α, μ a * (∑ b : β, ν b) := by
            simp [Finset.mul_sum]
      _ = 1 := by
            simp [hμ, hν])

/--
Independent product PMF over a finite dependent family of coordinate spaces.
At coordinate `i`, the draw has law `μ i`.
-/
noncomputable def pmfPi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i : ι, Fintype (α i)]
    (μ : ∀ i : ι, PMF (α i)) : PMF ((i : ι) → α i) :=
  PMF.ofFintype (fun f : (i : ι) → α i => ∏ i : ι, μ i (f i)) (by
    classical
    have hcoord : ∀ i : ι, ∑ a : α i, μ i a = 1 := by
      intro i
      rw [← PMF.tsum_coe (μ i), tsum_fintype]
    calc
      ∑ f : ((i : ι) → α i), ∏ i : ι, μ i (f i)
          = ∑ f ∈ Fintype.piFinset
              (fun i : ι => (Finset.univ : Finset (α i))),
              ∏ i : ι, μ i (f i) := by
            simp
      _ = ∏ i : ι, ∑ a ∈ (Finset.univ : Finset (α i)), μ i a := by
            symm
            exact Finset.prod_univ_sum
              (t := fun i : ι => (Finset.univ : Finset (α i)))
              (f := fun i a => μ i a)
      _ = 1 := by simp [hcoord])

@[simp]
theorem pmfProd_apply {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (ν : PMF β) (p : α × β) :
    pmfProd μ ν p = μ p.1 * ν p.2 := by
  simp [pmfProd]

@[simp]
theorem pmfPi_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i : ι, Fintype (α i)]
    (μ : ∀ i : ι, PMF (α i)) (f : (i : ι) → α i) :
    pmfPi μ f = ∏ i : ι, μ i (f i) := by
  simp [pmfPi]

@[simp]
theorem pmfProd_apply_toReal {α β : Type*} [Fintype α] [Fintype β]
    (μ : PMF α) (ν : PMF β) (p : α × β) :
    (pmfProd μ ν p).toReal = (μ p.1).toReal * (ν p.2).toReal := by
  rw [pmfProd_apply]
  exact ENNReal.toReal_mul

@[simp]
theorem pmfPi_apply_toReal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i : ι, Fintype (α i)]
    (μ : ∀ i : ι, PMF (α i)) (f : (i : ι) → α i) :
    (pmfPi μ f).toReal = ∏ i : ι, (μ i (f i)).toReal := by
  rw [pmfPi_apply]
  simp

/--
Split a same-codomain finite function into two distinguished coordinates and
the remaining coordinates.
-/
def twoCoordFunEquivProdRest {ι α : Type*} [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) :
    (ι → α) ≃ (α × α) × ({k : ι // k ≠ i ∧ k ≠ j} → α) where
  toFun f := ((f i, f j), fun k => f k.1)
  invFun x k :=
    if hi : k = i then x.1.1
    else if hj : k = j then x.1.2
    else x.2 ⟨k, hi, hj⟩
  left_inv f := by
    funext k
    by_cases hi : k = i
    · subst hi
      simp
    · by_cases hj : k = j
      · subst hj
        simp [hi]
      · simp [hi, hj]
  right_inv x := by
    apply Prod.ext
    · apply Prod.ext
      · simp
      · simp [Ne.symm hij]
    · funext k
      simp [k.2.1, k.2.2]

/--
Under a finite independent product with same-codomain coordinate laws, the
two-coordinate marginal expectation is the pair-product expectation.
-/
theorem pmfExp_pmfPi_twoCoord_eq_pairExp
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : ι → PMF α) {i j : ι} (hij : i ≠ j)
    (F : α → α → ℝ) :
    pmfExp (pmfPi (fun k : ι => μ k)) (fun f : ι → α => F (f i) (f j)) =
      pmfPairExp (μ i) (μ j) F := by
  classical
  let Rest := {k : ι // k ≠ i ∧ k ≠ j}
  let e := twoCoordFunEquivProdRest (α := α) i j hij
  have hrest_mass :
      ∑ rest : Rest → α, ∏ k : Rest, (μ k.1 (rest k)).toReal = 1 := by
    have hcoord : ∀ k : Rest, ∑ a : α, (μ k.1 a).toReal = 1 := by
      intro k
      exact pmfToRealSum (μ k.1)
    calc
      ∑ rest : Rest → α, ∏ k : Rest, (μ k.1 (rest k)).toReal
          = ∏ k : Rest, ∑ a : α, (μ k.1 a).toReal := by
            symm
            simpa using
              (Finset.prod_univ_sum
                (t := fun _k : Rest => (Finset.univ : Finset α))
                (f := fun k a => (μ k.1 a).toReal))
      _ = 1 := by simp [hcoord]
  have hprod_split :
      ∀ x : (α × α) × (Rest → α),
        (∏ k : ι, (μ k ((e.symm x) k)).toReal) =
          (μ i x.1.1).toReal * (μ j x.1.2).toReal *
            ∏ k : Rest, (μ k.1 (x.2 k)).toReal := by
    intro x
    let g : ι → ℝ := fun k => (μ k ((e.symm x) k)).toReal
    have hi_eval : g i = (μ i x.1.1).toReal := by
      simp [g, e, twoCoordFunEquivProdRest]
    have hj_eval : g j = (μ j x.1.2).toReal := by
      simp [g, e, twoCoordFunEquivProdRest, Ne.symm hij]
    have hrest :
        (∏ k ∈ ({i}ᶜ : Finset ι) \ {j}, g k) =
          ∏ k : Rest, (μ k.1 (x.2 k)).toReal := by
      rw [Finset.prod_subtype
        (s := ({i}ᶜ : Finset ι) \ {j})
        (p := fun k : ι => k ≠ i ∧ k ≠ j)]
      · refine Finset.prod_congr rfl ?_
        intro k _
        simp [g, e, twoCoordFunEquivProdRest, k.2.1, k.2.2]
      · intro k
        simp
    calc
      ∏ k : ι, (μ k ((e.symm x) k)).toReal
          = ∏ k : ι, g k := rfl
      _ = g i * ∏ k ∈ ({i}ᶜ : Finset ι), g k := by
            rw [Fintype.prod_eq_mul_prod_compl]
      _ = g i * (g j * ∏ k ∈ ({i}ᶜ : Finset ι) \ {j}, g k) := by
            congr 1
            rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem]
            simp [hij.symm]
      _ = (μ i x.1.1).toReal * (μ j x.1.2).toReal *
            ∏ k : Rest, (μ k.1 (x.2 k)).toReal := by
            rw [hi_eval, hj_eval, hrest]
            ring
  unfold pmfPairExp pmfExp
  calc
    ∑ f : ι → α,
        (pmfPi (fun k : ι => μ k) f).toReal * F (f i) (f j)
        =
        ∑ x : (α × α) × (Rest → α),
          (pmfPi (fun k : ι => μ k) (e.symm x)).toReal *
            F ((e.symm x) i) ((e.symm x) j) := by
          simpa [e] using
            (Equiv.sum_comp e.symm
              (fun f : ι → α =>
                (pmfPi (fun k : ι => μ k) f).toReal * F (f i) (f j))).symm
    _ =
        ∑ x : (α × α) × (Rest → α),
          ((μ i x.1.1).toReal * (μ j x.1.2).toReal *
              ∏ k : Rest, (μ k.1 (x.2 k)).toReal) *
            F x.1.1 x.1.2 := by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [pmfPi_apply_toReal, hprod_split x]
          simp [e, twoCoordFunEquivProdRest, Ne.symm hij]
    _ =
        ∑ pair : α × α, ∑ rest : Rest → α,
          ((μ i pair.1).toReal * (μ j pair.2).toReal *
              ∏ k : Rest, (μ k.1 (rest k)).toReal) *
            F pair.1 pair.2 := by
          simpa [Finset.univ_product_univ] using
            (Finset.sum_product'
              (s := (Finset.univ : Finset (α × α)))
              (t := (Finset.univ : Finset (Rest → α)))
              (f := fun pair rest =>
                ((μ i pair.1).toReal * (μ j pair.2).toReal *
                    ∏ k : Rest, (μ k.1 (rest k)).toReal) *
                  F pair.1 pair.2))
    _ =
        ∑ pair : α × α,
          ((μ i pair.1).toReal * (μ j pair.2).toReal) *
            F pair.1 pair.2 := by
          refine Finset.sum_congr rfl ?_
          intro pair _
          calc
            ∑ rest : Rest → α,
              ((μ i pair.1).toReal * (μ j pair.2).toReal *
                  ∏ k : Rest, (μ k.1 (rest k)).toReal) *
                F pair.1 pair.2
                =
                ((μ i pair.1).toReal * (μ j pair.2).toReal *
                    F pair.1 pair.2) *
                  ∑ rest : Rest → α,
                    ∏ k : Rest, (μ k.1 (rest k)).toReal := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro rest _
                  ring
            _ = ((μ i pair.1).toReal * (μ j pair.2).toReal) *
                  F pair.1 pair.2 := by
                  rw [hrest_mass]
                  ring
    _ =
        ∑ a : α, (μ i a).toReal *
          ∑ b : α, (μ j b).toReal * F a b := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro b _
          ring

/-- Expectations under `pmfProd` are independent pair expectations. -/
theorem pmfExp_pmfProd_eq_pairExp {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (f : α × β → ℝ) :
    pmfExp (pmfProd μ ν) f =
      pmfPairExp μ ν (fun a b => f (a, b)) := by
  classical
  simp [pmfExp, pmfPairExp]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro b _
  ring

/--
The two-coordinate event marginal of a same-codomain finite independent product
is the independent pair-product event probability.
-/
theorem pmfProb_pmfPi_twoCoord_eq_pmfProd
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : ι → PMF α) {i j : ι} (hij : i ≠ j)
    (p : α → α → Prop) [DecidableRel p] :
    pmfProb (pmfPi (fun k : ι => μ k))
        (fun f : ι → α => p (f i) (f j)) =
      pmfProb (pmfProd (μ i) (μ j))
        (fun x : α × α => p x.1 x.2) := by
  classical
  unfold pmfProb
  change
    pmfExp (pmfPi (fun k : ι => μ k))
        (fun f : ι → α => if p (f i) (f j) then (1 : ℝ) else 0) =
      pmfExp (pmfProd (μ i) (μ j))
        (fun x : α × α => if p x.1 x.2 then (1 : ℝ) else 0)
  rw [pmfExp_pmfPi_twoCoord_eq_pairExp
    (μ := μ) (i := i) (j := j) hij
    (F := fun a b => if p a b then (1 : ℝ) else 0)]
  rw [pmfExp_pmfProd_eq_pairExp]

/--
Split a dependent finite function into two distinguished coordinates and the
remaining dependent coordinates.
-/
def twoCoordDFunEquivProdRest {ι : Type*} [DecidableEq ι]
    {α : ι → Type*} (i j : ι) (hij : i ≠ j) :
    ((k : ι) → α k) ≃
      (α i × α j) ×
        ((k : {k : ι // k ≠ i ∧ k ≠ j}) → α k.1) where
  toFun f := ((f i, f j), fun k => f k.1)
  invFun x k :=
    if hi : k = i then by
      subst hi
      exact x.1.1
    else if hj : k = j then by
      subst hj
      exact x.1.2
    else x.2 ⟨k, hi, hj⟩
  left_inv f := by
    funext k
    by_cases hi : k = i
    · subst hi
      simp
    · by_cases hj : k = j
      · subst hj
        simp [hi]
      · simp [hi, hj]
  right_inv x := by
    apply Prod.ext
    · apply Prod.ext
      · simp
      · simp [hij.symm]
    · funext k
      simp [k.2.1, k.2.2]

/--
Under a finite independent dependent product, the two-coordinate marginal
expectation is the corresponding pair-product expectation.
-/
theorem pmfExp_pmfPi_twoCoord_eq_pairExp_dependent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ k : ι, Fintype (α k)]
    [∀ k : ι, DecidableEq (α k)]
    (μ : ∀ k : ι, PMF (α k)) {i j : ι} (hij : i ≠ j)
    (F : α i → α j → ℝ) :
    pmfExp (pmfPi μ) (fun f : (k : ι) → α k => F (f i) (f j)) =
      pmfPairExp (μ i) (μ j) F := by
  classical
  let Rest := {k : ι // k ≠ i ∧ k ≠ j}
  let e := twoCoordDFunEquivProdRest (α := α) i j hij
  have hrest_mass :
      ∑ rest : ((k : Rest) → α k.1),
          ∏ k : Rest, (μ k.1 (rest k)).toReal = 1 := by
    have hcoord : ∀ k : Rest, ∑ a : α k.1, (μ k.1 a).toReal = 1 := by
      intro k
      exact pmfToRealSum (μ k.1)
    calc
      ∑ rest : ((k : Rest) → α k.1),
          ∏ k : Rest, (μ k.1 (rest k)).toReal
          = ∏ k : Rest, ∑ a : α k.1, (μ k.1 a).toReal := by
            symm
            simpa [Rest] using
              (Finset.prod_univ_sum
                (t := fun k : Rest => (Finset.univ : Finset (α k.1)))
                (f := fun k a => (μ k.1 a).toReal))
      _ = 1 := by simp [hcoord]
  have hprod_split :
      ∀ x : (α i × α j) × ((k : Rest) → α k.1),
        (∏ k : ι, (μ k ((e.symm x) k)).toReal) =
          (μ i x.1.1).toReal * (μ j x.1.2).toReal *
            ∏ k : Rest, (μ k.1 (x.2 k)).toReal := by
    intro x
    let g : ι → ℝ := fun k => (μ k ((e.symm x) k)).toReal
    have hi_eval : g i = (μ i x.1.1).toReal := by
      simp [g, e, twoCoordDFunEquivProdRest]
    have hj_eval : g j = (μ j x.1.2).toReal := by
      simp [g, e, twoCoordDFunEquivProdRest, hij.symm]
    have hrest :
        (∏ k ∈ ({i}ᶜ : Finset ι) \ {j}, g k) =
          ∏ k : Rest, (μ k.1 (x.2 k)).toReal := by
      rw [Finset.prod_subtype
        (s := ({i}ᶜ : Finset ι) \ {j})
        (p := fun k : ι => k ≠ i ∧ k ≠ j)]
      · refine Finset.prod_congr rfl ?_
        intro k _
        simp [g, e, twoCoordDFunEquivProdRest, k.2.1, k.2.2]
      · intro k
        simp
    calc
      ∏ k : ι, (μ k ((e.symm x) k)).toReal
          = ∏ k : ι, g k := rfl
      _ = g i * ∏ k ∈ ({i}ᶜ : Finset ι), g k := by
            rw [Fintype.prod_eq_mul_prod_compl]
      _ = g i * (g j * ∏ k ∈ ({i}ᶜ : Finset ι) \ {j}, g k) := by
            congr 1
            rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem]
            simp [hij.symm]
      _ = (μ i x.1.1).toReal * (μ j x.1.2).toReal *
            ∏ k : Rest, (μ k.1 (x.2 k)).toReal := by
            rw [hi_eval, hj_eval, hrest]
            ring
  unfold pmfPairExp pmfExp
  calc
    ∑ f : ((k : ι) → α k),
        (pmfPi μ f).toReal * F (f i) (f j)
        =
        ∑ x : (α i × α j) × ((k : Rest) → α k.1),
          (pmfPi μ (e.symm x)).toReal *
            F ((e.symm x) i) ((e.symm x) j) := by
          simpa [e] using
            (Equiv.sum_comp e.symm
              (fun f : (k : ι) → α k =>
                (pmfPi μ f).toReal * F (f i) (f j))).symm
    _ =
        ∑ x : (α i × α j) × ((k : Rest) → α k.1),
          ((μ i x.1.1).toReal * (μ j x.1.2).toReal *
              ∏ k : Rest, (μ k.1 (x.2 k)).toReal) *
            F x.1.1 x.1.2 := by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [pmfPi_apply_toReal, hprod_split x]
          simp [e, twoCoordDFunEquivProdRest, hij.symm]
    _ =
        ∑ pair : α i × α j, ∑ rest : ((k : Rest) → α k.1),
          ((μ i pair.1).toReal * (μ j pair.2).toReal *
              ∏ k : Rest, (μ k.1 (rest k)).toReal) *
            F pair.1 pair.2 := by
          simpa [Finset.univ_product_univ] using
            (Finset.sum_product'
              (s := (Finset.univ : Finset (α i × α j)))
              (t := (Finset.univ : Finset ((k : Rest) → α k.1)))
              (f := fun pair rest =>
                ((μ i pair.1).toReal * (μ j pair.2).toReal *
                    ∏ k : Rest, (μ k.1 (rest k)).toReal) *
                  F pair.1 pair.2))
    _ =
        ∑ pair : α i × α j,
          ((μ i pair.1).toReal * (μ j pair.2).toReal) *
            F pair.1 pair.2 := by
          refine Finset.sum_congr rfl ?_
          intro pair _
          calc
            ∑ rest : ((k : Rest) → α k.1),
              ((μ i pair.1).toReal * (μ j pair.2).toReal *
                  ∏ k : Rest, (μ k.1 (rest k)).toReal) *
                F pair.1 pair.2
                =
                ((μ i pair.1).toReal * (μ j pair.2).toReal *
                    F pair.1 pair.2) *
                  ∑ rest : ((k : Rest) → α k.1),
                    ∏ k : Rest, (μ k.1 (rest k)).toReal := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro rest _
                  ring
            _ = ((μ i pair.1).toReal * (μ j pair.2).toReal) *
                  F pair.1 pair.2 := by
                  rw [hrest_mass]
                  ring
    _ =
        ∑ a : α i, (μ i a).toReal *
          ∑ b : α j, (μ j b).toReal * F a b := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro b _
          ring

/--
The two-coordinate event marginal of a finite independent dependent product is
the independent pair-product event probability.
-/
theorem pmfProb_pmfPi_twoCoord_eq_pmfProd_dependent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ k : ι, Fintype (α k)]
    [∀ k : ι, DecidableEq (α k)]
    (μ : ∀ k : ι, PMF (α k)) {i j : ι} (hij : i ≠ j)
    (p : α i → α j → Prop) [DecidableRel p] :
    pmfProb (pmfPi μ)
        (fun f : (k : ι) → α k => p (f i) (f j)) =
      pmfProb (pmfProd (μ i) (μ j))
        (fun x : α i × α j => p x.1 x.2) := by
  classical
  unfold pmfProb
  change
    pmfExp (pmfPi μ)
        (fun f : (k : ι) → α k => if p (f i) (f j) then (1 : ℝ) else 0) =
      pmfExp (pmfProd (μ i) (μ j))
        (fun x : α i × α j => if p x.1 x.2 then (1 : ℝ) else 0)
  rw [pmfExp_pmfPi_twoCoord_eq_pairExp_dependent
    (μ := μ) (i := i) (j := j) hij
    (F := fun a b => if p a b then (1 : ℝ) else 0)]
  rw [pmfExp_pmfProd_eq_pairExp]

/--
For independent finite PMFs, the probability of a product event factors.
-/
theorem pmfProb_pmfProd_and_eq_mul_pmfProb {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β)
    (p : α → Prop) (q : β → Prop)
    [DecidablePred p] [DecidablePred q] :
    pmfProb (pmfProd μ ν) (fun x : α × β => p x.1 ∧ q x.2) =
      pmfProb μ p * pmfProb ν q := by
  classical
  unfold pmfProb
  rw [pmfExp_pmfProd_eq_pairExp]
  exact pmfPairExp_indicator_and_eq_mul_pmfProb μ ν p q

/-- The expectation of a separable product factors under independent draws. -/
theorem pmfPairExp_mul_separable {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (μ : PMF α) (ν : PMF β) (f : α → ℝ) (g : β → ℝ) :
    pmfPairExp μ ν (fun a b => f a * g b) =
      pmfExp μ f * pmfExp ν g := by
  classical
  unfold pmfPairExp pmfExp
  calc
    ∑ a : α, (μ a).toReal * (∑ b : β, (ν b).toReal * (f a * g b))
        =
        ∑ a : α, (μ a).toReal * (f a * ∑ b : β, (ν b).toReal * g b) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro b _
          ring
    _ =
        (∑ a : α, (μ a).toReal * f a) *
          (∑ b : β, (ν b).toReal * g b) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro a _
          ring

end EconCSLib
