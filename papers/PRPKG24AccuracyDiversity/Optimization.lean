import PRPKG24AccuracyDiversity.Representation
import EconCSLib.Foundations.Math.Asymptotics

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

namespace ConsumptionModel

/--
Finite code for allocations of exactly `N` items.

Each count is stored as a `Fin (N + 1)`, so the search space is finite. The
subtype proof records that the decoded allocation has total `N`.
-/
abbrev FeasibleAllocationCode (T N : ℕ) :=
  { f : ItemType T → Fin (N + 1) // ∑ t : ItemType T, (f t).val = N }

namespace FeasibleAllocationCode

/-- Decode a finite allocation code into the library's count-allocation type. -/
def toAllocation {T N : ℕ} (x : FeasibleAllocationCode T N) : CountAllocation T where
  count := fun t => (x.1 t).val

@[simp] theorem toAllocation_count {T N : ℕ}
    (x : FeasibleAllocationCode T N) (t : ItemType T) :
    x.toAllocation.count t = (x.1 t).val := rfl

/-- Decoded feasible codes have the requested total. -/
theorem toAllocation_feasible {T N : ℕ}
    (x : FeasibleAllocationCode T N) :
    FeasibleAtTotal N x.toAllocation := by
  exact x.2

/-- A fixed-total allocation can be encoded in the finite search space. -/
def ofFeasible {T N : ℕ} (a : CountAllocation T)
    (hfeas : FeasibleAtTotal N a) : FeasibleAllocationCode T N :=
  ⟨fun t =>
      ⟨a.count t, Nat.lt_succ_of_le
        (by
          have hle := EconCSLib.Allocation.count_le_total a t
          have htotal : a.total = N := hfeas
          rw [htotal] at hle
          exact hle)⟩,
    by
      simpa [FeasibleAtTotal] using hfeas⟩

@[simp] theorem toAllocation_ofFeasible {T N : ℕ}
    (a : CountAllocation T) (hfeas : FeasibleAtTotal N a) :
    (ofFeasible a hfeas).toAllocation = a := by
  cases a
  rfl

/-- A canonical feasible code putting all `N` items on one available type. -/
noncomputable def singleton {T N : ℕ} [Nonempty (ItemType T)] :
    FeasibleAllocationCode T N := by
  classical
  let t0 : ItemType T := Classical.choice inferInstance
  refine ⟨fun t =>
    if t = t0 then ⟨N, Nat.lt_succ_self N⟩ else ⟨0, Nat.succ_pos N⟩, ?_⟩
  simp only [apply_ite]
  calc
    (∑ t : ItemType T, (if t = t0 then N else 0 : ℕ))
        = ∑ t ∈ (Finset.univ : Finset (ItemType T)),
            (if t = t0 then N else 0 : ℕ) := rfl
    _ = (if t0 = t0 then N else 0 : ℕ) := by
        exact Finset.sum_eq_single t0
          (by
            intro b _ hb
            simp [hb])
          (by
            intro hnot
            simp at hnot)
    _ = N := by
        simp

end FeasibleAllocationCode

/-- A finite fixed-total count-allocation problem always has an objective maximizer. -/
theorem exists_isOptimalAtTotal {T : ℕ} [Nonempty (ItemType T)]
    (M : ConsumptionModel T) (N : ℕ) :
    ∃ a : CountAllocation T, M.IsOptimalAtTotal N a := by
  classical
  let instCode : Nonempty (FeasibleAllocationCode T N) :=
    ⟨FeasibleAllocationCode.singleton (T := T) (N := N)⟩
  haveI : Nonempty (FeasibleAllocationCode T N) := instCode
  let score : FeasibleAllocationCode T N → ℝ :=
    fun x => M.objective x.toAllocation
  obtain ⟨xmax, _hxmem, hxmax⟩ :=
    Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (FeasibleAllocationCode T N)))
      (H := Finset.univ_nonempty) (f := score)
  refine ⟨xmax.toAllocation, ?_, ?_⟩
  · exact FeasibleAllocationCode.toAllocation_feasible xmax
  · intro b hb
    let xb : FeasibleAllocationCode T N :=
      FeasibleAllocationCode.ofFeasible b hb
    have hle : score xb ≤ EconCSLib.finiteMax score :=
      EconCSLib.le_finiteMax score xb
    unfold EconCSLib.finiteMax at hle
    rw [hxmax] at hle
    simpa [score, xb] using hle

/-- Objective values attainable by allocations of exactly `N` items. -/
def attainableValuesAtTotal {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ) : Set ℝ :=
  {r | ∃ a : CountAllocation T, FeasibleAtTotal N a ∧ r = M.objective a}

/-- Supremal objective value among allocations of size `N`. -/
noncomputable def optimalValueAtTotal {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ) : ℝ :=
  sSup (attainableValuesAtTotal M N)

/-- The set of optimal allocations of size `N`. -/
def optimalAllocationsAtTotal {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ) : Set (CountAllocation T) :=
  {a | M.IsOptimalAtTotal N a}

/--
A theorem target: every optimal allocation at size `N` approximately matches a
specified γ-homogeneity profile.
-/
noncomputable def ApproxHomogeneityOfOptima {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ) (G : GammaHomogeneityProfile T) (ε : ℝ) : Prop :=
  ∀ a : CountAllocation T, M.IsOptimalAtTotal N a → G.Approx a ε

/--
A theorem target for asymptotic statements: there exists an error schedule tending to zero
such that all positive-size optimal allocations approximately match the profile.

The target intentionally ignores `N = 0`: the paper's claims are limits as
`n → ∞`, and zero-size allocations need not match a nonzero target profile.
-/
def AsymptoticHomogeneityTarget {T : ℕ}
    (Mseq : ℕ → ConsumptionModel T) (G : GammaHomogeneityProfile T)
    (TendsToZero : (ℕ → ℝ) → Prop) : Prop :=
  ∃ ε : ℕ → ℝ,
    TendsToZero ε ∧ ∀ N a, 0 < N → (Mseq N).IsOptimalAtTotal N a → G.Approx a (ε N)

/-- The default PRPKG asymptotic target using the reusable filter-based zero predicate. -/
def AsymptoticHomogeneity {T : ℕ}
    (Mseq : ℕ → ConsumptionModel T) (G : GammaHomogeneityProfile T) : Prop :=
  AsymptoticHomogeneityTarget Mseq G EconCSLib.Math.TendsToZero

theorem AsymptoticHomogeneityTarget.mono_rate {T : ℕ}
    {Mseq : ℕ → ConsumptionModel T} {G : GammaHomogeneityProfile T}
    {Rate₁ Rate₂ : (ℕ → ℝ) → Prop}
    (hRate : ∀ ε, Rate₁ ε → Rate₂ ε) :
    AsymptoticHomogeneityTarget Mseq G Rate₁ →
      AsymptoticHomogeneityTarget Mseq G Rate₂ := by
  intro ⟨ε, hε, happrox⟩
  exact ⟨ε, hRate ε hε, happrox⟩

theorem AsymptoticHomogeneityTarget.of_exactInvRate {T : ℕ}
    {Mseq : ℕ → ConsumptionModel T} {G : GammaHomogeneityProfile T} :
    AsymptoticHomogeneityTarget Mseq G EconCSLib.Math.ExactInvRate →
      AsymptoticHomogeneity Mseq G :=
  AsymptoticHomogeneityTarget.mono_rate
    (fun ε hε => EconCSLib.Math.ExactInvRate_implies_TendsToZero ε hε)

theorem AsymptoticHomogeneityTarget.of_exactInvSqrtRate {T : ℕ}
    {Mseq : ℕ → ConsumptionModel T} {G : GammaHomogeneityProfile T} :
    AsymptoticHomogeneityTarget Mseq G EconCSLib.Math.ExactInvSqrtRate →
      AsymptoticHomogeneity Mseq G :=
  AsymptoticHomogeneityTarget.mono_rate
    (fun ε hε => EconCSLib.Math.ExactInvSqrtRate_implies_TendsToZero ε hε)

/--
Uniform `O(1)` count error for every positive-size optimum gives a paper-style
exact `C / N` asymptotic homogeneity target.
-/
theorem AsymptoticHomogeneityTarget.of_uniform_count_abs_error {T : ℕ}
    {Mseq : ℕ → ConsumptionModel T} {G : GammaHomogeneityProfile T} {C : ℝ}
    (hC : 0 < C)
    (hclose :
      ∀ N (a : CountAllocation T), 0 < N → (Mseq N).IsOptimalAtTotal N a →
        ∀ t, |(a.count t : ℝ) - (N : ℝ) * G.targetShare t| ≤ C) :
    AsymptoticHomogeneityTarget Mseq G EconCSLib.Math.ExactInvRate := by
  refine ⟨fun N => C / (N : ℝ), ?_, ?_⟩
  · exact ⟨C, hC, fun N => rfl⟩
  · intro N a hN hopt
    exact GammaHomogeneityProfile.approx_of_count_abs_error
      G a hopt.1 hN (hclose N a hN hopt)

end ConsumptionModel
end PRPKG24AccuracyDiversity
