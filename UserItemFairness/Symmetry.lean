import UserItemFairness.Optimization
import DecisionCore.Classwise

open DecisionCore

namespace UserItemFairness

abbrev UserType (K : ℕ) := Fin K
abbrev TypePolicy (K n : ℕ) := DecisionCore.Policy (UserType K) (Item n)

namespace RecommendationModel

/--
A recommendation model together with a user-type map for which equal types have
identical utility rows. This is the data needed to formalize the paper's `S_symm`.
-/
structure SymmetricData (m n K : ℕ) where
  model : RecommendationModel m n
  types : UserTypeAssignment m K
  agreeWithinTypes : UtilitiesAgreeWithinTypes model types

end RecommendationModel

namespace UserTypeAssignment

/-- Lift a type-level policy to a user-level policy by composition with the type map. -/
def liftTypePolicy {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (ρ : TypePolicy K n) : Policy m n :=
  DecisionCore.Policy.liftAlong τ.toType ρ

/-- A user-level policy is type-symmetric if equal types receive equal PMFs. -/
def IsTypeSymmetric {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (ρ : Policy m n) : Prop :=
  DecisionCore.Policy.IsClasswise τ.toType ρ

/-- The set `S_symm` of type-symmetric user-level policies. -/
def SymmetricPolicies {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) : Set (Policy m n) :=
  DecisionCore.Policy.ClasswisePolicies τ.toType

@[simp] theorem liftTypePolicy_apply {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (ρ : TypePolicy K n) (u : User m) :
    liftTypePolicy τ ρ u = ρ (τ.toType u) := rfl

@[simp] theorem liftTypePolicy_sameType {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (ρ : TypePolicy K n)
    {u u' : User m} (h : τ.toType u = τ.toType u') :
    liftTypePolicy τ ρ u = liftTypePolicy τ ρ u' := by
  simp [liftTypePolicy, h]

/-- Every lifted type-level policy is type-symmetric. -/
theorem liftTypePolicy_isTypeSymmetric {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (ρ : TypePolicy K n) :
    IsTypeSymmetric τ (liftTypePolicy τ ρ) := by
  simpa [IsTypeSymmetric, liftTypePolicy] using
    (DecisionCore.Policy.liftAlong_isClasswise (τ := τ.toType) (ρ := ρ))

/-- Chosen representative user for each declared user type. -/
abbrev TypeRepresentatives {m K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) :=
  DecisionCore.Policy.FiberRepresentatives τ.toType

/--
Descend a user-level policy to the type level by evaluating it on one chosen
representative user from each type.
-/
def descendTypePolicy {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : Policy m n) : TypePolicy K n :=
  DecisionCore.Policy.descendAlong reps ρ

@[simp] theorem descendTypePolicy_apply {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : Policy m n) (k : UserType K) :
    descendTypePolicy τ reps ρ k = ρ (reps.repr k) := rfl

@[simp] theorem descendTypePolicy_liftTypePolicy {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : TypePolicy K n) :
    descendTypePolicy τ reps (liftTypePolicy τ ρ) = ρ := by
  simpa [descendTypePolicy, liftTypePolicy] using
    (DecisionCore.Policy.descendAlong_liftAlong (τ := τ.toType) reps ρ)

/--
If a user-level policy is type-symmetric, then after choosing one representative
per type it is exactly the lift of a type-level policy.
-/
theorem liftTypePolicy_descendTypePolicy_eq_of_isTypeSymmetric {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : Policy m n)
    (hρ : IsTypeSymmetric τ ρ) :
    liftTypePolicy τ (descendTypePolicy τ reps ρ) = ρ := by
  simpa [IsTypeSymmetric, descendTypePolicy, liftTypePolicy] using
    (DecisionCore.Policy.liftAlong_descendAlong_eq_of_isClasswise
      (τ := τ.toType) reps ρ hρ)

/--
A user-level policy is type-symmetric exactly when it comes from lifting some
policy on user types. Representatives make the reverse direction explicit.
-/
theorem isTypeSymmetric_iff_exists_liftTypePolicy {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : Policy m n) :
    IsTypeSymmetric τ ρ ↔ ∃ ρK : TypePolicy K n, liftTypePolicy τ ρK = ρ := by
  simpa [IsTypeSymmetric, liftTypePolicy] using
    (DecisionCore.Policy.isClasswise_iff_exists_liftAlong (τ := τ.toType) reps ρ)

end UserTypeAssignment

namespace TypePolicy

/-- Positive-support type-item pairs `(k, j)`. -/
noncomputable def activeTypeItemPairs {K n : ℕ}
    (ρ : TypePolicy K n) : Finset (UserType K × Item n) :=
  DecisionCore.Policy.activePairs ρ

/-- Number of positive-support type-item pairs. -/
noncomputable def activeTypeItemPairsCard {K n : ℕ} (ρ : TypePolicy K n) : ℕ :=
  DecisionCore.Policy.activePairsCard ρ

/-- Zero-support type-item pairs `(k, j)`. -/
noncomputable def inactiveTypeItemPairs {K n : ℕ}
    (ρ : TypePolicy K n) : Finset (UserType K × Item n) :=
  DecisionCore.Policy.inactivePairs ρ

@[simp] theorem mem_inactiveTypeItemPairs {K n : ℕ}
    (ρ : TypePolicy K n) (p : UserType K × Item n) :
    p ∈ inactiveTypeItemPairs ρ ↔ ρ p.1 p.2 = 0 := by
  simp [inactiveTypeItemPairs]

/-- Number of zero-support type-item pairs. -/
noncomputable def inactiveTypeItemPairsCard {K n : ℕ} (ρ : TypePolicy K n) : ℕ :=
  DecisionCore.Policy.inactivePairsCard ρ

/-- Items recommended to more than one user type. -/
noncomputable def sharedItems {K n : ℕ} (ρ : TypePolicy K n) : Finset (Item n) :=
  DecisionCore.Policy.multiAssignedActions ρ

/-- Target shape of the first sparsity conclusion in Proposition 2. -/
def ActivePairsBound {K n : ℕ} (ρ : TypePolicy K n) : Prop :=
  activeTypeItemPairsCard ρ ≤ n + K - 1

/-- Target shape of the second sparsity conclusion in Proposition 2. -/
def SharedItemsBound {K n : ℕ} (ρ : TypePolicy K n) : Prop :=
  (sharedItems ρ).card ≤ K - 1

/-- The combined sparse-support shape extracted from Proposition 2. -/
def SparseShape {K n : ℕ} (ρ : TypePolicy K n) : Prop :=
  ActivePairsBound ρ ∧ SharedItemsBound ρ

/--
Support-count consequence of the LP basic-feasible-solution theorem used in
the paper. The linear-programming fact supplies that at least
`nK + 1 - (n + K)` nonnegativity constraints bind; in the recommendation LP
these binding nonnegativity constraints are exactly zero-probability type-item
pairs.
-/
def BasicFeasibleSupportCertificate {K n : ℕ} (ρ : TypePolicy K n) : Prop :=
  n * K + 1 - (n + K) ≤ inactiveTypeItemPairsCard ρ

/-- Active and inactive type-item pairs partition all `K * n` type-item pairs. -/
theorem activeTypeItemPairsCard_add_inactiveTypeItemPairsCard_eq {K n : ℕ}
    (ρ : TypePolicy K n) :
    activeTypeItemPairsCard ρ + inactiveTypeItemPairsCard ρ = K * n := by
  simpa [activeTypeItemPairsCard, inactiveTypeItemPairsCard, UserType, Item]
    using (DecisionCore.Policy.activePairsCard_add_inactivePairsCard_eq_card
      (ρ := ρ))

/--
The paper's support-count arithmetic: once the basic-feasible-solution theorem
gives enough binding nonnegativity constraints, at most `n + K - 1` type-item
pairs can have positive support.
-/
theorem activePairsBound_of_basicFeasibleSupportCertificate {K n : ℕ}
    [NeZero K] [NeZero n]
    (ρ : TypePolicy K n) (hcert : BasicFeasibleSupportCertificate ρ) :
    ActivePairsBound ρ := by
  unfold ActivePairsBound activeTypeItemPairsCard
    BasicFeasibleSupportCertificate inactiveTypeItemPairsCard at *
  have hsupport :=
    DecisionCore.Policy.activePairsCard_le_card_sub_of_inactivePairsCard_ge
      (ρ := ρ) hcert
  simp [UserType, Item, Nat.mul_comm] at hsupport
  exact le_trans hsupport (by omega)

/--
Appendix D, Lemma 4, Part 1 for the two-type Problem 6 LP: a basic feasible
solution has at most `n + 1` positive `x_j,y_j` variables.
-/
theorem activePairsCard_le_n_add_one_of_basicFeasibleSupportCertificate_two
    {n : ℕ} [NeZero n]
    (ρ : TypePolicy 2 n) (hcert : BasicFeasibleSupportCertificate ρ) :
    activeTypeItemPairsCard ρ ≤ n + 1 := by
  have hactive :=
    activePairsBound_of_basicFeasibleSupportCertificate ρ hcert
  unfold ActivePairsBound at hactive
  omega

/--
Appendix D, Lemma 4, Part 1 for the two-type Problem 6 LP: at least `n - 1`
of the `x_j,y_j` variables are zero in a basic feasible solution.
-/
theorem inactivePairsCard_ge_n_sub_one_of_basicFeasibleSupportCertificate_two
    {n : ℕ} [NeZero n]
    (ρ : TypePolicy 2 n) (hcert : BasicFeasibleSupportCertificate ρ) :
    n - 1 ≤ inactiveTypeItemPairsCard ρ := by
  unfold BasicFeasibleSupportCertificate at hcert
  omega

/-- Types that recommend item `j` with positive probability. -/
noncomputable def activeTypesForItem {K n : ℕ}
    (ρ : TypePolicy K n) (j : Item n) : Finset (UserType K) :=
  Finset.univ.filter fun k => ρ k j ≠ 0

@[simp] theorem mem_activeTypesForItem {K n : ℕ}
    (ρ : TypePolicy K n) (j : Item n) (k : UserType K) :
    k ∈ activeTypesForItem ρ j ↔ ρ k j ≠ 0 := by
  simp [activeTypesForItem]

noncomputable def primaryActiveType {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0)
    (j : Item n) : UserType K :=
  Classical.choose (hcover j)

theorem primaryActiveType_spec {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0)
    (j : Item n) :
    ρ (primaryActiveType ρ hcover j) j ≠ 0 :=
  Classical.choose_spec (hcover j)

theorem exists_activeType_ne_primary_of_shared {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0)
    {j : Item n} (hj : j ∈ sharedItems ρ) :
    ∃ k, k ≠ primaryActiveType ρ hcover j ∧ ρ k j ≠ 0 := by
  rcases (DecisionCore.Policy.mem_multiAssignedActions ρ j).mp hj with
    ⟨k, k', hne, hk, hk'⟩
  by_cases hp : primaryActiveType ρ hcover j = k
  · refine ⟨k', ?_, hk'⟩
    intro hkp
    exact hne (hp.symm.trans hkp.symm)
  · exact ⟨k, (by intro h; exact hp h.symm), hk⟩

noncomputable def secondaryActiveType {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0)
    (j : {j : Item n // j ∈ sharedItems ρ}) : UserType K :=
  Classical.choose (exists_activeType_ne_primary_of_shared ρ hcover j.property)

theorem secondaryActiveType_ne_primary {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0)
    (j : {j : Item n // j ∈ sharedItems ρ}) :
    secondaryActiveType ρ hcover j ≠ primaryActiveType ρ hcover j :=
  (Classical.choose_spec
    (exists_activeType_ne_primary_of_shared ρ hcover j.property)).1

theorem secondaryActiveType_spec {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0)
    (j : {j : Item n // j ∈ sharedItems ρ}) :
    ρ (secondaryActiveType ρ hcover j) j.1 ≠ 0 :=
  (Classical.choose_spec
    (exists_activeType_ne_primary_of_shared ρ hcover j.property)).2

noncomputable def itemSharedInjection {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0) :
    (Item n ⊕ {j : Item n // j ∈ sharedItems ρ}) →
      {p : UserType K × Item n // p ∈ activeTypeItemPairs ρ}
  | Sum.inl j =>
      ⟨(primaryActiveType ρ hcover j, j), by
        simpa [activeTypeItemPairs] using primaryActiveType_spec ρ hcover j⟩
  | Sum.inr j =>
      ⟨(secondaryActiveType ρ hcover j, j.1), by
        simpa [activeTypeItemPairs] using secondaryActiveType_spec ρ hcover j⟩

theorem itemSharedInjection_injective {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0) :
    Function.Injective (itemSharedInjection ρ hcover) := by
  intro x y hxy
  cases x with
  | inl j =>
      cases y with
      | inl j' =>
          simp [itemSharedInjection] at hxy
          exact congrArg Sum.inl hxy.2
      | inr sj =>
          simp [itemSharedInjection] at hxy
          have hitem : j = sj.1 := hxy.2
          subst hitem
          exact False.elim ((secondaryActiveType_ne_primary ρ hcover sj) hxy.1.symm)
  | inr sj =>
      cases y with
      | inl j =>
          simp [itemSharedInjection] at hxy
          have hitem : sj.1 = j := hxy.2
          subst hitem
          exact False.elim ((secondaryActiveType_ne_primary ρ hcover sj) hxy.1)
      | inr sj' =>
          simp [itemSharedInjection] at hxy
          exact congrArg Sum.inr hxy.2

/--
If every item is recommended by some type, then active type-item pairs contain
one pair for every item plus one additional pair for every shared item.
-/
theorem card_items_add_sharedItems_le_activePairsCard {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0) :
    n + (sharedItems ρ).card ≤ activeTypeItemPairsCard ρ := by
  have hcard :=
    Fintype.card_le_of_injective (itemSharedInjection ρ hcover)
      (itemSharedInjection_injective ρ hcover)
  have hdomain :
      Fintype.card (Item n ⊕ {j : Item n // j ∈ sharedItems ρ}) =
        n + (sharedItems ρ).card := by
    simp [Fintype.card_sum, Fintype.card_coe, Item]
  have hcodomain :
      Fintype.card {p : UserType K × Item n // p ∈ activeTypeItemPairs ρ} =
        (activeTypeItemPairs ρ).card := by
    exact Fintype.card_coe (activeTypeItemPairs ρ)
  rw [hdomain, hcodomain] at hcard
  simpa [activeTypeItemPairsCard] using hcard

theorem sharedItemsBound_of_activePairsBound_of_item_coverage {K n : ℕ}
    [NeZero K]
    (ρ : TypePolicy K n)
    (hactive : ActivePairsBound ρ)
    (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0) :
    SharedItemsBound ρ := by
  have hlower := card_items_add_sharedItems_le_activePairsCard ρ hcover
  unfold ActivePairsBound at hactive
  unfold SharedItemsBound
  have hK : 1 ≤ K := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne K))
  have hle : n + (sharedItems ρ).card ≤ n + (K - 1) := by
    rw [← Nat.add_sub_assoc hK n]
    exact le_trans hlower hactive
  exact Nat.add_le_add_iff_left.mp hle

theorem sparseShape_of_activePairsBound_of_item_coverage {K n : ℕ}
    [NeZero K]
    (ρ : TypePolicy K n)
    (hactive : ActivePairsBound ρ)
    (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0) :
    SparseShape ρ := by
  exact ⟨hactive, sharedItemsBound_of_activePairsBound_of_item_coverage
    ρ hactive hcover⟩

end TypePolicy
end UserItemFairness
