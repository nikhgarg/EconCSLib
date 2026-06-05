import EconCSLib.Foundations.Probability.Averaging

namespace PRPKG24AccuracyDiversity

open MeasureTheory
open scoped BigOperators

/-!
# Continuous-Sphere Proposition 4 Layer

This file keeps the paper-facing Proposition 4 averaging names stable while the
reusable averaging/minimization certificate lives in
`EconCSLib.Foundations.Probability.Averaging`.
-/

/--
Paper-facing alias for the reusable averaging/minimization certificate used in
Proposition 4.
-/
abbrev Proposition4AveragingCertificate :=
  EconCSLib.Probability.AveragingMinimizationCertificate

namespace Proposition4AveragingCertificate

noncomputable def ofFiniteUniformAverage
    {Profile User : Type*} [Fintype User] [Nonempty User]
    (gamma : Profile → ℝ) (rho : Profile → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (average_rho_eq_uniformValue :
      ∀ alpha : Profile,
        (∑ u : User, rho alpha u) / (Fintype.card User : ℝ) =
          uniformValue)
    (rho_le_gamma : ∀ alpha : Profile, ∀ u : User, rho alpha u ≤ gamma alpha) :
    Proposition4AveragingCertificate Profile User :=
  EconCSLib.Probability.AveragingMinimizationCertificate.ofFiniteUniformAverage
    gamma rho uniformProfile uniformValue uniform_gamma_eq
    average_rho_eq_uniformValue rho_le_gamma

noncomputable def ofProbabilityIntegralAverage
    {Profile User : Type*} [MeasurableSpace User]
    (userMeasure : Measure User) [IsProbabilityMeasure userMeasure]
    (gamma : Profile → ℝ) (rho : Profile → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (rho_integrable : ∀ alpha : Profile, Integrable (rho alpha) userMeasure)
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (integral_rho_eq_uniformValue :
      ∀ alpha : Profile, (∫ u, rho alpha u ∂userMeasure) =
        uniformValue)
    (rho_le_gamma : ∀ alpha : Profile, ∀ u : User, rho alpha u ≤ gamma alpha) :
    Proposition4AveragingCertificate Profile User :=
  EconCSLib.Probability.AveragingMinimizationCertificate.ofProbabilityIntegralAverage
    userMeasure gamma rho uniformProfile uniformValue rho_integrable
    uniform_gamma_eq integral_rho_eq_uniformValue rho_le_gamma

noncomputable def ofProbabilityKernelAverage
    {Profile User Item : Type*} [MeasurableSpace User] [MeasurableSpace Item]
    (userMeasure : Measure User) [IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → Measure Item)
    (profile_probability :
      ∀ alpha : Profile, IsProbabilityMeasure (profileMeasure alpha))
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (rho_integrable :
      ∀ alpha : Profile,
        Integrable (fun u => ∫ x, kernel x u ∂profileMeasure alpha)
          userMeasure)
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (integral_kernel_swap :
      ∀ alpha : Profile,
        (∫ u, (∫ x, kernel x u ∂profileMeasure alpha) ∂userMeasure) =
          ∫ x, (∫ u, kernel x u ∂userMeasure) ∂profileMeasure alpha)
    (kernel_user_integral_eq :
      ∀ x : Item, (∫ u, kernel x u ∂userMeasure) = uniformValue)
    (rho_le_gamma :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ gamma alpha) :
    Proposition4AveragingCertificate Profile User :=
  EconCSLib.Probability.AveragingMinimizationCertificate.ofProbabilityKernelAverage
    userMeasure profileMeasure profile_probability gamma kernel uniformProfile
    uniformValue rho_integrable uniform_gamma_eq integral_kernel_swap
    kernel_user_integral_eq rho_le_gamma

noncomputable def ofProbabilityKernelAverageOfIntegrable
    {Profile User Item : Type*} [MeasurableSpace User] [MeasurableSpace Item]
    (userMeasure : Measure User) [IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → Measure Item)
    (profile_probability :
      ∀ alpha : Profile, IsProbabilityMeasure (profileMeasure alpha))
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (kernel_integrable :
      ∀ alpha : Profile,
        Integrable (Function.uncurry kernel)
          ((profileMeasure alpha).prod userMeasure))
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (kernel_user_integral_eq :
      ∀ x : Item, (∫ u, kernel x u ∂userMeasure) = uniformValue)
    (rho_le_gamma :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ gamma alpha) :
    Proposition4AveragingCertificate Profile User :=
  EconCSLib.Probability.AveragingMinimizationCertificate.ofProbabilityKernelAverageOfIntegrable
    userMeasure profileMeasure profile_probability gamma kernel uniformProfile
    uniformValue kernel_integrable uniform_gamma_eq kernel_user_integral_eq
    rho_le_gamma

noncomputable def ofProbabilityKernelSymmetryAverageOfIntegrable
    {Profile User Item Sym : Type*} [MeasurableSpace User]
    [MeasurableSpace Item]
    (userMeasure : Measure User) [IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → Measure Item)
    (profile_probability :
      ∀ alpha : Profile, IsProbabilityMeasure (profileMeasure alpha))
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ)
    (kernel_integrable :
      ∀ alpha : Profile,
        Integrable (Function.uncurry kernel)
          ((profileMeasure alpha).prod userMeasure))
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (userAction : Sym → User → User)
    (itemAction : Sym → Item → Item)
    (anchor : Item)
    (userAction_measurePreserving :
      ∀ g : Sym, MeasurePreserving (userAction g) userMeasure userMeasure)
    (userAction_measurableEmbedding :
      ∀ g : Sym, MeasurableEmbedding (userAction g))
    (kernel_diagonal_invariant :
      ∀ g : Sym, ∀ x : Item, ∀ u : User,
        kernel (itemAction g x) (userAction g u) = kernel x u)
    (itemAction_transitive :
      ∀ x : Item, ∃ g : Sym, itemAction g anchor = x)
    (anchor_integral_eq_uniformValue :
      (∫ u, kernel anchor u ∂userMeasure) = uniformValue)
    (rho_le_gamma :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ gamma alpha) :
    Proposition4AveragingCertificate Profile User :=
  EconCSLib.Probability.AveragingMinimizationCertificate.ofProbabilityKernelSymmetryAverageOfIntegrable
    userMeasure profileMeasure profile_probability gamma kernel uniformProfile
    uniformValue kernel_integrable uniform_gamma_eq userAction itemAction anchor
    userAction_measurePreserving userAction_measurableEmbedding
    kernel_diagonal_invariant itemAction_transitive anchor_integral_eq_uniformValue
    rho_le_gamma

noncomputable def ofProbabilityKernelAverageOfBounded
    {Profile User Item : Type*} [MeasurableSpace User] [MeasurableSpace Item]
    (userMeasure : Measure User) [IsProbabilityMeasure userMeasure]
    (profileMeasure : Profile → Measure Item)
    (profile_probability :
      ∀ alpha : Profile, IsProbabilityMeasure (profileMeasure alpha))
    (gamma : Profile → ℝ) (kernel : Item → User → ℝ)
    (uniformProfile : Profile) (uniformValue : ℝ) (C : ℝ)
    (kernel_aestronglyMeasurable :
      ∀ alpha : Profile,
        AEStronglyMeasurable (Function.uncurry kernel)
          ((profileMeasure alpha).prod userMeasure))
    (kernel_norm_le :
      ∀ alpha : Profile,
        ∀ᵐ xu ∂((profileMeasure alpha).prod userMeasure),
          ‖Function.uncurry kernel xu‖ ≤ C)
    (uniform_gamma_eq : gamma uniformProfile = uniformValue)
    (kernel_user_integral_eq :
      ∀ x : Item, (∫ u, kernel x u ∂userMeasure) = uniformValue)
    (rho_le_gamma :
      ∀ alpha : Profile, ∀ u : User,
        (∫ x, kernel x u ∂profileMeasure alpha) ≤ gamma alpha) :
    Proposition4AveragingCertificate Profile User :=
  EconCSLib.Probability.AveragingMinimizationCertificate.ofProbabilityKernelAverageOfBounded
    userMeasure profileMeasure profile_probability gamma kernel uniformProfile
    uniformValue C kernel_aestronglyMeasurable kernel_norm_le uniform_gamma_eq
    kernel_user_integral_eq rho_le_gamma

/--
The abstract averaging step from Proposition 4, forwarded through the
paper-facing namespace.
-/
theorem uniform_minimizes {Profile User : Type*}
    (C : Proposition4AveragingCertificate Profile User) :
    ∀ alpha : Profile, C.gamma C.uniformProfile ≤ C.gamma alpha :=
  EconCSLib.Probability.AveragingMinimizationCertificate.uniform_minimizes C

end Proposition4AveragingCertificate

end PRPKG24AccuracyDiversity
