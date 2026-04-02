module

public import Mathlib.Probability.Kernel.Proper
public import GibbsMeasure.Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

public section

open MeasureTheory ENNReal NNReal Set

namespace ProbabilityTheory.Kernel
variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {μ : Measure[𝓧] X}
  {A B : Set X} {f g : X → ℝ≥0∞} {x₀ : X}

@[mk_iff]
class IsCondExp (π : Kernel[𝓑, 𝓧] X X) (μ : Measure[𝓧] X) : Prop where
  condExp_ae_eq_kernel_apply ⦃A : Set X⦄ : MeasurableSet[𝓧] A →
    μ[A.indicator 1| 𝓑] =ᵐ[μ] fun a ↦ (π a A).toReal

lemma isCondExp_iff_bind_eq_left (hπ : π.IsProper) (h𝓑𝓧 : 𝓑 ≤ 𝓧) [SigmaFinite (μ.trim h𝓑𝓧)] :
    IsCondExp π μ ↔ μ.bind π = μ := by
  simp_rw [isCondExp_iff, Filter.eventuallyEq_comm,
    toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq h𝓑𝓧, Measure.ext_iff]
  refine ⟨fun h A hA ↦ ?_, fun h A hA B hB ↦ ?_⟩
  · rw [eq_comm, Measure.bind_apply hA (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable]
    simpa using h hA _ .univ
  · rw [hπ.setLIntegral_eq_comp h𝓑𝓧 hA hB, eq_comm]
    exact h _ (by measurability)

lemma condExp_ae_eq_kernel_apply
    (h : ∀ (f : X → ℝ), Bornology.IsBounded (Set.range f) → Measurable[𝓧] f →
      condExp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)))
    {A : Set X} (A_mble : MeasurableSet[𝓧] A) :
    condExp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ))) =ᵐ[μ] (fun x ↦ (π x A).toReal) := by
  have ind_bdd : Bornology.IsBounded (Set.range (A.indicator (fun _ ↦ (1 : ℝ)))) := by
    apply (Metric.isBounded_Icc (0 : ℝ) 1).subset
    rw [range_subset_iff]
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  have ind_mble : Measurable[𝓧] (A.indicator (fun _ ↦ (1 : ℝ))) := by
    exact (measurable_indicator_const_iff 1).mpr A_mble
  specialize h _ ind_bdd ind_mble
  apply h.trans
  simp_rw [← Pi.one_def, @integral_indicator_one X 𝓧 _ _ A_mble]
  rfl

variable [π.IsCondExp μ]

private lemma condExp_indicator_ae_eq_integral_kernel (A_mble : MeasurableSet[𝓧] A) :
    condExp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ)))
      =ᵐ[μ] (fun x₀ ↦ ∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x ∂(π x₀)) := by
  apply (IsCondExp.condExp_ae_eq_kernel_apply (π := π) A_mble).trans
  simp_rw [← Pi.one_def, @integral_indicator_one X 𝓧 _ _ A_mble]
  rfl

variable [IsFiniteMeasure μ] [IsFiniteKernel π]

private lemma condExp_const_indicator_ae_eq_integral_kernel (c : ℝ) (A_mble : MeasurableSet[𝓧] A)
    (h : condExp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ))) =ᵐ[μ] (fun x ↦ (π x A).toReal)) :
    condExp 𝓑 μ (A.indicator (fun _ ↦ (c : ℝ)))
      =ᵐ[μ] (fun x₀ ↦ ∫ x, A.indicator (fun _ ↦ (c : ℝ)) x ∂(π x₀)) := by
  have smul_eq : A.indicator (fun _ ↦ (c : ℝ)) = c • A.indicator (fun _ ↦ (1 : ℝ)) := by
    apply funext
    intro x
    have hidentityc :
      (c • A.indicator (fun _ ↦ (1 : ℝ))) x = c * (A.indicator (fun _ ↦ (1 : ℝ)) x) := rfl
    rw [hidentityc]
    if hinA : x ∈ A then
      rw [indicator_of_mem hinA, indicator_of_mem hinA]
      exact Eq.symm (MulOneClass.mul_one c)
    else
      rw [indicator_of_notMem hinA, indicator_of_notMem hinA]
      exact Eq.symm (CommMonoidWithZero.mul_zero c)
  have foo : c • condExp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ)))
     =ᵐ[μ] condExp 𝓑 μ (A.indicator (fun _ ↦ (c : ℝ))) := by
    rw [smul_eq]
    exact (condExp_smul (μ := μ) c (A.indicator (fun _ ↦ (1 : ℝ))) 𝓑).symm
  nth_rw 2 [smul_eq]
  simp only [Pi.smul_apply, smul_eq_mul, integral_const_mul]
  apply foo.symm.trans
  have : c • (fun x₀ ↦ ∫ (a : X), A.indicator (fun x ↦ (1 : ℝ)) a ∂π x₀)
     = fun x₀ ↦ c * ∫ (a : X), A.indicator (fun x ↦ (1 : ℝ)) a ∂π x₀ := by
    ext; simp [smul_eq_mul]
  rw [← this]
  have := condExp_indicator_ae_eq_integral_kernel (μ := μ) (π := π) A_mble
  exact this.const_smul c

private lemma condExp_simpleFunc_ae_eq_integral_kernel (f : @SimpleFunc X 𝓧 ℝ) :
    condExp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)) := by
  induction f using SimpleFunc.induction with
  | @const c _s hs =>
    exact condExp_const_indicator_ae_eq_integral_kernel c hs
      (IsCondExp.condExp_ae_eq_kernel_apply hs)
  | @add f g _disj hf hg =>
    simp only [SimpleFunc.coe_add]
    exact (condExp_add (by fun_prop) (by fun_prop) 𝓑).trans
      ((hf.add hg).trans (.of_forall fun x₀ ↦
        (integral_add (by fun_prop) (by fun_prop)).symm))

lemma condExp_ae_eq_integral_kernel (f : X → ℝ) :
    condExp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)) := sorry

end ProbabilityTheory.Kernel
