module

public import Mathlib.Probability.Kernel.Proper
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import GibbsMeasure.Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import GibbsMeasure.Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

public section

open MeasureTheory ENNReal NNReal Set

attribute [fun_prop] MeasureTheory.StronglyMeasurable.integral_kernel

namespace ProbabilityTheory.Kernel
variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {μ : Measure[𝓧] X}
  {A B : Set X} {f g : X → ℝ≥0∞} {x₀ : X}

@[mk_iff]
class IsCondExp (π : Kernel[𝓑, 𝓧] X X) (μ : Measure[𝓧] X) : Prop where
  condExp_ae_eq_kernel_apply ⦃A : Set X⦄ : MeasurableSet[𝓧] A →
    μ[A.indicator 1| 𝓑] =ᵐ[μ] fun a ↦ (π a A).toReal

lemma isCondExp_iff_bind_eq_left (hπ : π.IsProper) (h𝓑𝓧 : 𝓑 ≤ 𝓧) [IsFiniteMeasure μ] :
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

private lemma condExp_const_indicator_ae_eq_integral_kernel (c : ℝ) (hA : MeasurableSet[𝓧] A) :
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
  have := condExp_indicator_ae_eq_integral_kernel (μ := μ) (π := π) hA
  exact this.const_smul c

private lemma condExp_simpleFunc_ae_eq_integral_kernel (f : @SimpleFunc X 𝓧 ℝ) [IsFiniteMeasure μ]
  [IsFiniteKernel π] : condExp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)) := by
  induction f using SimpleFunc.induction with
  | @const c _s hs => exact condExp_const_indicator_ae_eq_integral_kernel c hs
  | @add f g _disj hf hg =>
    simp only [SimpleFunc.coe_add]
    exact (condExp_add (by fun_prop) (by fun_prop) 𝓑).trans
      ((hf.add hg).trans (.of_forall fun x₀ ↦
        (integral_add (by fun_prop) (by fun_prop)).symm))

lemma condExp_ae_eq_integral (hπ : π.IsProper) (h𝓑𝓧 : 𝓑 ≤ 𝓧) (f : X → ℝ) [IsFiniteMeasure μ]
    (hf : Integrable f μ) : condExp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)) := by
  letI T (h : X → ℝ) (x₀ : X) := ∫ x, h x ∂(π x₀)
  have hbind : μ.bind π = μ := (isCondExp_iff_bind_eq_left hπ h𝓑𝓧).mp inferInstance
  have hπ_aemX : AEMeasurable (fun x₀ ↦ π x₀) μ := (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable
  have hTnorm_le (h : X → ℝ) (hh : AEMeasurable h μ) : (∫⁻ x₀, ‖T h x₀‖ₑ ∂μ) ≤ ∫⁻ x, ‖h x‖ₑ ∂μ := by
    calc (∫⁻ x₀, ‖T h x₀‖ₑ ∂μ) ≤ ∫⁻ x₀, ∫⁻ x, ‖h x‖ₑ ∂(π x₀) ∂μ :=
      lintegral_mono fun x₀ ↦ enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ x, ‖h x‖ₑ ∂μ := by rw [← Measure.lintegral_bind hπ_aemX (hbind.symm ▸ hh.enorm), hbind]
  have hT_congr {h₁ h₂ : X → ℝ} (h12 : h₁ =ᵐ[μ] h₂) : T h₁ =ᵐ[μ] T h₂ := by
    filter_upwards [Measure.ae_ae_of_ae_bind hπ_aemX (hbind.symm ▸ h12)] with _ hx₀
      using integral_congr_ae hx₀
  have hT_sm {h : _} (hh : StronglyMeasurable[𝓧] h) : AEStronglyMeasurable[𝓧] (T h) μ :=
    ((by fun_prop : StronglyMeasurable[𝓑] (T h)).mono h𝓑𝓧).aestronglyMeasurable
  have hT_int {h : _} (hh : Integrable h μ) : Integrable (T h) μ :=
    ⟨(hT_sm hh.1.stronglyMeasurable_mk).congr (hT_congr hh.1.ae_eq_mk).symm,
      (hTnorm_le h hh.1.aemeasurable).trans_lt hh.2⟩
  have hT_ae_int {h : _ → ℝ} (hh : Integrable h μ) : ∀ᵐ x₀ ∂μ, Integrable h (π x₀) := by
    have hmk_eq : ∀ᵐ_ ∂μ, h =ᵐ[_] hh.1.mk := μ.ae_ae_of_ae_bind hπ_aemX (hbind.symm ▸ hh.1.ae_eq_mk)
    have hfin : ∫⁻ x₀, (∫⁻ x, ‖hh.1.mk h x‖ₑ ∂(π x₀)) ∂μ ≠ ∞ := by
      rw [← Measure.lintegral_bind hπ_aemX (by fun_prop), hbind]
      exact (lintegral_congr_ae (hh.1.ae_eq_mk.symm.fun_comp _)).trans_ne hh.2.ne
    have hkm : Measurable[𝓑] (fun x₀ ↦ ∫⁻ x, ‖hh.1.mk h x‖ₑ ∂(π x₀)) := by fun_prop
    filter_upwards [ae_lt_top' ((hkm).mono h𝓑𝓧 le_rfl).aemeasurable hfin, hmk_eq]
      with x₀ hx₀ heq₀ using .congr ⟨by fun_prop, hx₀⟩ heq₀.symm
  suffices h : ∀ g : X → ℝ, Integrable g μ → condExp 𝓑 μ g =ᵐ[μ] T g from h f hf
  refine Integrable.induction' (fun g _ ↦ condExp 𝓑 μ g =ᵐ[μ] T g) (fun c _ hs _ ↦
    condExp_const_indicator_ae_eq_integral_kernel _ hs)
    (fun _ _ hh₁ hh₂ _ ih₁ ih₂ ↦ (condExp_add hh₁ hh₂ 𝓑).trans ((ih₁.add ih₂).trans ?_)) ?_
    (fun h₁ h₂ _ h12 ih ↦ (condExp_congr_ae h12).symm.trans (ih.trans (hT_congr h12)))
  · filter_upwards [hT_ae_int hh₁, hT_ae_int hh₂] with _ hx₁ hx₂ using (integral_add hx₁ hx₂).symm
  · letI Φ (f : X →₁[μ] ℝ) : X →₁[μ] ℝ := condExpL1CLM ℝ h𝓑𝓧 μ f
    letI Ψ (f : X →₁[μ] ℝ) : X →₁[μ] ℝ := (hT_int (L1.integrable_coeFn f)).toL1 (T f)
    have hΨ_cont : Continuous Ψ := by
      refine LipschitzWith.continuous (K := 1) (fun f g ↦ ?_)
      rw [Integrable.edist_toL1_toL1, ENNReal.coe_one, one_mul]
      have hstep : ∀ᵐ x₀ ∂μ, edist (T (⇑f) x₀) (T (⇑g) x₀) ≤ ∫⁻ x, edist (⇑f x) (⇑g x) ∂(π x₀) := by
        filter_upwards [hT_ae_int (L1.integrable_coeFn f), hT_ae_int (L1.integrable_coeFn g)]
          with _ hf₀ hg₀ using edist_eq_enorm_sub (E := ℝ) _ _ ▸ integral_sub hf₀ hg₀ ▸
            ((enorm_integral_le_lintegral_enorm _).trans
            (lintegral_mono fun _ ↦ (edist_eq_enorm_sub _ _).ge))
      calc
        _ ≤ ∫⁻ x₀, ∫⁻ x, edist (⇑f x) (⇑g x) ∂(π x₀) ∂μ := lintegral_mono_ae hstep
        _ = ∫⁻ x, edist _ _ ∂μ := by rw [← Measure.lintegral_bind hπ_aemX (by fun_prop), hbind]
        _ = edist f g := by rw [← Integrable.edist_toL1_toL1 (⇑f) (⇑g) (L1.integrable_coeFn f)
              (L1.integrable_coeFn g), Integrable.toL1_coeFn, Integrable.toL1_coeFn]
    have hset (f: ↥(Lp ℝ 1 μ)) : f ∈ {f | μ[↑↑f | 𝓑] =ᵐ[μ] T ↑↑f} ↔ f ∈ {f | Φ f = Ψ f} := by
      have hΦf : (⇑(Φ f)) =ᵐ[μ] condExp 𝓑 μ (⇑f) := by
        simpa using (condExp_ae_eq_condExpL1CLM h𝓑𝓧 (L1.integrable_coeFn f)).symm
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq, Lp.ext_iff]
      exact ⟨fun h ↦ hΦf.trans (h.trans (Integrable.coeFn_toL1 _).symm), fun h ↦ hΦf.symm.trans
        (h.trans (Integrable.coeFn_toL1 _))⟩
    exact (Set.ext hset).symm ▸ (isClosed_eq (condExpL1CLM ℝ h𝓑𝓧 μ).continuous hΨ_cont)

end ProbabilityTheory.Kernel
