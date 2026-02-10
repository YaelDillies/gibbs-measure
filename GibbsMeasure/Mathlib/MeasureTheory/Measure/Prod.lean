module

public import Mathlib.MeasureTheory.Measure.Prod

public section

namespace MeasureTheory.Measure
variable (X Y : Type*) [MeasurableSpace X] [MeasurableSpace Y]

lemma eq_prod_of_dirac_right (ν : Measure X) (y : Y) (μ : Measure (X × Y))
    (marg_X : Measure.map Prod.fst μ = ν) (marg_Y : Measure.map Prod.snd μ = Measure.dirac y) :
    μ = ν.prod (Measure.dirac y) := by
-- dynkin's pi system lemma
  sorry

lemma eq_prod_of_dirac_left (x : X) (ν : Measure Y) (μ : Measure (X × Y))
    (marg_X : Measure.map Prod.fst μ = Measure.dirac x) (marg_Y : Measure.map Prod.snd μ = ν) :
    μ = (Measure.dirac x).prod ν := by
  sorry

end MeasureTheory.Measure
