module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

public section

open TopologicalSpace MeasureTheory Filter
open scoped NNReal ENNReal Topology ComplexConjugate

variable {α ε ε' E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [ENorm ε] [ENorm ε']

namespace MeasureTheory

attribute [simp] memLp_top_const MemLp.indicator

@[simp] lemma memLp_top_one [One E] : MemLp (1 : α → E) ⊤ μ := memLp_top_const _

end MeasureTheory
