module

public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Set.Prod

@[expose] public section

namespace Set
variable {ι α : Type*} [DecidableEq ι]

lemma setOf_forall_notMem_eq_pi_sdiff (s t : Finset ι) (u : ι → Set α) :
    {f : ι → α | ∀ i ∈ s, i ∉ t → f i ∈ u i} = ((s \ t : Finset ι) : Set ι).pi u := by
  ext; simp [mem_pi]

end Set
