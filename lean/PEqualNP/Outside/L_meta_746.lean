import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_746

open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.EdgeUpper

def f (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)

lemma depends : ∀ i : Fin 4, ∃ x : Fin 4 → Bool,
    f (Function.update x i (!x i)) ≠ f x := by
  decide

lemma upper : HasCircuitSize 4 f 3 := by
  apply bld_hasCircuitSize
  have h : Bld 4 (fun x => x 0 && ((x 1 || x 2) || x 3)) 3 :=
    bld_and (bld_var 0)
      (bld_or (bld_or (bld_var 1) (bld_var 2)) (bld_var 3))
  refine bld_congr h ?_
  intro x
  cases hx : x 0 <;> simp [f, hx]

end PEqualNP.Outside.L_meta_746

theorem PEqualNP.Outside.L_meta_746 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4
      (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) s ↔
      3 ≤ s := by
  intro s
  constructor
  · intro h
    have hb := PEqualNP.MetaComplexity.Helpers.dep_lower 4
      PEqualNP.Outside.L_meta_746.f PEqualNP.Outside.L_meta_746.depends s h
    omega
  · intro hs
    obtain ⟨C, hok, hsize, heval⟩ := PEqualNP.Outside.L_meta_746.upper
    exact ⟨C, hok, le_trans hsize hs, heval⟩
