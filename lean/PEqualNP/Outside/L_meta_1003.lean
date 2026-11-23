import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1003

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 2]⟩,
      ⟨GateOp.or, [8, 5]⟩,
      ⟨GateOp.and, [1, 9]⟩,
      ⟨GateOp.or, [3, 6]⟩,
      ⟨GateOp.and, [2, 11]⟩,
      ⟨GateOp.or, [0, 6]⟩,
      ⟨GateOp.or, [13, 7]⟩,
      ⟨GateOp.and, [4, 14]⟩,
      ⟨GateOp.or, [3, 5]⟩,
      ⟨GateOp.and, [7, 16]⟩,
      ⟨GateOp.or, [10, 12]⟩,
      ⟨GateOp.or, [15, 17]⟩,
      ⟨GateOp.or, [18, 19]⟩],
    output := 20 }

lemma fan : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma eval (a b c d e f g h : Bool) :
    circuit.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (b && c) || (c && d) || (a && e) || (b && f) ||
      (c && g) || (d && h) || (e && g) || (f && h) || (h && e)) := by
  simp only [circuit, Circuit.eval, Circuit.wires,
    List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append,
    List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil,
    id, Bool.and_true, Bool.or_false]
  cases a <;> cases b <;> cases c <;> cases d <;>
    cases e <;> cases f <;> cases g <;> cases h <;> rfl

lemma inputs (x : Fin 8 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

end PEqualNP.Outside.L_meta_1003

theorem PEqualNP.Outside.L_meta_1003 :
    PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 13 := by
  refine ⟨PEqualNP.Outside.L_meta_1003.circuit,
    PEqualNP.Outside.L_meta_1003.fan, by decide, ?_⟩
  intro x
  rw [PEqualNP.Outside.L_meta_1003.inputs]
  exact PEqualNP.Outside.L_meta_1003.eval (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
