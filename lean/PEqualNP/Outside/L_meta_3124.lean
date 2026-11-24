import PEqualNP.Defs
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_3124

open PEqualNP.CircuitLowerBounds

private def target (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
  x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
  x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5

private def neighbor (j : Fin 9) : Fin 9 :=
  if j = 0 then 1 else if j = 1 then 0 else if j = 2 then 1 else
  if j = 3 then 2 else if j = 4 then 3 else if j = 5 then 0 else
  if j = 6 then 1 else if j = 7 then 2 else 3

private lemma essential (j : Fin 9) :
    ∃ x y : Fin 9 → Bool,
      (∀ k, k ≠ j → x k = y k) ∧ target x ≠ target y := by
  refine ⟨(fun k => decide (k = neighbor j)),
    (fun k => decide (k = neighbor j ∨ k = j)), ?_, ?_⟩
  · intro k hk
    simp [hk]
  · fin_cases j <;> decide

private def base (x : Fin 9 → Bool) : List Bool :=
  List.ofFn x ++ [!x 0]

private def initial (p : List ℕ) (x : Fin 9 → Bool) : List Bool :=
  base x ++ [GateOp.or.eval (p.map fun i => (base x).getD i false)]

private lemma fresh (s : List ℕ) (hs : s.length < 9) :
    ∃ j : Fin 9, j.val ∉ s := by
  classical
  by_contra hn
  have hsub : Finset.range 9 ⊆ s.toFinset := by
    intro i hi
    have hi9 : i < 9 := Finset.mem_range.mp hi
    have hm : i ∈ s := Classical.not_not.mp (fun h => hn ⟨⟨i, hi9⟩, h⟩)
    simpa using hm
  have hc := Finset.card_le_card hsub
  have hl := List.toFinset_card_le s
  simp only [Finset.card_range] at hc
  omega

private lemma snoc_agree (u v : List Bool) (a b : Bool) (j : ℕ)
    (hlen : u.length = v.length) (hab : a = b)
    (h : ∀ i, i ≠ j → u.getD i false = v.getD i false) :
    ∀ i, i ≠ j → (u ++ [a]).getD i false = (v ++ [b]).getD i false := by
  intro i hi
  by_cases hil : i < u.length
  · rw [List.getD_append _ _ _ _ hil,
      List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hlen, hab]

private lemma raw_get (x : Fin 9 → Bool) (i : ℕ) (hi : i < 9) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

private lemma base_agree (x y : Fin 9 → Bool) (j : Fin 9)
    (hj : j.val ≠ 0) (hxy : ∀ k, k ≠ j → x k = y k) :
    ∀ i, i ≠ j.val → (base x).getD i false = (base y).getD i false := by
  apply snoc_agree
  · simp
  · have h0 : (0 : Fin 9) ≠ j := by
      intro he
      exact hj (congrArg Fin.val he).symm
    rw [hxy 0 h0]
  · intro i hi
    by_cases hi9 : i < 9
    · rw [raw_get x i hi9, raw_get y i hi9]
      apply hxy
      intro he
      exact hi (congrArg Fin.val he)
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

private lemma initial_agree (p : List ℕ) (x y : Fin 9 → Bool) (j : Fin 9)
    (hj : j.val ≠ 0) (hjp : j.val ∉ p)
    (hxy : ∀ k, k ≠ j → x k = y k) :
    ∀ i, i ≠ j.val → (initial p x).getD i false = (initial p y).getD i false := by
  have hb := base_agree x y j hj hxy
  apply snoc_agree
  · simp [base]
  · congr 1
    apply List.map_congr_left
    intro i hi
    apply hb i
    intro he
    exact hjp (he ▸ hi)
  · exact hb

private lemma circuit_agree (C : Circuit)
    (hno : ¬∃ g : Gate, C.gates[1]? = some g)
    (u v : List Bool) (j : ℕ) (hlen : u.length = v.length)
    (h : ∀ i, i ≠ j → u.getD i false = v.getD i false)
    (hout : C.output ≠ j)
    (hpins : ∀ g ∈ C.gates, j ∉ g.inputs) :
    C.eval u = C.eval v := by
  rcases C with ⟨gs, out⟩
  cases gs with
  | nil => exact h out hout
  | cons g rest =>
    cases rest with
    | cons g' tail => exact (hno ⟨g', by simp⟩).elim
    | nil =>
      change (u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]).getD out false =
        (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]).getD out false
      apply snoc_agree _ _ _ _ j hlen _ h out hout
      congr 1
      apply List.map_congr_left
      intro i hi
      apply h i
      intro he
      exact hpins g (by simp) (he ▸ hi)

private lemma short_reads (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hno : ¬∃ g : Gate, C.gates[1]? = some g) :
    (C.gates.flatMap Gate.inputs).length ≤ 2 := by
  rcases C with ⟨gs, out⟩
  cases gs with
  | nil => simp
  | cons g rest =>
    cases rest with
    | cons g' tail => exact (hno ⟨g', by simp⟩).elim
    | nil => simpa using (hfan g (by simp)).2

private lemma obstruction (p : List ℕ) (hp : p.length ≤ 2)
    (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hno : ¬∃ g : Gate, C.gates[1]? = some g) :
    ∃ x : Fin 9 → Bool, C.eval (initial p x) ≠ target x := by
  classical
  have hr := short_reads C hfan hno
  have hshort : (0 :: C.output :: (p ++ C.gates.flatMap Gate.inputs)).length < 9 := by
    simp only [List.length_cons, List.length_append]
    omega
  obtain ⟨j, hj⟩ := fresh _ hshort
  simp only [List.mem_cons, List.mem_append, not_or] at hj
  rcases hj with ⟨hj0, hjout, hjp, hjg⟩
  obtain ⟨x, y, hxy, hdiff⟩ := essential j
  have heval : C.eval (initial p x) = C.eval (initial p y) := by
    apply circuit_agree C hno _ _ j.val
    · simp [initial, base]
    · exact initial_agree p x y j hj0 hjp hxy
    · exact Ne.symm hjout
    · intro g hg hm
      exact hjg (List.mem_flatMap.mpr ⟨g, hg, hm⟩)
  by_contra hn
  have hc : ∀ z : Fin 9 → Bool, C.eval (initial p z) = target z := by
    intro z
    exact Classical.not_not.mp (fun hz => hn ⟨z, hz⟩)
  exact hdiff ((hc x).symm.trans (heval.trans (hc y)))

end PEqualNP.Outside.L_meta_3124

theorem PEqualNP.Outside.L_meta_3124 : ∀ (x1 : List ℕ),
    x1.length ≤ (2 : ℕ) →
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x3 →
          x3.size ≤ (13 : ℕ) →
            (¬∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[(1 : ℕ)]? = Option.some x6) →
              ∃ (x7 : Fin (9 : ℕ) → Bool),
                have x8 : List Bool := List.ofFn x7 ++ [!x7 (0 : Fin (9 : ℕ))];
                x3.eval (x8 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
                  (List.map (fun (x9 : ℕ) => x8.getD x9 Bool.false) x1)]) ≠
                  (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) ||
                  x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) ||
                  x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) ||
                  x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) ||
                  x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) ||
                  x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) ||
                  x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) ||
                  x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) ||
                  x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) ||
                  x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) ||
                  x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) ||
                  x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro x1 h1 x3 hfan _ hno
  exact PEqualNP.Outside.L_meta_3124.obstruction x1 h1 x3 hfan hno
