import Mathlib.Data.List.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_736

open PEqualNP.CircuitLowerBounds

private def extend (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def reindex (psi : ℕ → ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map psi }

private lemma getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases lt : i < w.length
  · simp [List.getD, List.getElem?_append_left lt, Nat.ne_of_lt lt]
  · rw [List.getD, List.getElem?_append_right (by omega)]
    by_cases eq : i = w.length
    · simp [eq]
    · have a : w.length ≤ i := by omega
      have b : [b].length ≤ i - w.length := by simp; omega
      simp [eq, List.getD, List.getElem?_eq_none a, List.getElem?_eq_none b]

private lemma fold_preserves (psi : ℕ → ℕ) (n n' m : ℕ)
    (pin : ∀ t : ℕ, t < m → ∀ i : ℕ, psi i = n' + t ↔ i = n + t)
    (gs : List Gate) (t : ℕ) (w w' : List Bool)
    (ht : t + gs.length ≤ m) (hw : w.length = n + t) (hw' : w'.length = n' + t)
    (same : ∀ i, w'.getD (psi i) false = w.getD i false) :
    ∀ i, ((gs.map (reindex psi)).foldl extend w').getD (psi i) false =
      (gs.foldl extend w).getD i false := by
  induction gs generalizing t w w' with
  | nil => exact same
  | cons g rest ih =>
    have htm : t < m := by simp at ht; omega
    have hin :
        (g.inputs.map psi).map (fun j => w'.getD j false) =
          g.inputs.map (fun j => w.getD j false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => same i)
    apply ih (t + 1) (extend w g) (extend w' (reindex psi g))
    · simp at ht
      omega
    · simp [extend, hw]; omega
    · simp [extend, hw']; omega
    · intro i
      simp only [extend, reindex, getD_snoc, hw, hw', hin, pin t htm i, same i]

end PEqualNP.Outside.L_meta_736

theorem PEqualNP.Outside.L_meta_736 : ∀ (n n' : ℕ) (O : Finset (Fin n)) (e : Fin n' → Fin n), StrictMono e →
  (∀ k : Fin n, k ∉ O ↔ ∃ j : Fin n', e j = k) → n' + O.card = n →
  ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
  ∃ psi : ℕ → ℕ, ∀ x x' : List Bool, x.length = n → x'.length = n' →
    (∀ k ∈ O, x.getD (k : ℕ) false = true) →
    (∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) →
    (∀ i : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := 0 } x').getD (psi i) false
      = (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false) ∧
    (∀ o : ℕ, PEqualNP.CircuitLowerBounds.Circuit.eval
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := psi o } x'
      = PEqualNP.CircuitLowerBounds.Circuit.eval { gates := gates, output := o } x) := by
  classical
  open PEqualNP.Outside.L_meta_736 in
  open PEqualNP.CircuitLowerBounds in
  intro n n' O e _ image _ gates
  let m := gates.length
  let onInput (i : ℕ) := ∃ j : Fin n', (e j).val = i
  let psi (i : ℕ) : ℕ :=
    if h : onInput i then h.choose.val
    else if i < n then n' else n' + 1 + (i - n)
  have pin (t : ℕ) (_ht : t < m) (i : ℕ) :
      psi i = (n' + 1) + t ↔ i = n + t := by
    unfold psi
    split
    next he =>
      have hj := he.choose.isLt
      have hi : i < n := he.choose_spec ▸ (e he.choose).isLt
      omega
    next _ =>
      split
      next hi => omega
      next hn => omega
  refine ⟨psi, ?_⟩
  intro x x' hx hx' hO he
  have base (i : ℕ) : (x' ++ [true]).getD (psi i) false = x.getD i false := by
    by_cases himage : onInput i
    · rw [show psi i = himage.choose.val by exact dite_eq_left himage,
        getD_snoc, hx']
      rw [if_neg (Nat.ne_of_lt himage.choose.isLt)]
      simpa only [himage.choose_spec] using (he himage.choose).symm
    · by_cases iold : i < n
      · have hpsi : psi i = n' := by
          rw [show psi i = _ by exact dite_eq_right himage, if_pos iold]
        rw [hpsi, getD_snoc, hx', if_pos rfl]
        let k : Fin n := ⟨i, iold⟩
        have hk : k ∈ O := by
          by_contra hn
          obtain ⟨j, hj⟩ := (image k).mp hn
          exact himage ⟨j, congrArg Fin.val hj⟩
        exact (hO k hk).symm
      · have hpsi : n' + 1 ≤ psi i := by
          rw [show psi i = _ by exact dite_eq_right himage, if_neg iold]
          omega
        have hnew : (x' ++ [true]).length ≤ psi i := by
          simpa only [List.length_append, List.length_singleton, hx'] using hpsi
        have hold : x.length ≤ i := by omega
        simp [List.getD, List.getElem?_eq_none hnew, List.getElem?_eq_none hold]
  have output := fold_preserves psi n (n' + 1) m pin gates 0 x (x' ++ [true])
    (by simp [m]) (by simpa using hx) (by simp [hx']) base
  constructor
  · exact output
  · intro o
    exact output o
