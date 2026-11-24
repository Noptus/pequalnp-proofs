import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2352

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : ReadsBack n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hC j hj i hi)]

lemma or_true (n : ℕ) (C : Circuit) (z : Fin n → Bool) (hC : ReadsBack n C)
    (j a : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (ha : a ∈ (gateAt C j).inputs) (hv : wv n C z a = true) :
    wv n C z (n + j) = true := by
  rw [wv_rec n C z hC j hj, hop]
  apply List.any_eq_true.mpr
  exact ⟨wv n C z a, List.mem_map.mpr ⟨a, ha, rfl⟩, hv⟩

lemma and_true (n : ℕ) (C : Circuit) (z : Fin n → Bool) (hC : PEqualNP.TopForm.IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (h0 : wv n C z ((gateAt C j).inputs.getD 0 0) = true)
    (h1 : wv n C z ((gateAt C j).inputs.getD 1 0) = true) :
    wv n C z (n + j) = true := by
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hC.2.2 _ hmem)
  have ha : wv n C z a = true := by simpa [hab] using h0
  have hb : wv n C z b = true := by simpa [hab] using h1
  rw [wv_rec n C z hC.2.1 j hj, hop, hab]
  simp [GateOp.eval, ha, hb]

end PEqualNP.Outside.L_meta_2352

open PEqualNP.Outside.L_meta_2352

theorem PEqualNP.Outside.L_meta_2352 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → ∀ R : ℕ → ℕ → Prop, R = Relation.ReflTransGen (fun ra rb => ra < rb ∧ ∃ rj, rb = n + rj ∧ rj < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ra ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C rj).inputs) → ∀ T : ℕ → List (ℕ × ℕ) → Prop, T = (fun tt tL => ∀ Q : ℕ → List (ℕ × ℕ) → Prop, (∀ (qv qt : ℕ), qv < n → R qv qt → Q qt [(qt, qv)]) → (∀ (qj qt : ℕ) (qL1 qL2 : List (ℕ × ℕ)), qj < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C qj).op = PEqualNP.CircuitLowerBounds.GateOp.and → R (n + qj) qt → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 0 0) qL1 → Q ((PEqualNP.MetaComplexity.NestedCover.gateAt C qj).inputs.getD 1 0) qL2 → Q qt (qL1 ++ qL2)) → Q tt tL) → ∀ (top : ℕ) (L : List (ℕ × ℕ)) (z : Fin n → Bool), T top L → (∀ gv ∈ L, (C.wires (List.ofFn z)).getD (gv.1) false = true) → (C.wires (List.ofFn z)).getD (top) false = true := by
  intro n C hC R hR T hT top L z hs hz
  have hprop : ∀ a b, R a b → wv n C z a = true → wv n C z b = true := by
    intro a b hab
    rw [hR] at hab
    induction hab with
    | refl => exact fun h => h
    | @tail u v hau huv ih =>
      intro ha
      rcases huv with ⟨_, j, rfl, hj, hop, hu⟩
      exact or_true n C z hC.2.1 j u hj hop hu (ih ha)
  rw [hT] at hs
  apply hs (fun t l => (∀ gv ∈ l, wv n C z gv.1 = true) → wv n C z t = true) ?_ ?_ hz
  · intro qv qt _ _ hall
    exact hall (qt, qv) (by simp)
  · intro qj qt qL1 qL2 hj hop hr h1 h2 hall
    apply hprop (n + qj) qt hr
    apply and_true n C z hC qj hj hop
    · apply h1
      intro gv hgv
      exact hall gv (List.mem_append.mpr (Or.inl hgv))
    · apply h2
      intro gv hgv
      exact hall gv (List.mem_append.mpr (Or.inr hgv))
