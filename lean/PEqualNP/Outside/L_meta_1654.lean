import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1654

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi
    exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hi hv⟩

lemma run_mono (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w w' : List Bool), w.length = w'.length →
      (∀ i, w.getD i false = true → w'.getD i false = true) →
      ∀ i, (run gs w).getD i false = true → (run gs w').getD i false = true := by
  induction gs with
  | nil =>
    intro w w' _ h i hi
    exact h i hi
  | cons g gs ih =>
    intro w w' hlen h i hi
    have hstep : run (g :: gs) w =
        run gs (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) := rfl
    have hstep' : run (g :: gs) w' =
        run gs (w' ++ [g.op.eval (g.inputs.map fun j => w'.getD j false)]) := rfl
    rw [hstep] at hi
    rw [hstep']
    apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem g hg')) _ _
      (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact h j hj
    · by_cases heq : j = w.length
      · subst j
        have hs : ∀ (l : List Bool) (b : Bool), (l ++ [b]).getD l.length false = b := by
          intro l b
          simp
        rw [hs] at hj
        rw [hlen, hs]
        exact gate_mono g (hm g List.mem_cons_self) w w' (fun k _ => h k) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

lemma wire_mono {n : ℕ} (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) (i : ℕ)
    (hi : (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false = true) :
    (Circuit.wires ⟨gs, 0⟩ (List.ofFn y)).getD i false = true := by
  refine run_mono gs hm (List.ofFn x) (List.ofFn y) (by simp) ?_ i hi
  intro j hj
  by_cases hlt : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at hj
    rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
    simp only [List.getElem_ofFn] at hj ⊢
    exact hxy ⟨j, hlt⟩ hj
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
    exact Bool.noConfusion hj

end PEqualNP.Outside.L_meta_1654

theorem PEqualNP.Outside.L_meta_1654 :
  ∀ (n L : ℕ) (line : Fin L → Finset (Fin n)) (l : Fin L) (gates : List PEqualNP.CircuitLowerBounds.Gate) (G K : ℕ) (I : Finset (Fin n)),
  (∀ p r : Fin n, p ≠ r → ∃! j : Fin L, p ∈ line j ∧ r ∈ line j) →
  (∀ j j' : Fin L, j ≠ j' → (line j ∩ line j').card = 1) →
  (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
  (∀ k : ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g → ∀ i ∈ g.inputs, i < n + k) →
  (¬ ∃ X : Finset (Fin n), Disjoint X (line l) ∧
      (∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) ∧
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD G false = true ∧
      (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ X)))).getD K false = true) →
  Disjoint I (line l) →
  (∀ a ∈ I, ∀ b ∈ I, ∀ c ∈ I, a ≠ b → a ≠ c → b ≠ c → ¬ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ c ∈ line j) →
  (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u ∈ I)))).getD K false = true →
  ∀ v : Fin n, v ∉ line l →
    (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u : Fin n => decide (u = v)))).getD G false = true →
    v ∉ I ∧ ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ ∃ j : Fin L, a ∈ line j ∧ b ∈ line j ∧ v ∈ line j := by
  classical
  intro n L line l gates G K I _ _ hops _ hno hIdis hIarc hIK v hvl hvG
  have hm : ∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g hg => (hops g hg).1
  constructor
  · intro hvI
    apply hno
    refine ⟨I, hIdis, hIarc, ?_, hIK⟩
    refine PEqualNP.Outside.L_meta_1654.wire_mono gates hm
      (fun u : Fin n => decide (u = v)) _ ?_ G hvG
    intro u hu
    have huv : u = v := of_decide_eq_true hu
    simpa only [decide_eq_true_eq, huv] using hvI
  · by_contra hsec
    apply hno
    refine ⟨insert v I, ?_, ?_, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro u hu hul
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hvl hul
      · exact Finset.disjoint_left.mp hIdis hu hul
    · intro a ha b hb c hc hab hac hbc hcol
      obtain ⟨j, haj, hbj, hcj⟩ := hcol
      rcases Finset.mem_insert.mp ha with ha | ha
      · have hbI : b ∈ I := (Finset.mem_insert.mp hb).resolve_left
          (fun hbv => hab (ha.trans hbv.symm))
        have hcI : c ∈ I := (Finset.mem_insert.mp hc).resolve_left
          (fun hcv => hac (ha.trans hcv.symm))
        exact hsec ⟨b, hbI, c, hcI, hbc, j, hbj, hcj, ha ▸ haj⟩
      · rcases Finset.mem_insert.mp hb with hb | hb
        · have hcI : c ∈ I := (Finset.mem_insert.mp hc).resolve_left
            (fun hcv => hbc (hb.trans hcv.symm))
          exact hsec ⟨a, ha, c, hcI, hac, j, haj, hcj, hb ▸ hbj⟩
        · rcases Finset.mem_insert.mp hc with hc | hc
          · exact hsec ⟨a, ha, b, hb, hab, j, haj, hbj, hc ▸ hcj⟩
          · exact hIarc a ha b hb c hc hab hac hbc ⟨j, haj, hbj, hcj⟩
    · refine PEqualNP.Outside.L_meta_1654.wire_mono gates hm
        (fun u : Fin n => decide (u = v)) _ ?_ G hvG
      intro u hu
      have huv : u = v := of_decide_eq_true hu
      simp [huv]
    · refine PEqualNP.Outside.L_meta_1654.wire_mono gates hm
        (fun u : Fin n => decide (u ∈ I)) _ ?_ K hIK
      intro u hu
      apply decide_eq_true_eq.mpr
      exact Finset.mem_insert_of_mem (of_decide_eq_true hu)
