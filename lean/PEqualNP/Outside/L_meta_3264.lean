import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3264

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wf (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma wf_len (gs : List Gate) :
    ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    change (wf gs (step w g)).length = _
    rw [ih]
    simp [step] <;> omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    change (wf gs (step w g)).getD i false = _
    rw [ih _ _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma getD_snoc_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma output_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (h : circuitFun n C x = true) : C.output < n + C.size := by
  by_contra hn
  have hlen : (C.wires (List.ofFn x)).length = n + C.size := by
    exact (wf_len C.gates (List.ofFn x)).trans (by simp [Circuit.size])
  have hd : (C.wires (List.ofFn x)).getD C.output false = false := by
    apply List.getD_eq_default
    omega
  change (C.wires (List.ofFn x)).getD C.output false = true at h
  rw [hd] at h
  cases h

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp),
      List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp),
      List.getD_eq_default _ _ (by simp; omega)]

lemma relabel_fun (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    circuitFun m (relabel n m π C) x = circuitFun n C (x ∘ π) := by
  exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

lemma wmap_lt (n m : ℕ) (π : Fin n → Fin m) (w k : ℕ)
    (hw : w < n + k) : wmap n m π w < m + k := by
  unfold wmap
  split
  · have := (π ⟨w, by assumption⟩).isLt
    omega
  · omega

lemma relabel_ao2 (n m : ℕ) (π : Fin n → Fin m) (C : Circuit)
    (h : IsAO2 n C) : IsAO2 m (relabel n m π C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact h.1 g0 hg0
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa [relabel] using hj
    have he : gateAt (relabel n m π C) j = relGate n m π (gateAt C j) := by
      unfold gateAt relabel
      rw [List.getD_eq_getElem _ _ (by simpa using hj'),
        List.getD_eq_getElem _ _ hj']
      simp only [List.getElem_map]
    rw [he] at hi
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hi
    exact wmap_lt n m π w j (h.2.1 j hj' w hw)
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    simpa [relGate] using h.2.2 g0 hg0

def extend (n : ℕ) (C : Circuit) (g : Gate) : Circuit :=
  ⟨C.gates ++ [g], n + C.gates.length⟩

lemma extend_ao2 (n : ℕ) (C : Circuit) (g : Gate) (h : IsAO2 n C)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2)
    (hb : ∀ i ∈ g.inputs, i < n + C.gates.length) : IsAO2 n (extend n C g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact h.1 g' hg'
    · have he : g' = g := List.mem_singleton.mp hg'
      subst g'
      exact hop
  · intro j hj i hi
    have hj' : j < C.gates.length + 1 := by simpa [extend] using hj
    by_cases hlt : j < C.gates.length
    · have he : gateAt (extend n C g) j = gateAt C j := by
        simp [gateAt, extend, List.getD, List.getElem?_append_left hlt]
      rw [he] at hi
      exact h.2.1 j hlt i hi
    · have heq : j = C.gates.length := by omega
      subst j
      have he : gateAt (extend n C g) C.gates.length = g := by
        simp [gateAt, extend, List.getD]
      rw [he] at hi
      exact hb i hi
  · intro g' hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact h.2.2 g' hg'
    · have he : g' = g := List.mem_singleton.mp hg'
      subst g'
      exact hlen

lemma extend_fun (n : ℕ) (C : Circuit) (g : Gate) (x : Fin n → Bool) :
    circuitFun n (extend n C g) x =
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
  have hlen : (wf C.gates (List.ofFn x)).length = n + C.gates.length := by
    rw [wf_len, List.length_ofFn]
  change ((C.gates ++ [g]).foldl step (List.ofFn x)).getD
    (n + C.gates.length) false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (step (wf C.gates (List.ofFn x)) g).getD (n + C.gates.length) false = _
  unfold step
  rw [← hlen]
  exact getD_snoc_eq _ _

lemma extend_keep (n : ℕ) (C : Circuit) (g : Gate) (x : Fin n → Bool)
    (i : ℕ) (hi : i < n + C.gates.length) :
    ((extend n C g).wires (List.ofFn x)).getD i false =
      (C.wires (List.ofFn x)).getD i false := by
  change ((C.gates ++ [g]).foldl step (List.ofFn x)).getD i false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  apply List.getD_append
  change i < (wf C.gates (List.ofFn x)).length
  rw [wf_len, List.length_ofFn]
  exact hi

lemma wire_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  change (wf C.gates (List.ofFn x)).getD i.val false = _
  rw [wf_keep _ _ _ (by simpa using i.isLt)]
  simp [List.getD]

lemma attach_pair (n : ℕ) (C : Circuit) (i j : Fin n) (h : IsAO2 n C)
    (ho : C.output < n + C.size) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size + 2 ∧ D.output < n + D.size ∧
      ∀ x : Fin n → Bool,
        circuitFun n D x = (circuitFun n C x || (x i && x j)) := by
  let A := extend n C ⟨GateOp.and, [i.val, j.val]⟩
  have hA : IsAO2 n A := by
    apply extend_ao2 n C _ h (Or.inl rfl) rfl
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> omega
  let D := extend n A ⟨GateOp.or, [C.output, A.output]⟩
  have hD : IsAO2 n D := by
    apply extend_ao2 n A _ hA (Or.inr rfl) rfl
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp only [A, extend, List.length_append, List.length_singleton]
      have ho' : C.output < n + C.gates.length := ho
      omega
    · simp [A, extend]
  refine ⟨D, hD, ?_, ?_, ?_⟩
  · simp [D, A, extend, Circuit.size] <;> omega
  · simp [D, extend, Circuit.size]
  · intro x
    have hOld : (A.wires (List.ofFn x)).getD C.output false = circuitFun n C x := by
      exact extend_keep n C _ x C.output ho
    have hNew : (A.wires (List.ofFn x)).getD A.output false = (x i && x j) := by
      change circuitFun n A x = _
      change circuitFun n (extend n C ⟨GateOp.and, [i.val, j.val]⟩) x = _
      rw [extend_fun]
      change GateOp.and.eval [(C.wires (List.ofFn x)).getD i.val false,
        (C.wires (List.ofFn x)).getD j.val false] = (x i && x j)
      rw [wire_input n C x i, wire_input n C x j]
      cases x i <;> cases x j <;> rfl
    change circuitFun n (extend n A ⟨GateOp.or, [C.output, A.output]⟩) x = _
    rw [extend_fun]
    change GateOp.or.eval [(A.wires (List.ofFn x)).getD C.output false,
      (A.wires (List.ofFn x)).getD A.output false] =
        (circuitFun n C x || (x i && x j))
    rw [hOld, hNew]
    cases circuitFun n C x <;> cases x i <;> cases x j <;> rfl

lemma attach_pairs (N : ℕ) (C : Circuit) (h : IsAO2 (N + N) C)
    (ho : C.output < N + N + C.size) (S : Finset (Fin N × Fin N)) :
    ∃ D : Circuit, IsAO2 (N + N) D ∧ D.size ≤ C.size + 2 * S.card ∧
      D.output < N + N + D.size ∧ ∀ x : Fin (N + N) → Bool,
        circuitFun (N + N) D x = true ↔ circuitFun (N + N) C x = true ∨
          ∃ i j : Fin N, (i, j) ∈ S ∧
            x (Fin.castAdd N i) = true ∧ x (Fin.natAdd N j) = true := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨C, h, by simp, ho, ?_⟩
    intro x
    simp
  | @insert e S he ih =>
    rcases e with ⟨a, b⟩
    obtain ⟨D, hD, hsD, hoD, hvD⟩ := ih
    obtain ⟨D', hD', hsD', hoD', hvD'⟩ :=
      attach_pair (N + N) D (Fin.castAdd N a) (Fin.natAdd N b) hD hoD
    refine ⟨D', hD', ?_, hoD', ?_⟩
    · rw [Finset.card_insert_of_notMem he]
      omega
    · intro x
      rw [hvD' x, Bool.or_eq_true, Bool.and_eq_true, hvD x]
      constructor
      · rintro ((hc | ⟨i, j, hij, hi, hj⟩) | ⟨ha, hb⟩)
        · exact Or.inl hc
        · exact Or.inr ⟨i, j, Finset.mem_insert_of_mem hij, hi, hj⟩
        · exact Or.inr ⟨a, b, Finset.mem_insert_self _ _, ha, hb⟩
      · rintro (hc | ⟨i, j, hij, hi, hj⟩)
        · exact Or.inl (Or.inl hc)
        · rcases Finset.mem_insert.mp hij with heq | hij
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
            exact Or.inr ⟨hi, hj⟩
          · exact Or.inl (Or.inr ⟨i, j, hij, hi, hj⟩)

end PEqualNP.Outside.L_meta_3264

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3264

theorem PEqualNP.Outside.L_meta_3264 :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      x3.Nonempty →
        PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →
          (∀ (x7 : Fin (x1 + x2) → Bool),
            PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 =
              Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2),
                (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧
                  x7 (Fin.natAdd x1 x9) = Bool.true)) →
            let x8 : ℕ := x1 + x2;
            have x9 : Finset (Fin (x1 + x2) × Fin (x1 + x2)) :=
              Finset.image (fun (x9 : Fin x1 × Fin x2) =>
                (Fin.castAdd x2 x9.1, Fin.natAdd x1 x9.2)) x3;
            ∀ (x10 : Finset (Fin x8 × Fin x8)),
              ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit),
                PEqualNP.TopForm.IsAO2 (x8 + x8) x11 ∧
                  x11.size ≤ x4.size + (2 : ℕ) * x10.card ∧
                    ∀ (x12 : Fin (x8 + x8) → Bool),
                      PEqualNP.MetaComplexity.circuitFun (x8 + x8) x11 x12 =
                        Decidable.decide (∃ (x13 : Fin (x1 + x2)) (x14 : Fin (x1 + x2)),
                          (x13, x14) ∈ x9 ∪ x10 ∧
                            x12 (Fin.castAdd x8 x13) = Bool.true ∧
                              x12 (Fin.natAdd x8 x14) = Bool.true) := by
  classical
  intro n m E C hE hC hfun
  dsimp only
  intro S
  let N := n + m
  let π : Fin N → Fin (N + N) := fun i =>
    if i.val < n then Fin.castAdd N i else Fin.natAdd N i
  have hπl (a : Fin n) :
      π (Fin.castAdd m a) = Fin.castAdd N (Fin.castAdd m a) := by
    simp [π, a.isLt]
  have hπr (b : Fin m) :
      π (Fin.natAdd n b) = Fin.natAdd N (Fin.natAdd n b) := by
    have hn : ¬ (Fin.natAdd n b).val < n := by
      change ¬ n + b.val < n
      omega
    simp only [π, ite_eq_right hn]
  let B := relabel N (N + N) π C
  have hB : IsAO2 (N + N) B := relabel_ao2 N (N + N) π C hC
  have ht : circuitFun N C (fun _ => true) = true := by
    rw [hfun]
    apply decide_eq_true_iff.mpr
    obtain ⟨⟨a, b⟩, hab⟩ := hE
    exact ⟨a, b, hab, rfl, rfl⟩
  have hoC := output_lt N C (fun _ => true) ht
  have hsize : B.size = C.size := by simp [B, relabel, Circuit.size]
  have hoB : B.output < N + N + B.size := by
    rw [hsize]
    exact wmap_lt N (N + N) π C.output C.size hoC
  let T : Finset (Fin N × Fin N) :=
    E.image (fun e => (Fin.castAdd m e.1, Fin.natAdd n e.2))
  have hvB (x : Fin (N + N) → Bool) :
      circuitFun (N + N) B x = true ↔ ∃ i j : Fin N, (i, j) ∈ T ∧
        x (Fin.castAdd N i) = true ∧ x (Fin.natAdd N j) = true := by
    change circuitFun (N + N) (relabel N (N + N) π C) x = true ↔ _
    rw [relabel_fun, hfun, decide_eq_true_iff]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      refine ⟨Fin.castAdd m a, Fin.natAdd n b,
        Finset.mem_image.mpr ⟨(a, b), hab, rfl⟩, ?_, ?_⟩
      · simpa only [Function.comp_apply, hπl] using ha
      · simpa only [Function.comp_apply, hπr] using hb
    · rintro ⟨i, j, hij, hi, hj⟩
      obtain ⟨⟨a, b⟩, hab, hp⟩ := Finset.mem_image.mp hij
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      refine ⟨a, b, hab, ?_, ?_⟩
      · simpa only [Function.comp_apply, hπl] using hi
      · simpa only [Function.comp_apply, hπr] using hj
  obtain ⟨D, hD, hsD, _, hvD⟩ := attach_pairs N B hB hoB S
  refine ⟨D, hD, ?_, ?_⟩
  · simpa only [hsize] using hsD
  · intro x
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_iff, hvD x, hvB x]
    change (∃ i j : Fin N, (i, j) ∈ T ∧
      x (Fin.castAdd N i) = true ∧ x (Fin.natAdd N j) = true) ∨
      (∃ i j : Fin N, (i, j) ∈ S ∧
        x (Fin.castAdd N i) = true ∧ x (Fin.natAdd N j) = true) ↔
      ∃ i j : Fin N, (i, j) ∈ T ∪ S ∧
        x (Fin.castAdd N i) = true ∧ x (Fin.natAdd N j) = true
    simp only [Finset.mem_union, or_and_right, exists_or]
