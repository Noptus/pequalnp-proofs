import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1495

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def ev (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [ev w g]) w

lemma run_append (a b : List Gate) (w : List Bool) :
    run (a ++ b) w = run b (run a w) := by
  simp [run, List.foldl_append]

lemma run_start (gs : List Gate) (w : List Bool) :
    ∃ t : List Bool, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (w ++ [ev w g])
    refine ⟨ev w g :: t, ?_, by simp [hl]⟩
    change run gs (w ++ [ev w g]) = _
    rw [ht]
    simp

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_start gs w
  simp [ht, hl]

lemma run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_start gs w
  rw [ht, List.getD_append _ _ _ _ hi]

lemma getD_snoc_ne (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases h : i < w.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

def redirect (k p i : ℕ) : ℕ :=
  if i = k then p else if k < i then i - 1 else i

def rename (k p : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (redirect k p)⟩

lemma redirect_bound (k p t i : ℕ) (hp : p < k) (hk : k ≤ t) (hi : i < t + 1) :
    redirect k p i < t := by
  unfold redirect
  split_ifs <;> omega

lemma redirect_slot (k p t i : ℕ) (hp : p < k) (hk : k < t) :
    redirect k p i = t - 1 ↔ i = t := by
  unfold redirect
  split_ifs <;> omega

lemma initial_simulation (w : List Bool) (p : ℕ) (b : Bool)
    (hp : p < w.length) (hb : b = w.getD p false) :
    ∀ i, w.getD (redirect w.length p i) false = (w ++ [b]).getD i false := by
  intro i
  by_cases he : i = w.length
  · subst i
    simp [redirect, hb]
  · by_cases hi : i < w.length
    · have hni : ¬ w.length < i := by omega
      simp only [redirect, if_neg he, if_neg hni]
      exact (List.getD_append _ _ _ _ hi).symm
    · have hgt : w.length < i := by omega
      simp only [redirect, if_neg he, if_pos hgt]
      rw [List.getD_eq_default _ _ (by omega),
        List.getD_eq_default _ _ (by simp; omega)]

lemma simulate (gs : List Gate) (k p : ℕ) (hp : p < k)
    (w w' : List Bool) (hlen : w'.length + 1 = w.length) (hk : k < w.length)
    (hval : ∀ i, w'.getD (redirect k p i) false = w.getD i false) :
    ∀ i, (run (gs.map (rename k p)) w').getD (redirect k p i) false =
      (run gs w).getD i false := by
  induction gs generalizing w w' with
  | nil => exact hval
  | cons g gs ih =>
    have he : ev w' (rename k p g) = ev w g := by
      unfold ev rename
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hval i
    change ∀ i,
      (run (gs.map (rename k p)) (w' ++ [ev w' (rename k p g)])).getD
          (redirect k p i) false =
        (run gs (w ++ [ev w g])).getD i false
    rw [he]
    apply ih (w ++ [ev w g]) (w' ++ [ev w g])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (by simp only [List.length_append, List.length_singleton]; omega)
    intro i
    by_cases hi : i = w.length
    · subst i
      have hr : redirect k p w.length = w'.length := by
        have h := (redirect_slot k p w.length w.length hp hk).2 rfl
        omega
      rw [hr]
      simp
    · have hr : redirect k p i ≠ w'.length := by
        intro h
        apply hi
        apply (redirect_slot k p w.length i hp hk).1
        omega
      rw [getD_snoc_ne _ _ _ hr, getD_snoc_ne _ _ _ hi]
      exact hval i

def Back : ℕ → List Gate → Prop
  | _, [] => True
  | n, g :: gs => (∀ i ∈ g.inputs, i < n) ∧ Back (n + 1) gs

lemma back_of_reads (gs : List Gate) (n : ℕ)
    (h : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j) :
    Back n gs := by
  induction gs generalizing n with
  | nil => trivial
  | cons g gs ih =>
    constructor
    · intro i hi
      have hh := h 0 (by simp) i (by simpa using hi)
      simpa using hh
    · apply ih
      intro j hj i hi
      have hh := h (j + 1) (by simp; omega) i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

lemma reads_of_back (gs : List Gate) (n : ℕ) (h : Back n gs) :
    ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j := by
  induction gs generalizing n with
  | nil => simp
  | cons g gs ih =>
    intro j hj i hi
    cases j with
    | zero =>
      have hh := h.1 i (by simpa using hi)
      simpa using hh
    | succ j =>
      have hh := ih (n + 1) h.2 j (by simpa using hj) i (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

lemma back_append (pre post : List Gate) (n : ℕ) :
    Back n (pre ++ post) ↔ Back n pre ∧ Back (n + pre.length) post := by
  induction pre generalizing n with
  | nil => simp [Back]
  | cons g pre ih =>
    simp only [List.cons_append, Back, ih, List.length_cons]
    simp [and_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma back_rename (post : List Gate) (k p t : ℕ) (hp : p < k) (hk : k ≤ t)
    (h : Back (t + 1) post) : Back t (post.map (rename k p)) := by
  induction post generalizing t with
  | nil => trivial
  | cons g post ih =>
    constructor
    · intro i hi
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
      exact redirect_bound k p t a hp hk (h.1 a ha)
    · exact ih (t + 1) (by omega) h.2

lemma split_at {α : Type} (l : List α) (j : ℕ) (hj : j < l.length) :
    ∃ pre a post, l = pre ++ a :: post ∧ pre.length = j := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    cases j with
    | zero => exact ⟨[], a, l, rfl, rfl⟩
    | succ j =>
      obtain ⟨pre, b, post, hs, hl⟩ := ih j (by simpa using hj)
      exact ⟨a :: pre, b, post, by simp [hs], by simp [hl]⟩

lemma smaller (n : ℕ) (C : Circuit) (hC : IsAO2 n C) (j p : ℕ)
    (hj : j < C.gates.length) (hp : p < n + j)
    (hsame : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD p false = gateVal n C j x) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧ D.size + 1 = C.size := by
  obtain ⟨pre, g, post, hs, hl⟩ := split_at C.gates j hj
  let k := n + j
  let D : Circuit :=
    ⟨pre ++ post.map (rename k p), redirect k p C.output⟩
  have hback : Back n C.gates := back_of_reads C.gates n hC.2.1
  rw [hs, back_append] at hback
  have hpost : Back (k + 1) post := by
    simpa only [Back, hl] using hback.2.2
  have hDback : Back n D.gates := by
    apply (back_append pre (post.map (rename k p)) n).2
    refine ⟨hback.1, ?_⟩
    rw [hl]
    exact back_rename post k p k hp (Nat.le_refl _) hpost
  have hpre_mem : ∀ a ∈ pre, a ∈ C.gates := by
    intro a ha
    rw [hs]
    exact List.mem_append_left _ ha
  have hpost_mem : ∀ a ∈ post, a ∈ C.gates := by
    intro a ha
    rw [hs]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ ha)
  have hDAO : IsAO2 n D := by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      change a ∈ pre ++ post.map (rename k p) at ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hC.1 a (hpre_mem a ha)
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact hC.1 b (hpost_mem b hb)
    · exact reads_of_back D.gates n hDback
    · intro a ha
      change a ∈ pre ++ post.map (rename k p) at ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hC.2.2 a (hpre_mem a ha)
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        simpa [rename] using hC.2.2 b (hpost_mem b hb)
  refine ⟨D, hDAO, ?_, ?_⟩
  · funext x
    let w := run pre (List.ofFn x)
    have hw : w.length = k := by simp [w, run_length, k, hl]
    have hwire : C.wires (List.ofFn x) = run post (w ++ [ev w g]) := by
      change run C.gates (List.ofFn x) = _
      rw [hs, run_append]
      rfl
    have hwp : (C.wires (List.ofFn x)).getD p false = w.getD p false := by
      rw [hwire, run_keep post _ p (by simp only [List.length_append, List.length_singleton]; omega)]
      exact List.getD_append _ _ _ _ (by omega)
    have hwj : gateVal n C j x = ev w g := by
      unfold gateVal
      rw [hwire, run_keep post _ (n + j)
        (by simp only [List.length_append, List.length_singleton]; dsimp [k] at hw; omega)]
      have he : n + j = w.length := hw.symm
      rw [he]
      simp
    have hev : ev w g = w.getD p false :=
      hwj.symm.trans ((hsame x).symm.trans hwp)
    have hinit : ∀ i, w.getD (redirect k p i) false = (w ++ [ev w g]).getD i false := by
      rw [← hw]
      exact initial_simulation w p (ev w g) (by omega) hev
    have hsim := simulate post k p hp (w ++ [ev w g]) w
      (by simp) (by simp only [List.length_append, List.length_singleton]; omega) hinit C.output
    change (D.wires (List.ofFn x)).getD D.output false =
      (C.wires (List.ofFn x)).getD C.output false
    rw [hwire]
    change (run (pre ++ post.map (rename k p)) (List.ofFn x)).getD
      (redirect k p C.output) false = _
    rw [run_append]
    exact hsim
  · change (pre ++ post.map (rename k p)).length + 1 = C.gates.length
    rw [hs]
    simp only [List.length_append, List.length_map, List.length_cons]
    omega

lemma no_alias (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (j p : ℕ)
    (hj : j < C.gates.length) (hp : p < n + j)
    (hsame : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD p false = gateVal n C j x) : False := by
  obtain ⟨D, hD, he, hs⟩ := smaller n C hC.1 j p hj hp hsame
  have hmin := hC.2.2 D hD (he.trans hC.2.1)
  omega

lemma input_value (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    (C.wires (List.ofFn x)).getD u.val false = x u := by
  change (run C.gates (List.ofFn x)).getD u.val false = x u
  rw [run_keep C.gates _ u.val (by simpa using u.isLt)]
  simp [List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_1495

theorem PEqualNP.Outside.L_meta_1495 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsLeastAO G C →
      ∀ (j : ℕ), j < C.gates.length → n + j ≠ C.output →
        (∀ i < j, ∃ x : Fin n → Bool,
          PEqualNP.EdgeOwnership.gateVal n C i x ≠ PEqualNP.EdgeOwnership.gateVal n C j x) ∧
        (∀ u : Fin n, ∃ x : Fin n → Bool,
          x u ≠ PEqualNP.EdgeOwnership.gateVal n C j x) := by
  classical
  intro n G _ C hC j hj _
  constructor
  · intro i hi
    by_contra hn
    push_neg at hn
    apply PEqualNP.Outside.L_meta_1495.no_alias n G C hC j (n + i) hj (by omega)
    intro x
    exact hn x
  · intro u
    by_contra hn
    push_neg at hn
    apply PEqualNP.Outside.L_meta_1495.no_alias n G C hC j u.val hj (by omega)
    intro x
    rw [PEqualNP.Outside.L_meta_1495.input_value n C x u]
    exact hn x
