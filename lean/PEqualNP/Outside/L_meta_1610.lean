import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1610

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact gate_mono C (w - n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt => ih r (by omega)
    · simp [missing_value C x w (by unfold Circuit.size; omega)]

lemma forest_count {α ι : Type*} [DecidableEq α] [LinearOrder ι]
    (I : Finset ι) (S : Finset α) (a b : ι → α) (hne : S.Nonempty)
    (hend : ∀ i ∈ I, a i ∈ S ∧ b i ∈ S)
    (hcut : ∀ g ∈ I, ∃ X : Finset α, a g ∈ X ∧ b g ∉ X ∧
      ∀ i ∈ I, i < g → (a i ∈ X ↔ b i ∈ X)) :
    I.card + 1 ≤ S.card := by
  classical
  induction I using Finset.strongInductionOn generalizing S with
  | _ I ih =>
    by_cases hI : I = ∅
    · simpa [hI] using hne.card_pos
    have hIn : I.Nonempty := Finset.nonempty_iff_ne_empty.mpr hI
    let g := I.max' hIn
    have hg : g ∈ I := Finset.max'_mem I hIn
    obtain ⟨X, haX, hbX, hX⟩ := hcut g hg
    let J := I.erase g
    let J₁ := J.filter fun i => a i ∈ X
    let J₂ := J.filter fun i => a i ∉ X
    let S₁ := S.filter fun v => v ∈ X
    let S₂ := S.filter fun v => v ∉ X
    have hJ (i : ι) (hi : i ∈ J) : i ∈ I ∧ i < g := by
      obtain ⟨hne', hi'⟩ := Finset.mem_erase.mp hi
      exact ⟨hi', lt_of_le_of_ne (Finset.le_max' I i hi') hne'⟩
    have hJ₁ : J₁ ⊂ I := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨(Finset.filter_subset _ _).trans (Finset.erase_subset _ _), ?_⟩
      intro heq
      have : g ∈ J₁ := heq.symm ▸ hg
      have : g ∈ I.erase g := (Finset.mem_filter.mp this).1
      simp at this
    have hJ₂ : J₂ ⊂ I := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨(Finset.filter_subset _ _).trans (Finset.erase_subset _ _), ?_⟩
      intro heq
      have : g ∈ J₂ := heq.symm ▸ hg
      have : g ∈ I.erase g := (Finset.mem_filter.mp this).1
      simp at this
    have hn₁ : S₁.Nonempty := ⟨a g, Finset.mem_filter.mpr ⟨(hend g hg).1, haX⟩⟩
    have hn₂ : S₂.Nonempty := ⟨b g, Finset.mem_filter.mpr ⟨(hend g hg).2, hbX⟩⟩
    have he₁ : ∀ i ∈ J₁, a i ∈ S₁ ∧ b i ∈ S₁ := by
      intro i hi
      obtain ⟨hi, hai⟩ := Finset.mem_filter.mp hi
      obtain ⟨hiI, hig⟩ := hJ i hi
      exact ⟨Finset.mem_filter.mpr ⟨(hend i hiI).1, hai⟩,
        Finset.mem_filter.mpr ⟨(hend i hiI).2, (hX i hiI hig).mp hai⟩⟩
    have he₂ : ∀ i ∈ J₂, a i ∈ S₂ ∧ b i ∈ S₂ := by
      intro i hi
      obtain ⟨hi, hai⟩ := Finset.mem_filter.mp hi
      obtain ⟨hiI, hig⟩ := hJ i hi
      exact ⟨Finset.mem_filter.mpr ⟨(hend i hiI).1, hai⟩,
        Finset.mem_filter.mpr ⟨(hend i hiI).2, fun hb => hai ((hX i hiI hig).mpr hb)⟩⟩
    have hc₁ : ∀ k ∈ J₁, ∃ Y : Finset α, a k ∈ Y ∧ b k ∉ Y ∧
        ∀ i ∈ J₁, i < k → (a i ∈ Y ↔ b i ∈ Y) := by
      intro k hk
      obtain ⟨Y, ha, hb, hY⟩ := hcut k (hJ k (Finset.mem_filter.mp hk).1).1
      exact ⟨Y, ha, hb, fun i hi hik => hY i (hJ i (Finset.mem_filter.mp hi).1).1 hik⟩
    have hc₂ : ∀ k ∈ J₂, ∃ Y : Finset α, a k ∈ Y ∧ b k ∉ Y ∧
        ∀ i ∈ J₂, i < k → (a i ∈ Y ↔ b i ∈ Y) := by
      intro k hk
      obtain ⟨Y, ha, hb, hY⟩ := hcut k (hJ k (Finset.mem_filter.mp hk).1).1
      exact ⟨Y, ha, hb, fun i hi hik => hY i (hJ i (Finset.mem_filter.mp hi).1).1 hik⟩
    have h₁ := ih J₁ hJ₁ S₁ hn₁ he₁ hc₁
    have h₂ := ih J₂ hJ₂ S₂ hn₂ he₂ hc₂
    have hJS : J₁.card + J₂.card = J.card := Finset.card_filter_add_card_filter_not _
    have hSS : S₁.card + S₂.card = S.card := Finset.card_filter_add_card_filter_not _
    have hJI : J.card + 1 = I.card := by
      dsimp [J]
      have hp := Finset.card_pos.mpr hIn
      rw [Finset.card_erase_of_mem hg]
      omega
    omega

def Merges {n : ℕ} (C : Circuit) (L : Finset (Fin n))
    (t : Fin n → Fin n → Bool) (g : Fin C.gates.length) : Prop :=
  (C.gates.get g).op = GateOp.or ∧
  value C (fun v : Fin n => decide (v ∉ L)) (n + (g : ℕ)) = false ∧
  ∃ w1 w2 : ℕ, (C.gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L, ∃ r' ∈ L,
    value C (t r) w1 = true ∧ value C (t r') w2 = true ∧
    ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ ∀ i : Fin C.gates.length,
      i < g → (C.gates.get i).op = GateOp.or →
      value C (fun v : Fin n => decide (v ∉ L)) (n + (i : ℕ)) = false →
      ∀ a b : ℕ, (C.gates.get i).inputs = [a, b] →
      ∀ y ∈ L, ∀ y' ∈ L,
      (value C (t y) a = true ∨ value C (t y) b = true) →
      (value C (t y') a = true ∨ value C (t y') b = true) → (y ∈ X ↔ y' ∈ X)

lemma one_side {n : ℕ} (C : Circuit) (L M : Finset (Fin n)) (m : Fin n)
    (t : Fin n → Fin n → Bool) (hLM : L ∩ M = {m})
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hback : ∀ (i : Fin C.gates.length), ∀ w ∈ (C.gates.get i).inputs, w < n + (i : ℕ))
    (I : Finset (Fin C.gates.length))
    (hI : ∀ g ∈ I, Merges C L t g)
    (hM : ∀ g ∈ I, value C (fun v : Fin n => decide (v ∉ M)) (n + (g : ℕ)) = false) :
    I.card ≤ ((L \ M).filter (fun r => ∃ v ∈ M, t r v = true)).card := by
  classical
  let D := (L \ M).filter (fun r => ∃ v ∈ M, t r v = true)
  let S := insert m D
  have hmL : m ∈ L := by
    have : m ∈ L ∩ M := by rw [hLM]; simp
    exact (Finset.mem_inter.mp this).1
  have hSL : S ⊆ L := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hmL
    · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hr).1).1
  have hS (g : Fin C.gates.length) (hg : g ∈ I) (r : Fin n) (hr : r ∈ L)
      (hv : value C (t r) (n + (g : ℕ)) = true) : r ∈ S := by
    have hcross : ∃ v ∈ M, t r v = true := by
      by_contra hnone
      have hle : ∀ v, t r v = true → (decide (v ∉ M) : Bool) = true := by
        intro v hv
        apply decide_eq_true
        intro hvM
        exact hnone ⟨v, hvM, hv⟩
      have hv' := mono C hC (t r) (fun v : Fin n => decide (v ∉ M)) hle _ hv
      rw [hM g hg] at hv'
      cases hv'
    by_cases hrM : r ∈ M
    · have : r = m := by
        have hh : r ∈ L ∩ M := Finset.mem_inter.mpr ⟨hr, hrM⟩
        rw [hLM] at hh
        exact Finset.mem_singleton.mp hh
      exact Finset.mem_insert.mpr (Or.inl this)
    · exact Finset.mem_insert.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hr, hrM⟩, hcross⟩))
  have data : ∀ g : Fin C.gates.length, ∃ a b : Fin n, g ∈ I →
      a ∈ S ∧ b ∈ S ∧ value C (t a) (n + (g : ℕ)) = true ∧
      value C (t b) (n + (g : ℕ)) = true ∧
      ∃ X : Finset (Fin n), a ∈ X ∧ b ∉ X ∧
        ∀ i ∈ I, i < g → ∀ y ∈ L, ∀ y' ∈ L,
        value C (t y) (n + (i : ℕ)) = true →
        value C (t y') (n + (i : ℕ)) = true → (y ∈ X ↔ y' ∈ X) := by
    intro g
    by_cases hg : g ∈ I
    · obtain ⟨hop, hf, w1, w2, hw, r, hr, r', hr', hv, hv', X, hx, hx', hcut⟩ := hI g hg
      have hrg : value C (t r) (n + (g : ℕ)) = true := by
        apply (or_value C g.val g.isLt hop (t r)).mpr
        refine ⟨w1, ?_, ?_, hv⟩
        · change w1 ∈ (C.gates.get g).inputs
          rw [hw]
          exact List.mem_cons_self
        · apply hback g w1
          rw [hw]
          exact List.mem_cons_self
      have hr'g : value C (t r') (n + (g : ℕ)) = true := by
        apply (or_value C g.val g.isLt hop (t r')).mpr
        refine ⟨w2, ?_, ?_, hv'⟩
        · change w2 ∈ (C.gates.get g).inputs
          rw [hw]
          exact List.mem_cons_of_mem w1 List.mem_cons_self
        · apply hback g w2
          rw [hw]
          exact List.mem_cons_of_mem w1 List.mem_cons_self
      refine ⟨r, r', fun _ => ⟨hS g hg r hr hrg, hS g hg r' hr' hr'g, hrg, hr'g,
        X, hx, hx', ?_⟩⟩
      intro i hi hig y hy y' hy' hiy hiy'
      obtain ⟨hiop, hif, a, b, hab, hrest⟩ := hI i hi
      have hdisj (z : Fin n) (hz : value C (t z) (n + (i : ℕ)) = true) :
          value C (t z) a = true ∨ value C (t z) b = true := by
        obtain ⟨w, hw, _, hv⟩ := (or_value C i.val i.isLt hiop (t z)).mp hz
        change w ∈ (C.gates.get i).inputs at hw
        rw [hab] at hw
        rcases List.mem_pair.mp hw with rfl | rfl
        · exact Or.inl hv
        · exact Or.inr hv
      exact hcut i hig hiop hif a b hab y hy y' hy' (hdisj y hiy) (hdisj y' hiy')
    · exact ⟨m, m, fun h => (hg h).elim⟩
  choose a b hab using data
  have hend : ∀ g ∈ I, a g ∈ S ∧ b g ∈ S := by
    intro g hg
    exact ⟨(hab g hg).1, (hab g hg).2.1⟩
  have hcut : ∀ g ∈ I, ∃ X : Finset (Fin n), a g ∈ X ∧ b g ∉ X ∧
      ∀ i ∈ I, i < g → (a i ∈ X ↔ b i ∈ X) := by
    intro g hg
    obtain ⟨_, _, _, _, X, hx, hx', hX⟩ := hab g hg
    refine ⟨X, hx, hx', ?_⟩
    intro i hi hig
    obtain ⟨hai, hbi, hia, hib, _⟩ := hab i hi
    exact hX i hi hig (a i) (hSL hai) (b i) (hSL hbi) hia hib
  have hcount := forest_count I S a b ⟨m, Finset.mem_insert_self m D⟩ hend hcut
  have hbound : S.card ≤ D.card + 1 := Finset.card_insert_le m D
  change I.card ≤ D.card
  omega

end PEqualNP.Outside.L_meta_1610

open PEqualNP.Outside.L_meta_1610

theorem PEqualNP.Outside.L_meta_1610 : ∀ (n : ℕ) (L M : Finset (Fin n)) (m : Fin n) (t u : Fin n → Fin n → Bool)
    (gates : List PEqualNP.CircuitLowerBounds.Gate) (oL oM : ℕ),
    L ∩ M = {m} →
    (∀ r ∈ L, ∀ v ∈ L, t r v = true ↔ v = r) → (∀ r ∈ M, ∀ v ∈ M, u r v = true ↔ v = r) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < n + (i : ℕ)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, oL⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false → (∀ r ∈ L, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, oL⟩ (List.ofFn (t r)) = true) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, oM⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false → (∀ r ∈ M, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, oM⟩ (List.ofFn (u r)) = true) →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L, ∃ r' ∈ L,
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (t r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (t r')) = true ∧
          ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ ∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (i : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false → ∀ a b : ℕ, (gates.get i).inputs = [a, b] →
            ∀ y ∈ L, ∀ y' ∈ L, (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (t y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (t y)) = true) →
              (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (t y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (t y')) = true) → (y ∈ X ↔ y' ∈ X)) ∧
        ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ M, ∃ r' ∈ M,
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (u r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (u r')) = true ∧
          ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ ∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (i : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false → ∀ a b : ℕ, (gates.get i).inputs = [a, b] →
            ∀ y ∈ M, ∀ y' ∈ M, (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (u y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (u y)) = true) →
              (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (u y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (u y')) = true) → (y ∈ X ↔ y' ∈ X))) →
      I.card ≤ ((L \ M).filter (fun r => ∃ v ∈ M, t r v = true)).card ∧
      I.card ≤ ((M \ L).filter (fun r => ∃ v ∈ L, u r v = true)).card := by
  classical
  intro n L M m t u gates oL oM hLM ht hu hC hback hfL htL hfM htM I hI
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates, 0⟩
  change ∀ g ∈ I, Merges C L t g ∧ Merges C M u g at hI
  constructor
  · exact one_side C L M m t hLM hC hback I (fun g hg => (hI g hg).1)
      (fun g hg => (hI g hg).2.2.1)
  · apply one_side C M L m u (by rw [Finset.inter_comm]; exact hLM) hC hback I
      (fun g hg => (hI g hg).2)
    intro g hg
    exact (hI g hg).1.2.1
