import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3473

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.ReadK

def run {α : Type} (E : GateOp → List α → α) (d : α) (gs : List Gate)
    (xs : List α) : List α :=
  gs.foldl (fun w g => w ++ [E g.op (g.inputs.map fun i => w.getD i d)]) xs

lemma run_cons {α : Type} (E : GateOp → List α → α) (d : α)
    (g : Gate) (gs : List Gate) (xs : List α) :
    run E d (g :: gs) xs =
      run E d gs (xs ++ [E g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

lemma run_length {α : Type} (E : GateOp → List α → α) (d : α)
    (gs : List Gate) : ∀ xs, (run E d gs xs).length = xs.length + gs.length := by
  induction gs with
  | nil => intro xs; simp [run]
  | cons g gs ih =>
    intro xs
    rw [run_cons, ih]
    simp
    omega

lemma run_keep {α : Type} (E : GateOp → List α → α) (d : α)
    (gs : List Gate) : ∀ (xs : List α) (i : ℕ), i < xs.length →
      (run E d gs xs).getD i d = xs.getD i d := by
  induction gs with
  | nil => intro xs i hi; rfl
  | cons g gs ih =>
    intro xs i hi
    rw [run_cons, ih _ i (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma run_gate {α : Type} (E : GateOp → List α → α) (d : α)
    (gs : List Gate) : ∀ (xs : List α) (j : ℕ) (g : Gate), gs[j]? = some g →
      (run E d gs xs).getD (xs.length + j) d =
        E g.op (g.inputs.map fun i => (run E d (gs.take j) xs).getD i d) := by
  induction gs with
  | nil => intro xs j g h; simp at h
  | cons g0 gs ih =>
    intro xs j g h
    cases j with
    | zero =>
      simp at h
      subst g
      rw [run_cons, run_keep E d gs _ _ (by simp)]
      simp [run]
    | succ j =>
      simp at h
      rw [run_cons]
      have h1 := ih (xs ++ [E g0.op (g0.inputs.map fun i => xs.getD i d)]) j g h
      simp only [List.length_append, List.length_singleton] at h1
      rw [show xs.length + (j + 1) = xs.length + 1 + j by omega, h1]
      simp [run_cons]

lemma run_take {α : Type} (E : GateOp → List α → α) (d : α)
    (gs : List Gate) (xs : List α) (j i : ℕ) (hj : j ≤ gs.length)
    (hi : i < xs.length + j) :
    (run E d (gs.take j) xs).getD i d = (run E d gs xs).getD i d := by
  have he : run E d gs xs = run E d (gs.drop j) (run E d (gs.take j) xs) := by
    unfold run
    rw [← List.foldl_append, List.take_append_drop]
  rw [he, run_keep E d (gs.drop j) _ i
    (by rw [run_length, List.length_take, Nat.min_eq_left hj]; exact hi)]

def value {α : Type} (E : GateOp → List α → α) (d : α)
    (C : Circuit) (xs : List α) (w : ℕ) : α := (run E d C.gates xs).getD w d

lemma value_input {α : Type} (E : GateOp → List α → α) (d : α)
    (C : Circuit) (xs : List α) {n w : ℕ} (hx : xs.length = n) (hw : w < n) :
    value E d C xs w = xs.getD w d :=
  run_keep E d C.gates xs w (by omega)

lemma value_big {α : Type} (E : GateOp → List α → α) (d : α)
    (C : Circuit) (xs : List α) {n w : ℕ} (hx : xs.length = n)
    (hw : n + C.gates.length ≤ w) : value E d C xs w = d := by
  apply List.getD_eq_default
  rw [run_length, hx]
  exact hw

lemma gateAt_eq {C : Circuit} {k : ℕ} (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by simp [gateAt, hk]

def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length,
    ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k

lemma ao_of {n : ℕ} {C : Circuit} (h : IsAO2 n C) : AO n C := by
  intro k hk
  have hm : gateAt C k ∈ C.gates := by
    rw [gateAt_eq hk]
    exact List.getElem_mem hk
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 _ hm)
  exact ⟨h.1 _ hm, a, b, hab,
    h.2.1 k hk a (by rw [hab]; simp), h.2.1 k hk b (by rw [hab]; simp)⟩

lemma ao_to {n : ℕ} {C : Circuit} (h : AO n C) : IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    rw [← gateAt_eq hk]
    exact (h k hk).1
  · intro k hk i hi
    obtain ⟨_, a, b, hab, ha, hb⟩ := h k hk
    rw [hab] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨_, a, b, hab, _⟩ := h k hk
    rw [← gateAt_eq hk, hab]
    rfl

lemma value_gate {α : Type} (E : GateOp → List α → α) (d : α)
    {n : ℕ} {C : Circuit} (hC : AO n C) (xs : List α) (hx : xs.length = n)
    {k : ℕ} (hk : k < C.gates.length) :
    value E d C xs (n + k) =
      E (gateAt C k).op ((gateAt C k).inputs.map (value E d C xs)) := by
  have hg : C.gates[k]? = some (gateAt C k) := by
    rw [gateAt_eq hk]
    simp [hk]
  have he := run_gate E d C.gates xs k (gateAt C k) hg
  rw [hx] at he
  unfold value
  rw [he]
  congr 1
  apply List.map_congr_left
  intro i hi
  obtain ⟨_, a, b, hab, ha, hb⟩ := hC k hk
  have hil : i < n + k := by
    rw [hab] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  exact run_take E d C.gates xs k i hk.le (by omega)

lemma value_two {α : Type} (E : GateOp → List α → α) (d : α)
    {n : ℕ} {C : Circuit} (hC : AO n C) (xs : List α) (hx : xs.length = n)
    {k a b : ℕ} (hk : k < C.gates.length) (hab : (gateAt C k).inputs = [a, b]) :
    value E d C xs (n + k) =
      E (gateAt C k).op [value E d C xs a, value E d C xs b] := by
  rw [value_gate E d hC xs hx hk, hab]
  rfl

def bv (C : Circuit) (xs : List Bool) (w : ℕ) : Bool := value GateOp.eval false C xs w

lemma circuit_eq (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = bv C (List.ofFn x) C.output := rfl

lemma bv_input (C : Circuit) (xs : List Bool) {n w : ℕ}
    (hx : xs.length = n) (hw : w < n) : bv C xs w = xs.getD w false :=
  value_input GateOp.eval false C xs hx hw

lemma bv_big (C : Circuit) (xs : List Bool) {n w : ℕ}
    (hx : xs.length = n) (hw : n + C.gates.length ≤ w) : bv C xs w = false :=
  value_big GateOp.eval false C xs hx hw

lemma bv_two {n : ℕ} {C : Circuit} (hC : AO n C) (xs : List Bool)
    (hx : xs.length = n) {k a b : ℕ} (hk : k < C.gates.length)
    (hab : (gateAt C k).inputs = [a, b]) :
    bv C xs (n + k) = (gateAt C k).op.eval [bv C xs a, bv C xs b] :=
  value_two GateOp.eval false hC xs hx hk hab

lemma bv_mono {n : ℕ} {C : Circuit} (hC : AO n C) (xs ys : List Bool)
    (hx : xs.length = n) (hy : ys.length = n)
    (hxy : ∀ i < n, xs.getD i false = true → ys.getD i false = true) :
    ∀ w, bv C xs w = true → bv C ys w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hn : w < n
    · rw [bv_input C xs hx hn] at hw
      rw [bv_input C ys hy hn]
      exact hxy w hn hw
    by_cases hb : n + C.gates.length ≤ w
    · rw [bv_big C xs hx hb] at hw
      cases hw
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    obtain ⟨hop, a, b, hab, ha, hb⟩ := hC k hk
    rw [bv_two hC xs hx hk hab] at hw
    rw [bv_two hC ys hy hk hab]
    rcases hop with hop | hop
    · rw [hop] at hw ⊢
      simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
        Bool.and_eq_true] at hw ⊢
      exact ⟨ih a ha hw.1, ih b hb hw.2⟩
    · rw [hop] at hw ⊢
      simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
        Bool.or_eq_true] at hw ⊢
      exact hw.elim (fun h => Or.inl (ih a ha h)) (fun h => Or.inr (ih b hb h))

def topOff (n v : ℕ) : List Bool := List.ofFn fun i : Fin n => decide (i.val ≠ v)

lemma topOff_length (n v : ℕ) : (topOff n v).length = n := by simp [topOff]

lemma off_zero {n : ℕ} {C : Circuit} (hC : AO n C) (v w : ℕ)
    (hw : bv C (topOff n v) w = false) (xs : List Bool) (hx : xs.length = n)
    (hv : xs.getD v false = false) : bv C xs w = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have ht := bv_mono hC xs (topOff n v) hx (topOff_length n v) (fun i hi hit => by
    have hne : i ≠ v := by intro he; subst i; rw [hv] at hit; cases hit
    simp [topOff, List.getD_eq_getElem?_getD, hi, hne]) w h
  rw [hw] at ht
  cases ht

def lpE (op : GateOp) (ins : List (Bool × Bool)) : Bool × Bool :=
  match op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
      (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

def ini (s : ℕ → Bool) (xs : List Bool) : List (Bool × Bool) :=
  (xs.zipIdx).map fun (b, i) => if s i then (false, b) else (b, false)

def lv (C : Circuit) (s : ℕ → Bool) (xs : List Bool) (w : ℕ) : Bool × Bool :=
  value lpE (false, false) C (ini s xs) w

lemma ini_length (s : ℕ → Bool) (xs : List Bool) : (ini s xs).length = xs.length := by
  simp [ini]

lemma lv_input (C : Circuit) (s : ℕ → Bool) (xs : List Bool) {n w : ℕ}
    (hx : xs.length = n) (hw : w < n) :
    lv C s xs w = if s w then (false, xs.getD w false) else (xs.getD w false, false) := by
  unfold lv
  rw [value_input lpE (false, false) C (ini s xs) (by rw [ini_length, hx]) hw]
  have hw' : w < xs.length := by omega
  simp [ini, List.getD_eq_getElem?_getD, hw']

lemma lv_big (C : Circuit) (s : ℕ → Bool) (xs : List Bool) {n w : ℕ}
    (hx : xs.length = n) (hw : n + C.gates.length ≤ w) : lv C s xs w = (false, false) :=
  value_big lpE (false, false) C (ini s xs) (by rw [ini_length, hx]) hw

lemma lv_two {n : ℕ} {C : Circuit} (hC : AO n C) (s : ℕ → Bool) (xs : List Bool)
    (hx : xs.length = n) {k a b : ℕ} (hk : k < C.gates.length)
    (hab : (gateAt C k).inputs = [a, b]) :
    lv C s xs (n + k) = lpE (gateAt C k).op [lv C s xs a, lv C s xs b] :=
  value_two lpE (false, false) hC (ini s xs) (by rw [ini_length, hx]) hk hab

lemma lv_zero {n : ℕ} {C : Circuit} (hC : AO n C) (s : ℕ → Bool)
    (xs : List Bool) (hx : xs.length = n) :
    ∀ w, bv C xs w = false → lv C s xs w = (false, false) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hn : w < n
    · rw [bv_input C xs hx hn] at hw
      rw [lv_input C s xs hx hn, hw]
      cases s w <;> rfl
    by_cases hb : n + C.gates.length ≤ w
    · exact lv_big C s xs hx hb
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    obtain ⟨hop, a, b, hab, ha, hb⟩ := hC k hk
    rw [bv_two hC xs hx hk hab] at hw
    rw [lv_two hC s xs hx hk hab]
    rcases hop with hop | hop
    · rw [hop] at hw ⊢
      have hz : bv C xs a = false ∨ bv C xs b = false := by
        cases h1 : bv C xs a <;> cases h2 : bv C xs b <;>
          simp_all [GateOp.eval]
      rcases hz with hz | hz
      · rw [ih a ha hz]
        simp [lpE]
      · rw [ih b hb hz]
        simp [lpE]
    · rw [hop] at hw ⊢
      have hz : bv C xs a = false ∧ bv C xs b = false := by
        cases h1 : bv C xs a <;> cases h2 : bv C xs b <;>
          simp_all [GateOp.eval]
      rw [ih a ha hz.1, ih b hb hz.2]
      rfl

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def bypass (n : ℕ) (C : Circuit) (r b : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩),
    tau n r b C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r b : ℕ) :
    (bypass n C r b).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_gate {n : ℕ} {C : Circuit} {r b k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r b) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  rw [gateAt_eq (by rw [bypass_length]; exact hk)]
  simp [bypass]

lemma rho_lt {r k m : ℕ} (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho
  split_ifs <;> omega

lemma tau_lt {n r b w k : ℕ} (hb : b < n + r) (hw : w < n + rho r k) :
    tau n r b w < n + k := by
  unfold tau rho at *
  split_ifs at * <;> omega

lemma bypass_ao {n : ℕ} {C : Circuit} (hC : AO n C) {r b : ℕ}
    (hr : r < C.gates.length) (hb : b < n + r) : AO n (bypass n C r b) := by
  intro k hk
  rw [bypass_length] at hk
  rw [bypass_gate hk]
  obtain ⟨hop, a, c, hac, ha, hc⟩ := hC (rho r k) (rho_lt hr hk)
  refine ⟨hop, tau n r b a, tau n r b c, ?_, tau_lt hb ha, tau_lt hb hc⟩
  simp [hac]

lemma transfer {α : Type} (E : GateOp → List α → α) (d : α)
    (R : α → α → Prop) (hrefl : ∀ a, R a a)
    (htrans : ∀ a b c, R a b → R b c → R a c)
    (hop : ∀ op, (op = GateOp.and ∨ op = GateOp.or) →
      ∀ (l : List ℕ) (f g : ℕ → α), (∀ i ∈ l, R (f i) (g i)) →
        R (E op (l.map f)) (E op (l.map g)))
    {n : ℕ} {C : Circuit} (hC : AO n C) (xs : List α) (hx : xs.length = n)
    {r b : ℕ} (hr : r < C.gates.length) (hb : b < n + r)
    (hR : R (value E d C xs (n + r)) (value E d C xs b)) :
    ∀ w, R (value E d C xs w) (value E d (bypass n C r b) xs (tau n r b w)) := by
  have hD := bypass_ao hC hr hb
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · have ht : tau n r b w = w := by simp [tau, show w < n + r by omega]
      rw [ht, value_input E d C xs hx hn,
        value_input E d (bypass n C r b) xs hx hn]
      exact hrefl _
    by_cases hbig : n + C.gates.length ≤ w
    · have ht : tau n r b w = w - 1 := by
        simp [tau, show ¬ w < n + r by omega, show w ≠ n + r by omega]
      rw [ht, value_big E d C xs hx hbig,
        value_big E d (bypass n C r b) xs hx (by rw [bypass_length]; omega)]
      exact hrefl _
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    by_cases he : k = r
    · subst k
      have hi := ih b hb
      have ht : tau n r b b = b := by simp [tau, hb]
      rw [ht] at hi
      have ht' : tau n r b (n + r) = b := by simp [tau]
      rw [ht']
      exact htrans _ _ _ hR hi
    have hk : k < C.gates.length := by omega
    obtain ⟨k', ht, hrho, hk'⟩ : ∃ k', tau n r b (n + k) = n + k' ∧
        rho r k' = k ∧ k' < C.gates.length - 1 := by
      by_cases hkr : k < r
      · refine ⟨k, ?_, ?_, by omega⟩
        · simp [tau, show n + k < n + r by omega]
        · simp [rho, hkr]
      · refine ⟨k - 1, ?_, ?_, by omega⟩
        · simp only [tau, if_neg (show ¬ n + k < n + r by omega),
            if_neg (show n + k ≠ n + r by omega)]
          omega
        · rw [rho, if_neg (by omega)]
          omega
    rw [ht, value_gate E d hC xs hx hk,
      value_gate E d hD xs hx (by rw [bypass_length]; exact hk'),
      bypass_gate hk', hrho]
    simp only [List.map_map]
    apply hop _ (hC k hk).1
    intro i hi
    obtain ⟨_, a, c, hac, ha, hc⟩ := hC k hk
    have hil : i < n + k := by
      rw [hac] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> assumption
    exact ih i hil

lemma bypass_equal {α : Type} (E : GateOp → List α → α) (d : α)
    {n : ℕ} {C : Circuit} (hC : AO n C) (xs : List α) (hx : xs.length = n)
    {r b : ℕ} (hr : r < C.gates.length) (hb : b < n + r)
    (he : value E d C xs (n + r) = value E d C xs b) :
    value E d (bypass n C r b) xs (bypass n C r b).output =
      value E d C xs C.output := by
  exact (transfer E d Eq (fun _ => rfl) (fun _ _ _ => Eq.trans)
    (by intro op _ l f g h; rw [List.map_congr_left h]) hC xs hx hr hb he C.output).symm

lemma bypass_dom {n : ℕ} {C : Circuit} (hC : AO n C) (xs : List Bool)
    (hx : xs.length = n) {r b : ℕ} (hr : r < C.gates.length) (hb : b < n + r)
    (he : bv C xs b = true → bv C xs (n + r) = true) :
    bv (bypass n C r b) xs (bypass n C r b).output = true → bv C xs C.output = true := by
  apply transfer GateOp.eval false (fun a b => b = true → a = true)
    (fun _ h => h) (fun _ _ _ h1 h2 h => h1 (h2 h)) _ hC xs hx hr hb he C.output
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro hg i hi
    exact h i hi (hg i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, hg⟩
    exact ⟨i, hi, h i hi hg⟩

lemma or_zero_exists {n : ℕ} {C : Circuit} (hC : AO n C) (v : Fin n)
    (x y : Fin n → Bool) (hxy : ∀ i, i ≠ v → x i = y i)
    (hne : circuitFun n C x ≠ circuitFun n C y)
    (ht : bv C (topOff n v.val) C.output = true) :
    ∃ r a b, r < C.gates.length ∧ (gateAt C r).op = GateOp.or ∧
      (gateAt C r).inputs = [a, b] ∧ a < n + r ∧ b < n + r ∧
      (bv C (topOff n v.val) a = false ∨ bv C (topOff n v.val) b = false) := by
  by_contra hno
  have hor : ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.or →
      ∀ a b, (gateAt C k).inputs = [a, b] → a < n + k → b < n + k →
        bv C (topOff n v.val) a = true ∧ bv C (topOff n v.val) b = true := by
    intro k hk hop a b hab ha hb
    cases ea : bv C (topOff n v.val) a <;> cases eb : bv C (topOff n v.val) b
    · exact False.elim (hno ⟨k, a, b, hk, hop, hab, ha, hb, Or.inl ea⟩)
    · exact False.elim (hno ⟨k, a, b, hk, hop, hab, ha, hb, Or.inl ea⟩)
    · exact False.elim (hno ⟨k, a, b, hk, hop, hab, ha, hb, Or.inr eb⟩)
    · exact ⟨rfl, rfl⟩
  have hind : ∀ w, bv C (topOff n v.val) w = true →
      bv C (List.ofFn x) w = bv C (List.ofFn y) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases hn : w < n
      · rw [bv_input C _ (topOff_length n v.val) hn] at hw
        have hnv : w ≠ v.val := by
          simpa [topOff, List.getD_eq_getElem?_getD, hn] using hw
        have he := hxy ⟨w, hn⟩ (fun he => hnv (congrArg Fin.val he))
        rw [bv_input C (List.ofFn x) (by simp) hn,
          bv_input C (List.ofFn y) (by simp) hn]
        simpa [List.getD_eq_getElem?_getD, hn] using he
      by_cases hbig : n + C.gates.length ≤ w
      · rw [bv_big C _ (topOff_length n v.val) hbig] at hw
        cases hw
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hC k hk
      have hboth : bv C (topOff n v.val) a = true ∧ bv C (topOff n v.val) b = true := by
        rcases hop with hop | hop
        · rw [bv_two hC _ (topOff_length n v.val) hk hab, hop] at hw
          simpa [GateOp.eval] using hw
        · exact hor k hk hop a b hab ha hb
      rw [bv_two hC (List.ofFn x) (by simp) hk hab,
        bv_two hC (List.ofFn y) (by simp) hk hab,
        ih a ha hboth.1, ih b hb hboth.2]
  exact hne (hind C.output ht)

lemma shrink_or {n : ℕ} {C : Circuit} (hC : AO n C) (v : Fin n)
    {r a b : ℕ} (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or)
    (hab : (gateAt C r).inputs = [a, b]) (ha : a < n + r) (hb : b < n + r)
    (hz : bv C (topOff n v.val) a = false ∨ bv C (topOff n v.val) b = false) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
      (∀ x, circuitFun n D x = true → circuitFun n C x = true) ∧
      (∀ x, x v = false → circuitFun n D x = circuitFun n C x) ∧
      ∀ (s : ℕ → Bool) (p l : ℕ), v.val ≠ p → v.val ≠ l →
        lineSingle D n s p l = lineSingle C n s p l := by
  have build (c : ℕ) (hc : c < n + r)
      (hdom : ∀ xs, xs.length = n → bv C xs c = true → bv C xs (n + r) = true)
      (heq : ∀ xs, xs.length = n → xs.getD v.val false = false →
        bv C xs (n + r) = bv C xs c)
      (hleq : ∀ s xs, xs.length = n → xs.getD v.val false = false →
        lv C s xs (n + r) = lv C s xs c) :
      ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
        (∀ x, circuitFun n D x = true → circuitFun n C x = true) ∧
        (∀ x, x v = false → circuitFun n D x = circuitFun n C x) ∧
        ∀ (s : ℕ → Bool) (p l : ℕ), v.val ≠ p → v.val ≠ l →
          lineSingle D n s p l = lineSingle C n s p l := by
    refine ⟨bypass n C r c, ao_to (bypass_ao hC hr hc), ?_, ?_, ?_, ?_⟩
    · simp only [Circuit.size, bypass_length]
      omega
    · intro x
      exact bypass_dom hC (List.ofFn x) (by simp) hr hc
        (hdom (List.ofFn x) (by simp))
    · intro x hx
      apply bypass_equal GateOp.eval false hC (List.ofFn x) (by simp) hr hc
      apply heq (List.ofFn x) (by simp)
      simpa [List.getD_eq_getElem?_getD, v.isLt] using hx
    · intro s p l hp hl
      let xs := (List.range n).map fun i => i == p || i == l
      have hx : xs.length = n := by simp [xs]
      have hv : xs.getD v.val false = false := by
        simp [xs, List.getD_eq_getElem?_getD, v.isLt, hp, hl]
      have he := bypass_equal lpE (false, false) hC (ini s xs)
        (by rw [ini_length, hx]) hr hc (hleq s xs hx hv)
      exact congrArg Prod.snd he
  rcases hz with hz | hz
  · have hdom : ∀ (xs : List Bool), xs.length = n →
        bv C xs b = true → bv C xs (n + r) = true := by
      intro xs hx h
      rw [bv_two hC xs hx hr hab, hop]
      simp [GateOp.eval, h]
    have heq : ∀ (xs : List Bool), xs.length = n → xs.getD v.val false = false →
        bv C xs (n + r) = bv C xs b := by
      intro xs hx hv
      rw [bv_two hC xs hx hr hab, hop, off_zero hC v.val a hz xs hx hv]
      simp [GateOp.eval]
    have hleq : ∀ (s : ℕ → Bool) (xs : List Bool), xs.length = n →
        xs.getD v.val false = false → lv C s xs (n + r) = lv C s xs b := by
      intro s xs hx hv
      have h0 := lv_zero hC s xs hx a (off_zero hC v.val a hz xs hx hv)
      rw [lv_two hC s xs hx hr hab, hop, h0]
      simp [lpE]
    exact build b hb hdom heq hleq
  · have hdom : ∀ (xs : List Bool), xs.length = n →
        bv C xs a = true → bv C xs (n + r) = true := by
      intro xs hx h
      rw [bv_two hC xs hx hr hab, hop]
      simp [GateOp.eval, h]
    have heq : ∀ (xs : List Bool), xs.length = n → xs.getD v.val false = false →
        bv C xs (n + r) = bv C xs a := by
      intro xs hx hv
      rw [bv_two hC xs hx hr hab, hop, off_zero hC v.val b hz xs hx hv]
      simp [GateOp.eval]
    have hleq : ∀ (s : ℕ → Bool) (xs : List Bool), xs.length = n →
        xs.getD v.val false = false → lv C s xs (n + r) = lv C s xs a := by
      intro s xs hx hv
      have h0 := lv_zero hC s xs hx b (off_zero hC v.val b hz xs hx hv)
      rw [lv_two hC s xs hx hr hab, hop, h0]
      simp [lpE]
    exact build a ha hdom heq hleq

end PEqualNP.Outside.L_meta_3473

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.L_meta_3473 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → (∃ (x5 : Fin x1 → Bool) (x6 : Fin x1 → Bool), (∀ (x7 : Fin x1), x7 ≠ x3 → x5 x7 = x6 x7) ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x5 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x6) → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x6 : Fin x1) => Decidable.decide (x6 = x3)) = Bool.false → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x7 ∧ x7.size < x2.size ∧ (∀ (x8 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x7 x8 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x8 = Bool.true) ∧ (∀ (x8 : Fin x1 → Bool), x8 x3 = Bool.false → PEqualNP.MetaComplexity.circuitFun x1 x7 x8 = PEqualNP.MetaComplexity.circuitFun x1 x2 x8) ∧ ∀ (x8 : ℕ → Bool) (x9 x10 : ℕ), ↑x3 ≠ x9 → ↑x3 ≠ x10 → PEqualNP.ReadK.lineSingle x7 x1 x8 x9 x10 = PEqualNP.ReadK.lineSingle x2 x1 x8 x9 x10 := by
  intro n C v hAO hdep hsingle
  have hC := PEqualNP.Outside.L_meta_3473.ao_of hAO
  obtain ⟨x, y, hxy, hne⟩ := hdep
  have hpos : 0 < C.gates.length := by
    by_contra hn
    have hlen : C.gates.length = 0 := by omega
    by_cases ho : C.output < n
    · let u : Fin n := ⟨C.output, ho⟩
      by_cases hu : u = v
      · rw [PEqualNP.Outside.L_meta_3473.circuit_eq,
          PEqualNP.Outside.L_meta_3473.bv_input C
            (List.ofFn (fun i : Fin n => decide (i = v))) (n := n) (by simp) ho] at hsingle
        have hh : (⟨C.output, ho⟩ : Fin n) = v := hu
        simp [List.getD_eq_getElem?_getD, ho, hh] at hsingle
      · apply hne
        rw [PEqualNP.Outside.L_meta_3473.circuit_eq,
          PEqualNP.Outside.L_meta_3473.circuit_eq,
          PEqualNP.Outside.L_meta_3473.bv_input C (List.ofFn x) (n := n) (by simp) ho,
          PEqualNP.Outside.L_meta_3473.bv_input C (List.ofFn y) (n := n) (by simp) ho]
        simpa [List.getD_eq_getElem?_getD, ho, u] using hxy u hu
    · have hbig : n + C.gates.length ≤ C.output := by omega
      apply hne
      change PEqualNP.Outside.L_meta_3473.bv C (List.ofFn x) C.output =
        PEqualNP.Outside.L_meta_3473.bv C (List.ofFn y) C.output
      rw [PEqualNP.Outside.L_meta_3473.bv_big C (List.ofFn x) (by simp) hbig,
        PEqualNP.Outside.L_meta_3473.bv_big C (List.ofFn y) (by simp) hbig]
  cases ht : PEqualNP.Outside.L_meta_3473.bv C
      (PEqualNP.Outside.L_meta_3473.topOff n v.val) C.output with
  | true =>
    obtain ⟨r, a, b, hr, hop, hab, ha, hb, hz⟩ :=
      PEqualNP.Outside.L_meta_3473.or_zero_exists hC v x y hxy hne ht
    exact PEqualNP.Outside.L_meta_3473.shrink_or hC v hr hop hab ha hb hz
  | false =>
    let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨[], n⟩
    have hD : ∀ z : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n D z = false := by
      intro z
      change (List.ofFn z).getD n false = false
      exact List.getD_eq_default _ _ (by simp)
    refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
    · exact PEqualNP.Outside.L_meta_3473.ao_to (by intro k hk; simp [D] at hk)
    · exact hpos
    · intro z hz
      rw [hD] at hz
      cases hz
    · intro z hz
      rw [hD, PEqualNP.Outside.L_meta_3473.circuit_eq]
      symm
      apply PEqualNP.Outside.L_meta_3473.off_zero hC v.val C.output ht
        (List.ofFn z) (by simp)
      simpa [List.getD_eq_getElem?_getD, v.isLt] using hz
    · intro s p l hp hl
      let xs := (List.range n).map fun i => i == p || i == l
      have hx : xs.length = n := by simp [xs]
      have hv : xs.getD v.val false = false := by
        simp [xs, List.getD_eq_getElem?_getD, v.isLt, hp, hl]
      have hc := PEqualNP.Outside.L_meta_3473.lv_zero hC s xs hx C.output
        (PEqualNP.Outside.L_meta_3473.off_zero hC v.val C.output ht xs hx hv)
      have hd := PEqualNP.Outside.L_meta_3473.lv_big D s xs hx (w := n) (by simp [D])
      change (PEqualNP.Outside.L_meta_3473.lv D s xs n).2 =
        (PEqualNP.Outside.L_meta_3473.lv C s xs C.output).2
      rw [hd, hc]
