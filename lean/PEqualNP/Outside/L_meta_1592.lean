import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity SimpleGraph

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) :
    (L ++ [S]).getD L.length d = S := by simp

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

lemma normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool Nat

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, (Sum.inl c : Stat) ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

set_option maxHeartbeats 800000 in
lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

lemma elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length →
    (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

lemma agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj

def initAt (n : ℕ) (p : Fin n) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => if i = p then Sum.inl b else Sum.inr i.val)

lemma initAt_self (n : ℕ) (p : Fin n) (b : Bool) :
    (initAt n p b).getD p.val (Sum.inl false) = Sum.inl b := by
  simp [initAt]

lemma inv_initAt (n : ℕ) (p : Fin n) (b : Bool) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn (Function.update x p b)) (initAt n p b, []) := by
  refine ⟨by simp [initAt], ?_⟩
  intro i
  by_cases hi : i < n
  · by_cases hip : (⟨i, hi⟩ : Fin n) = p
    · simp [initAt, hi, hip, Stat.Valid, Stat.val, wiresFrom]
    · simp [initAt, hi, hip, Function.update_of_ne hip, Stat.Valid, Stat.val, wiresFrom]
  · have h1 : n ≤ i := by omega
    rw [List.getD_eq_default _ _ (by simpa [initAt] using h1),
      List.getD_eq_default _ _ (by simpa using h1)]
    exact ⟨trivial, rfl⟩

lemma eliminate_at {n s : ℕ} (f : (Fin n → Bool) → Bool) (p : Fin n) (b : Bool)
    (hdep : ∃ x : Fin n → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin n → Bool, f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize n f s) :
    ∃ t, t + 1 ≤ s ∧ HasCircuitSize n (fun x => f (Function.update x p b)) t := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initAt n p b, []) with hacc
  have hinv : ∀ x : Fin n → Bool,
      Inv n (List.ofFn x) (wiresFrom gs (List.ofFn (Function.update x p b))) acc := by
    intro x
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_initAt n p b x)
  have hval : ∀ x : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x))
        = f (Function.update x p b) := by
    intro x
    rw [((hinv x).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨x, y, hne⟩ := hnc
    apply hne
    rw [← hval x, ← hval y, hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
      by_cases hread : ∃ g ∈ gs, p.val ∈ g.inputs
      · have := elim_len_lt n p.val gs (initAt n p b, []) hnok
          (by simpa [initAt] using p.isLt) ⟨b, initAt_self n p b⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ p.val := by
          intro e
          rw [e, hacc, elim_getD n p.val _ gs _ (by simpa [initAt] using p.isLt)] at hst
          have hb := initAt_self n p b
          change (initAt n p b).getD p.val (Sum.inl false) = Sum.inr j at hst
          rw [hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        rw [← hevg, ← hevg]
        apply agree_except p.val gs _ _ hread (by simp) ?_ C.output hout
        intro a ha
        by_cases han : a < n
        · have hap : (⟨a, han⟩ : Fin n) ≠ p := fun e => ha (congrArg Fin.val e)
          simp [han, Function.update_of_ne hap]
        · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
    refine ⟨acc.2.length, hlen, ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_rfl, ?_⟩⟩
    intro x
    have := hval x
    rw [hst] at this
    exact this

noncomputable def F {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (x : Fin n → Bool) : Bool :=
  @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
    (Classical.propDecidable _)

lemma F_true {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    F G A x = true ↔ ((∃ a ∈ A, x a = true) ∨
      ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
  unfold F
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

lemma F_false {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    F G A (fun _ => false) = false := by
  rw [Bool.eq_false_iff, ne_eq, F_true]
  simp

lemma F_dep {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l u : Fin n)
    (h : G.Adj l u) (hu : u ∉ A) :
    ∃ x : Fin n → Bool, F G A (Function.update x l (!x l)) ≠ F G A x := by
  have hlu : l ≠ u := h.ne
  refine ⟨Function.update (fun _ => false) u true, ?_⟩
  have ht : F G A (Function.update (Function.update (fun _ => false) u true) l
      (!(Function.update (fun _ => false) u true l))) = true := by
    rw [F_true]
    exact Or.inr ⟨l, u, h, by simp [Function.update_of_ne hlu],
      by simp [Function.update_of_ne hlu.symm]⟩
  have hf : F G A (Function.update (fun _ => false) u true) = false := by
    rw [Bool.eq_false_iff, ne_eq, F_true]
    rintro (⟨a, ha, hx⟩ | ⟨i, j, hij, hi, hj⟩)
    · by_cases hau : a = u
      · exact hu (hau ▸ ha)
      · simp [Function.update_of_ne hau] at hx
    · have hiu : i = u := by
        by_contra hne
        simp [Function.update_of_ne hne] at hi
      have hju : j = u := by
        by_contra hne
        simp [Function.update_of_ne hne] at hj
      exact hij.ne (hiu.trans hju.symm)
  rw [ht, hf]
  simp

lemma F_restrict {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l u : Fin n)
    (hl : l ∉ A) (hleaf : ∀ v, G.Adj l v → v = u) (x : Fin n → Bool) :
    F G A (Function.update x l false) = F (G.deleteEdges {s(l, u)}) A x := by
  rw [Bool.eq_iff_iff, F_true, F_true]
  apply or_congr
  · constructor
    · rintro ⟨a, ha, hx⟩
      have hal : a ≠ l := fun e => hl (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal] at hx⟩
    · rintro ⟨a, ha, hx⟩
      have hal : a ≠ l := fun e => hl (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal]⟩
  · constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      have hil : i ≠ l := by rintro rfl; simp at hi
      have hjl : j ≠ l := by rintro rfl; simp at hj
      refine ⟨i, j, deleteEdges_adj.mpr ⟨hij, by simp [hil, hjl]⟩,
        by rwa [Function.update_of_ne hil] at hi,
        by rwa [Function.update_of_ne hjl] at hj⟩
    · rintro ⟨i, j, hdeleted, hi, hj⟩
      obtain ⟨hG, hne⟩ := deleteEdges_adj.mp hdeleted
      have hil : i ≠ l := by
        rintro rfl
        have hju := hleaf j hG
        subst j
        exact hne rfl
      have hjl : j ≠ l := by
        rintro rfl
        have hiu := hleaf i hG.symm
        subst i
        exact hne Sym2.eq_swap
      exact ⟨i, j, hG, by rwa [Function.update_of_ne hil],
        by rwa [Function.update_of_ne hjl]⟩

def Cover {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T

lemma cover_transfer {n : ℕ} (G : SimpleGraph (Fin n)) (l u : Fin n)
    (hsmall : ∀ T : Finset (Fin n), Cover G T → l ∈ T →
      ∃ T' : Finset (Fin n), Cover G T' ∧ T'.card < T.card)
    (k : ℕ) (hk : ∀ T : Finset (Fin n), Cover G T → k ≤ T.card) :
    ∀ T : Finset (Fin n), Cover (G.deleteEdges {s(l, u)}) T → k ≤ T.card := by
  classical
  intro T hT
  have hc : Cover G (insert l T) := by
    intro i j hij
    by_cases hil : i = l
    · subst i; exact Or.inl (Finset.mem_insert_self _ _)
    by_cases hjl : j = l
    · subst j; exact Or.inr (Finset.mem_insert_self _ _)
    rcases hT i j (deleteEdges_adj.mpr ⟨hij, by simp [hil, hjl]⟩) with hi | hj
    · exact Or.inl (Finset.mem_insert_of_mem hi)
    · exact Or.inr (Finset.mem_insert_of_mem hj)
  obtain ⟨T', hT', hcard⟩ := hsmall (insert l T) hc (Finset.mem_insert_self _ _)
  have hlow := hk T' hT'
  have hins := Finset.card_insert_le l T
  omega

lemma remaining_edge {n : ℕ} (G : SimpleGraph (Fin n)) (l u : Fin n) (hlu : G.Adj l u)
    (hsmall : ∀ T : Finset (Fin n), Cover G T → l ∈ T →
      ∃ T' : Finset (Fin n), Cover G T' ∧ T'.card < T.card) :
    ∃ i j : Fin n, (G.deleteEdges {s(l, u)}).Adj i j := by
  classical
  have hk : ∀ T : Finset (Fin n), Cover G T → 1 ≤ T.card := by
    intro T hT
    have hne : T.Nonempty := by
      rcases hT l u hlu with h | h
      · exact ⟨l, h⟩
      · exact ⟨u, h⟩
    exact hne.card_pos
  by_contra! hno
  have hc : Cover (G.deleteEdges {s(l, u)}) ∅ := by
    intro i j hij
    exact (hno i j hij).elim
  have := cover_transfer G l u hsmall 1 hk ∅ hc
  simp at this

lemma incidence_leaf {n : ℕ} (G : SimpleGraph (Fin n)) (l u : Fin n)
    (hleaf : ∀ v, G.Adj l v ↔ v = u) : G.incidenceSet l = {s(l, u)} := by
  ext e
  constructor
  · intro he
    change e ∈ G.edgeSet ∧ l ∈ e at he
    rcases Sym2.mem_iff_exists.mp he.2 with ⟨v, rfl⟩
    have hv : v = u := (hleaf v).mp (G.mem_edgeSet.mp he.1)
    simp [hv]
  · rintro rfl
    change s(l, u) ∈ G.edgeSet ∧ l ∈ s(l, u)
    exact ⟨G.mem_edgeSet.mpr ((hleaf u).mpr rfl), Sym2.mem_mk_left _ _⟩

end PEqualNP.Outside.L_meta_1592

theorem PEqualNP.Outside.L_meta_1592 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l u : Fin n),
    (∀ v : Fin n, (G.neighborSet v).ncard ≤ 3) →
    (∀ (w : Fin n) (c : G.Walk w w), c.IsCycle → 7 ≤ c.length) →
    (∀ i j : Fin n, G.Adj i j → i ∉ A) →
    (∀ y : Fin n, G.Adj l y ↔ y = u) →
    (∀ T : Finset (Fin n),
      (∀ i1 j1 : Fin n, G.Adj i1 j1 → i1 ∈ T ∨ j1 ∈ T) → l ∈ T →
      ∃ T' : Finset (Fin n),
        (∀ i2 j2 : Fin n, G.Adj i2 j2 → i2 ∈ T' ∨ j2 ∈ T') ∧ T'.card < T.card) →
    (∀ k' s' : ℕ,
      (∀ T2 : Finset (Fin n),
        (∀ i3 j3 : Fin n, (G.deleteEdges (G.incidenceSet l)).Adj i3 j3 → i3 ∈ T2 ∨ j3 ∈ T2) →
        k' ≤ T2.card) →
      PEqualNP.MetaComplexity.HasCircuitSize n
        (fun x' : Fin n → Bool =>
          @decide ((∃ a' ∈ A, x' a' = true) ∨
            ∃ i4 j4 : Fin n, (G.deleteEdges (G.incidenceSet l)).Adj i4 j4 ∧
              x' i4 = true ∧ x' j4 = true) (Classical.propDecidable _)) s' →
      A.card + (G.deleteEdges (G.incidenceSet l)).edgeSet.ncard + k' ≤ s' + 1) →
    ∀ k s : ℕ,
      (∀ T3 : Finset (Fin n),
        (∀ i5 j5 : Fin n, G.Adj i5 j5 → i5 ∈ T3 ∨ j5 ∈ T3) → k ≤ T3.card) →
      PEqualNP.MetaComplexity.HasCircuitSize n
        (fun x : Fin n → Bool =>
          @decide ((∃ a ∈ A, x a = true) ∨
            ∃ i6 j6 : Fin n, G.Adj i6 j6 ∧ x i6 = true ∧ x j6 = true)
              (Classical.propDecidable _)) s →
      A.card + G.edgeSet.ncard + k ≤ s + 1 := by
  classical
  intro n G A l u _hdeg _hcycle hA hleaf hsmall ih k s hk hc
  have hlu : G.Adj l u := (hleaf u).mpr rfl
  have hinc := PEqualNP.Outside.L_meta_1592.incidence_leaf G l u hleaf
  rw [hinc] at ih
  have hr := PEqualNP.Outside.L_meta_1592.F_restrict G A l u (hA l u hlu)
    (fun v h => (hleaf v).mp h)
  obtain ⟨i, j, hij⟩ := PEqualNP.Outside.L_meta_1592.remaining_edge G l u hlu hsmall
  have hnc : ∃ x y : Fin n → Bool,
      PEqualNP.Outside.L_meta_1592.F G A (Function.update x l false) ≠
      PEqualNP.Outside.L_meta_1592.F G A (Function.update y l false) := by
    refine ⟨fun _ => true, fun _ => false, ?_⟩
    rw [hr, hr, PEqualNP.Outside.L_meta_1592.F_false]
    have ht : PEqualNP.Outside.L_meta_1592.F (G.deleteEdges {s(l, u)}) A (fun _ => true) = true := by
      rw [PEqualNP.Outside.L_meta_1592.F_true]
      exact Or.inr ⟨i, j, hij, rfl, rfl⟩
    rw [ht]
    simp
  obtain ⟨t, hts, ht⟩ := PEqualNP.Outside.L_meta_1592.eliminate_at
    (PEqualNP.Outside.L_meta_1592.F G A) l false
    (PEqualNP.Outside.L_meta_1592.F_dep G A l u hlu (hA u l hlu.symm)) hnc hc
  have heq : (fun x => PEqualNP.Outside.L_meta_1592.F G A (Function.update x l false)) =
      PEqualNP.Outside.L_meta_1592.F (G.deleteEdges {s(l, u)}) A := funext hr
  rw [heq] at ht
  have hbound := ih k t (PEqualNP.Outside.L_meta_1592.cover_transfer G l u hsmall k hk) ht
  have hcard : (G.deleteEdges {s(l, u)}).edgeSet.ncard + 1 = G.edgeSet.ncard := by
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact Set.ncard_sdiff_singleton_add_one (G.mem_edgeSet.mpr hlu)
  omega
