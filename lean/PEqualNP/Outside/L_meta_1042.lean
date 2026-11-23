import PEqualNP.Defs
import Mathlib.Data.List.GetD

namespace PEqualNP.Outside.L_meta_1042

open PEqualNP.CircuitLowerBounds

private abbrev Mask := Fin 6 → Bool
private abbrev zeroMask : Mask := fun _ => false
private abbrev inputMask (i : Fin 6) : Mask := fun p => decide (i = p)
private abbrev inputs : List Mask := List.ofFn inputMask
private abbrev lines : Fin 4 → Finset (Fin 6) :=
  ![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}]
private abbrev target (k : Fin 4) : Mask := fun p => decide (p ∈ lines k)
private abbrev support (m : Mask) := Finset.univ.filter (fun i => m i = true)

-- A pair inside the triple, a four-set containing it, or its complement.
private abbrev pays (k : Fin 4) (m : Mask) : Prop :=
  ((support m).card = 2 ∧ support m ⊆ lines k) ∨
  ((support m).card = 4 ∧ lines k ⊆ support m) ∨
  m = (fun p => !(target k p))
private abbrev useful (k : Fin 4) (m : Mask) := m = target k ∨ pays k m

private def liftOp (op : GateOp) (args : List Mask) : Mask :=
  fun p => op.eval (args.map (fun m => m p))

private abbrev outputsTarget (args : List Mask) (k : Fin 4) :=
  liftOp .and args = target k ∨ liftOp .or args = target k ∨ liftOp .not args = target k

private lemma empty_case : ∀ k, ¬ outputsTarget [] k := by decide +kernel
private lemma unary_case : ∀ (k : Fin 4) (a : Mask),
    outputsTarget [a] k → useful k a := by decide +kernel
set_option maxHeartbeats 2000000 in
private lemma binary_case : ∀ (k : Fin 4) (a b : Mask),
    outputsTarget [a,b] k → useful k a ∨ useful k b := by decide +kernel

private lemma separate : ∀ (k j : Fin 4) (a : Mask), pays k a → pays j a → k = j := by
  decide +kernel
private lemma distinct_outputs : Function.Injective target := by decide +kernel
private lemma target_free : ∀ (k j : Fin 4), ¬ pays k (target j) := by decide +kernel
private lemma inputs_free : ∀ k : Fin 4, ∀ a ∈ inputs, ¬ useful k a := by decide +kernel
private lemma zero_free : ∀ k : Fin 4, ¬ useful k zeroMask := by decide +kernel

private abbrev allowed (g : Gate) := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
private abbrev args (g : Gate) (w : List Mask) := g.inputs.map (fun i => w.getD i zeroMask)
private abbrev gateMask (g : Gate) (w : List Mask) := liftOp g.op (args g w)

private lemma gate_source (g : Gate) (w : List Mask) (k : Fin 4) (hg : allowed g)
    (h : gateMask g w = target k) : ∃ a ∈ w, useful k a := by
  have hh : outputsTarget (args g w) k := by
    rcases hg.1 with e | e | e
    · exact Or.inl (by simpa only [gateMask, e] using h)
    · exact Or.inr (Or.inl (by simpa only [gateMask, e] using h))
    · exact Or.inr (Or.inr (by simpa only [gateMask, e] using h))
  have hl : (args g w).length ≤ 2 := by simpa only [args, List.length_map] using hg.2
  have found : ∃ a ∈ args g w, useful k a := by
    generalize args g w = l at hh hl ⊢
    cases l with
    | nil => exact (empty_case k hh).elim
    | cons a l =>
      cases l with
      | nil => exact ⟨a, by simp, unary_case k a hh⟩
      | cons b l =>
        cases l with
        | nil =>
          rcases binary_case k a b hh with ha | hb
          · exact ⟨a, by simp, ha⟩
          · exact ⟨b, by simp, hb⟩
        | cons c cs => simp at hl
  obtain ⟨a, ha, hu⟩ := found
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  refine ⟨_, ?_, hu⟩
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)] at hu
    exact (zero_free k hu).elim

private def trace : List Gate → List Mask → List Mask
  | [], _ => []
  | g :: gs, w =>
    let m := gateMask g w
    m :: trace gs (w ++ [m])

private lemma trace_length (gs : List Gate) (w : List Mask) : (trace gs w).length = gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp [trace, ih]

-- The first occurrence of each output needs an earlier mask assigned to that output.
private lemma first_source (k : Fin 4) (gs : List Gate) (w : List Mask)
    (hg : ∀ g ∈ gs, allowed g) (fresh : target k ∉ w) (hit : target k ∈ trace gs w) :
    ∃ a ∈ w ++ trace gs w, pays k a := by
  induction gs generalizing w with
  | nil => simp [trace] at hit
  | cons g gs ih =>
    let m := gateMask g w
    change target k ∈ m :: trace gs (w ++ [m]) at hit
    change ∃ a ∈ w ++ m :: trace gs (w ++ [m]), pays k a
    by_cases he : m = target k
    · obtain ⟨a, ha, hu⟩ := gate_source g w k (hg g (by simp)) he
      exact ⟨a, List.mem_append_left _ ha, hu.resolve_left (fun e => fresh (e ▸ ha))⟩
    · have hf : target k ∉ w ++ [m] := by simp [fresh, Ne.symm he]
      obtain ⟨a, ha, hp⟩ := ih (w ++ [m]) (fun z hz => hg z (List.mem_cons_of_mem _ hz))
        hf ((List.mem_cons.mp hit).resolve_left (Ne.symm he))
      exact ⟨a, by simpa using ha, hp⟩

private def boolStep (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

private lemma read_map (w : List Mask) (p : Fin 6) (i : ℕ) :
    (w.map (fun m => m p)).getD i false = (w.getD i zeroMask) p :=
  List.getD_map w zeroMask (fun m => m p)

private lemma evaluate (gs : List Gate) (w : List Mask) (p : Fin 6) :
    (w ++ trace gs w).map (fun m => m p) = gs.foldl boolStep (w.map (fun m => m p)) := by
  induction gs generalizing w with
  | nil => simp [trace]
  | cons g gs ih =>
    rw [List.foldl_cons]
    rw [show w ++ trace (g :: gs) w = (w ++ [gateMask g w]) ++ trace gs (w ++ [gateMask g w]) by
      simp [trace]]
    rw [ih]
    congr 1
    simp only [boolStep, List.map_append, List.map_cons, List.map_nil, gateMask, liftOp, args,
      List.map_map, Function.comp_def, read_map]

private lemma read_mem (w : List Mask) (i : ℕ) (k : Fin 4) (h : w.getD i zeroMask = target k) :
    target k ∈ w := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ hi] at h
    exact h ▸ List.getElem_mem hi
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)] at h
    exact (zero_free k (Or.inl h)).elim

end PEqualNP.Outside.L_meta_1042

open PEqualNP.Outside.L_meta_1042
open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1042 : (∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length) → ∀ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin 4 → ℕ), (∀ gg ∈ gl, (gg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gg.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gg.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gg.inputs.length ≤ 2) → (∃ ι : Fin 1 → Fin gl.length, ∀ qa : Fin gl.length, (gl.get qa).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ ka : Fin 1, ι ka = qa) → (∀ (oa : Fin 4) (xa : Fin 6 → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol oa⟩ (List.ofFn xa) = decide (∃ va ∈ (![{0, 1, 2}, {0, 3, 4}, {1, 3, 5}, {2, 4, 5}] : Fin 4 → Finset (Fin 6)) oa, xa va = true)) → 8 ≤ gl.length := by
  intro _ gs ol hg _ ho
  let log := trace gs inputs
  have occurs (k : Fin 4) : target k ∈ log := by
    have eqmask : (inputs ++ log).getD (ol k) zeroMask = target k := by
      funext p
      rw [← read_map, evaluate]
      simp only [inputs, List.map_ofFn, Function.comp_def]
      change (⟨gs, ol k⟩ : Circuit).eval (List.ofFn (fun i => inputMask i p)) = _
      rw [ho]
      simp [inputMask, target, lines]
    have hm := read_mem _ _ _ eqmask
    exact (List.mem_append.mp hm).resolve_left (fun h => inputs_free k _ h (Or.inl rfl))
  have paid (k : Fin 4) : ∃ m ∈ log, pays k m := by
    obtain ⟨m, hm, hp⟩ := first_source k gs inputs hg
      (fun h => inputs_free k _ h (Or.inl rfl)) (occurs k)
    exact ⟨m, (List.mem_append.mp hm).resolve_left (fun h => inputs_free k _ h (Or.inr hp)), hp⟩
  choose witness member assigned using paid
  let f : Fin 4 ⊕ Fin 4 → ↥log.toFinset := Sum.elim
    (fun k => ⟨target k, List.mem_toFinset.mpr (occurs k)⟩)
    (fun k => ⟨witness k, List.mem_toFinset.mpr (member k)⟩)
  have inj : Function.Injective f := by
    intro i j e
    have v := congrArg Subtype.val e
    cases i with
    | inl a =>
      cases j with
      | inl b => exact congrArg Sum.inl (distinct_outputs v)
      | inr b =>
        change target a = witness b at v
        exact (target_free b a (v.symm ▸ assigned b)).elim
    | inr a =>
      cases j with
      | inl b =>
        change witness a = target b at v
        exact (target_free a b (v ▸ assigned a)).elim
      | inr b =>
        change witness a = witness b at v
        exact congrArg Sum.inr (separate a b _ (assigned a) (v.symm ▸ assigned b))
  have hc := Fintype.card_le_of_injective f inj
  have hl := List.toFinset_card_le log
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe] at hc
  exact (hc.trans hl).trans_eq (trace_length gs inputs)
