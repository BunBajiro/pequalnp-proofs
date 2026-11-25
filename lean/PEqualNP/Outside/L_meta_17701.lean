import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17701

open PEqualNP.CircuitLowerBounds

def Grows (a b : Bool) : Prop := a = true → b = true

theorem read {xs ys : List Bool} (h : List.Forall₂ Grows xs ys) (i : ℕ) :
    Grows (xs.getD i false) (ys.getD i false) := by
  induction h generalizing i with
  | nil => simp [Grows]
  | cons hab _ ih =>
    cases i with
    | zero => exact hab
    | succ i => exact ih i

theorem run (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (xs ys : List Bool) (le : List.Forall₂ Grows xs ys) :
    List.Forall₂ Grows ((Circuit.mk gs 0).wires xs) ((Circuit.mk gs 0).wires ys) := by
  induction gs generalizing xs ys with
  | nil => exact le
  | cons g gs ih =>
    have gate : Grows (g.op.eval (g.inputs.map fun i => xs.getD i false))
        (g.op.eval (g.inputs.map fun i => ys.getD i false)) := by
      rcases ops g (by simp) with h | h
      · simp only [h,GateOp.eval,Grows,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
        intro hx i hi
        exact read le i (hx i hi)
      · simp only [h,GateOp.eval,Grows,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
        rintro ⟨i,hi,yes⟩
        exact ⟨i,hi,read le i yes⟩
    exact ih (fun g hg => ops g (List.mem_cons_of_mem _ hg)) _ _ (List.rel_append le (.cons gate .nil))

end PEqualNP.Outside.L_meta_17701

theorem PEqualNP.Outside.L_meta_17701 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → ∀ (x3 x4 : Fin (14 : ℕ) → Bool) (x5 : ℕ), (∀ (x6 : Fin (14 : ℕ)), x3 x6 = Bool.true → x4 x6 = Bool.true) → PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x3 x5 = Bool.true → PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x4 x5 = Bool.true) := by
  intro C legal x y i h
  have le : List.Forall₂ PEqualNP.Outside.L_meta_17701.Grows (List.ofFn x) (List.ofFn y) := by
    apply List.forall₂_iff_get.mpr
    refine ⟨by simp,?_⟩
    intro j hj _
    simp only [List.get_ofFn, PEqualNP.Outside.L_meta_17701.Grows]
    exact h ⟨j, by simpa only [List.length_ofFn] using hj⟩
  exact PEqualNP.Outside.L_meta_17701.read (PEqualNP.Outside.L_meta_17701.run C.gates legal.1 _ _ le) i
