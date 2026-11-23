import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_345

private abbrev edges : List (Fin 5 × Fin 5) :=
  [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 60000 in
private lemma subsetsChecked : ∀ S ∈ edges.toFinset.powerset,
    S.Nonempty → ∃ C : Finset (Fin 5), (∀ A ⊆ C, A.Nonempty → A ≠ C → ∃ e ∈ S, (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)) ∧ (∀ a b : Fin 5, a ∉ C → b ∉ C → (∃ x ∈ C, (x, a) ∈ S ∨ (a, x) ∈ S) → (∃ y ∈ C, (y, b) ∈ S ∨ (b, y) ∈ S) → ¬ ((a, b) ∈ edges ∨ (b, a) ∈ edges)) ∧ (S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1 := by
  exact @of_decide_eq_true _ Finset.decidableDforallFinset rfl

end PEqualNP.Outside.L_meta_345

open PEqualNP.Outside.L_meta_345

theorem PEqualNP.Outside.L_meta_345 :
    ∀ E : List (Fin 5 × Fin 5), E = [(0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4)] → ∀ S : Finset (Fin 5 × Fin 5), (∀ e ∈ S, e ∈ E) → S.Nonempty → ∃ C : Finset (Fin 5), (∀ A ⊆ C, A.Nonempty → A ≠ C → ∃ e ∈ S, (e.1 ∈ A ∧ e.2 ∈ C ∧ e.2 ∉ A) ∨ (e.2 ∈ A ∧ e.1 ∈ C ∧ e.1 ∉ A)) ∧ (∀ a b : Fin 5, a ∉ C → b ∉ C → (∃ x ∈ C, (x, a) ∈ S ∨ (a, x) ∈ S) → (∃ y ∈ C, (y, b) ∈ S ∨ (b, y) ∈ S) → ¬ ((a, b) ∈ E ∨ (b, a) ∈ E)) ∧ (S.filter (fun e => e.1 ∈ C ∨ e.2 ∈ C)).card % 2 = 1 := by
  intro E hE
  subst E
  intro S hS hne
  refine subsetsChecked S ?_ hne
  exact Finset.mem_powerset.mpr (fun e he => List.mem_toFinset.mpr (hS e he))
