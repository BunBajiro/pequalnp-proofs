import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1200

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [0, 9]⟩,
    ⟨.and, [1, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [4, 7]⟩,
    ⟨.and, [6, 13]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [15, 12]⟩,
    ⟨.or, [16, 14]⟩], 17⟩

theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_1200

open PEqualNP.Outside.L_meta_1200 in
theorem PEqualNP.Outside.L_meta_1200 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 6 && x 7)) x := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
