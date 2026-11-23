import Mathlib.Combinatorics.SimpleGraph.Acyclic
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_902

open PEqualNP.MetaComplexity

private lemma cycle_two_neighbors (G : SimpleGraph (Fin 7)) {v w : Fin 7} {c : G.Walk v v} (hc : c.IsCycle)
    (hw : w ∈ c.support) :
    ∃ u1 u2 : Fin 7, G.Adj w u1 ∧ G.Adj w u2 ∧ u1 ≠ u2 ∧
      u1 ∈ c.support ∧ u2 ∈ c.support := by
  classical
  let c' := c.rotate w hw
  have hc' : c'.IsCycle := hc.rotate hw
  have hlen : 3 ≤ c'.length := hc'.three_le_length
  have hmem_rot : ∀ x : Fin 7, x ∈ c'.support → x ∈ c.support := by
    intro x hx
    exact (SimpleGraph.Walk.mem_support_rotate_iff c w hw).1 hx
  cases hc'eq : c' with
  | nil => rw [hc'eq] at hlen; simp at hlen
  | cons h1 p =>
    rename_i u1
    have hp_len : 2 ≤ p.length := by rw [hc'eq] at hlen; simp at hlen; omega
    have hnodup : (s(w, u1) :: p.edges).Nodup := by
      have := hc'.edges_nodup
      rw [hc'eq] at this
      exact this
    cases hrev : p.reverse with
    | nil =>
      have : p.reverse.length = p.length := SimpleGraph.Walk.length_reverse p
      rw [hrev] at this; simp at this; omega
    | cons h2 q =>
      rename_i u2
      have hmem_e : s(w, u2) ∈ p.edges := by
        have h1e : s(w, u2) ∈ p.reverse.edges := by rw [hrev]; simp
        rw [SimpleGraph.Walk.edges_reverse] at h1e
        exact List.mem_reverse.1 h1e
      have hne : u1 ≠ u2 := by
        intro heq
        subst heq
        exact (List.nodup_cons.1 hnodup).1 hmem_e
      have hu1 : u1 ∈ c.support := by
        apply hmem_rot
        rw [hc'eq]
        simp [SimpleGraph.Walk.start_mem_support]
      have hu2 : u2 ∈ c.support := by
        apply hmem_rot
        rw [hc'eq]
        have hu2p : u2 ∈ p.reverse.support := by
          rw [hrev]; simp [SimpleGraph.Walk.start_mem_support]
        rw [SimpleGraph.Walk.support_reverse] at hu2p
        exact List.mem_cons_of_mem w (List.mem_reverse.1 hu2p)
      exact ⟨u1, u2, h1, h2, hne, hu1, hu2⟩

private lemma orderedForest (G : SimpleGraph (Fin 7))
    (huniq : ∀ a b d : Fin 7, G.Adj a b → G.Adj a d → b.val < a.val → d.val < a.val → b = d) : G.IsAcyclic := by
  intro v c hc
  have hne : c.support.toFinset.Nonempty := by
    refine ⟨v, List.mem_toFinset.2 (SimpleGraph.Walk.start_mem_support c)⟩
  obtain ⟨m, hm_mem, hm_max⟩ := Finset.exists_max_image c.support.toFinset (fun x : Fin 7 => x.val) hne
  obtain ⟨u1, u2, h1, h2, hne12, hu1, hu2⟩ := cycle_two_neighbors G hc (List.mem_toFinset.1 hm_mem)
  have hle1 : u1.val ≤ m.val := hm_max u1 (List.mem_toFinset.2 hu1)
  have hle2 : u2.val ≤ m.val := hm_max u2 (List.mem_toFinset.2 hu2)
  have hne1 : u1 ≠ m := G.ne_of_adj h1.symm
  have hne2 : u2 ≠ m := G.ne_of_adj h2.symm
  have hlt1 : u1.val < m.val := lt_of_le_of_ne hle1 (fun h => hne1 (Fin.ext h))
  have hlt2 : u2.val < m.val := lt_of_le_of_ne hle2 (fun h => hne2 (Fin.ext h))
  exact hne12 (huniq m u1 u2 h1 h2 hlt1 hlt2)

private lemma forestSize (G : SimpleGraph (Fin 7)) [DecidableRel G.Adj]
    (T : Finset (Fin 7)) (f : (Fin 7 → Bool) → Bool) (k : ℕ)
    (huniq : ∀ a b d : Fin 7, G.Adj a b → G.Adj a d → b.val < a.val → d.val < a.val → b = d)
    (edge : G.Adj 0 1)
    (cover : ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T)
    (least : ∀ S : Finset (Fin 7), (∀ i j, G.Adj i j → i ∈ S ∨ j ∈ S) → T.card ≤ S.card)
    (size_eq : G.edgeFinset.card + T.card - 1 = k)
    (eval_eq : ∀ x, decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) = f x) :
    ∀ s, HasCircuitSize 7 f s ↔ k ≤ s := by
  intro s
  rw [← funext eval_eq, ← size_eq]
  constructor
  · intro h
    have bound := L104 7 T.card s G (orderedForest G huniq) ⟨0, 1, edge⟩ least h
    omega
  · intro h
    obtain ⟨C, ho, hl, he⟩ := L105 7 G T ⟨0, 1, edge⟩ cover
    exact ⟨C, ho, hl.trans h, he⟩

private abbrev graph1 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 0 ∧ j = 5) ∨ (i = 0 ∧ j = 6))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private lemma case1 : ∀ s1 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x1 : Fin 7 → Bool => (x1 0 && x1 1) || (x1 0 && x1 2) || (x1 0 && x1 3) || (x1 0 && x1 4) || (x1 0 && x1 5) || (x1 0 && x1 6)) s1 ↔ 6 ≤ s1 := by
  let _ : DecidableRel graph1.Adj := inferInstance
  apply forestSize graph1 {0}
  all_goals exact of_decide_eq_true rfl

private abbrev graph2 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 0 ∧ j = 5) ∨ (i = 1 ∧ j = 6))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private lemma case2 : ∀ s2 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x2 : Fin 7 → Bool => (x2 0 && x2 1) || (x2 0 && x2 2) || (x2 0 && x2 3) || (x2 0 && x2 4) || (x2 0 && x2 5) || (x2 1 && x2 6)) s2 ↔ 7 ≤ s2 := by
  let _ : DecidableRel graph2.Adj := inferInstance
  apply forestSize graph2 {0, 1}
  all_goals exact of_decide_eq_true rfl

private abbrev graph3 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 1 ∧ j = 5) ∨ (i = 2 ∧ j = 6))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private lemma case3 : ∀ s3 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x3 : Fin 7 → Bool => (x3 0 && x3 1) || (x3 0 && x3 2) || (x3 1 && x3 3) || (x3 1 && x3 4) || (x3 1 && x3 5) || (x3 2 && x3 6)) s3 ↔ 7 ≤ s3 := by
  let _ : DecidableRel graph3.Adj := inferInstance
  apply forestSize graph3 {1, 2}
  all_goals exact of_decide_eq_true rfl

private abbrev graph4 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 1 ∧ j = 5) ∨ (i = 1 ∧ j = 6))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private lemma case4 : ∀ s4 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x4 : Fin 7 → Bool => (x4 0 && x4 1) || (x4 0 && x4 2) || (x4 0 && x4 3) || (x4 0 && x4 4) || (x4 1 && x4 5) || (x4 1 && x4 6)) s4 ↔ 7 ≤ s4 := by
  let _ : DecidableRel graph4.Adj := inferInstance
  apply forestSize graph4 {0, 1}
  all_goals exact of_decide_eq_true rfl

private abbrev graph5 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 1 ∧ j = 5) ∨ (i = 2 ∧ j = 6))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private lemma case5 : ∀ s5 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x5 : Fin 7 → Bool => (x5 0 && x5 1) || (x5 0 && x5 2) || (x5 0 && x5 3) || (x5 0 && x5 4) || (x5 1 && x5 5) || (x5 2 && x5 6)) s5 ↔ 8 ≤ s5 := by
  let _ : DecidableRel graph5.Adj := inferInstance
  apply forestSize graph5 {0, 1, 2}
  all_goals exact of_decide_eq_true rfl

private abbrev graph6 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 5) ∨ (i = 2 ∧ j = 6))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private lemma case6 : ∀ s6 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x6 : Fin 7 → Bool => (x6 0 && x6 1) || (x6 0 && x6 2) || (x6 1 && x6 3) || (x6 1 && x6 4) || (x6 2 && x6 5) || (x6 2 && x6 6)) s6 ↔ 7 ≤ s6 := by
  let _ : DecidableRel graph6.Adj := inferInstance
  apply forestSize graph6 {1, 2}
  all_goals exact of_decide_eq_true rfl

private abbrev graph7 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 5) ∨ (i = 5 ∧ j = 6))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private lemma case7 : ∀ s7 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x7 : Fin 7 → Bool => (x7 0 && x7 1) || (x7 0 && x7 2) || (x7 1 && x7 3) || (x7 1 && x7 4) || (x7 2 && x7 5) || (x7 5 && x7 6)) s7 ↔ 8 ≤ s7 := by
  let _ : DecidableRel graph7.Adj := inferInstance
  apply forestSize graph7 {1, 2, 5}
  all_goals exact of_decide_eq_true rfl

private abbrev graph8 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 5) ∨ (i = 4 ∧ j = 6))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private lemma case8 : ∀ s8 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x8 : Fin 7 → Bool => (x8 0 && x8 1) || (x8 0 && x8 2) || (x8 0 && x8 3) || (x8 1 && x8 4) || (x8 2 && x8 5) || (x8 4 && x8 6)) s8 ↔ 8 ≤ s8 := by
  let _ : DecidableRel graph8.Adj := inferInstance
  apply forestSize graph8 {0, 2, 4}
  all_goals exact of_decide_eq_true rfl

private abbrev graph9 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 1 ∧ j = 5) ∨ (i = 2 ∧ j = 6))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private lemma case9 : ∀ s9 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x9 : Fin 7 → Bool => (x9 0 && x9 1) || (x9 0 && x9 2) || (x9 0 && x9 3) || (x9 1 && x9 4) || (x9 1 && x9 5) || (x9 2 && x9 6)) s9 ↔ 8 ≤ s9 := by
  let _ : DecidableRel graph9.Adj := inferInstance
  apply forestSize graph9 {0, 1, 2}
  all_goals exact of_decide_eq_true rfl

private abbrev graph10 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 5) ∨ (i = 3 ∧ j = 6))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private lemma case10 : ∀ s10 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x10 : Fin 7 → Bool => (x10 0 && x10 1) || (x10 0 && x10 2) || (x10 0 && x10 3) || (x10 1 && x10 4) || (x10 2 && x10 5) || (x10 3 && x10 6)) s10 ↔ 8 ≤ s10 := by
  let _ : DecidableRel graph10.Adj := inferInstance
  apply forestSize graph10 {1, 2, 3}
  all_goals exact of_decide_eq_true rfl

private abbrev graph11 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨ (i = 5 ∧ j = 6))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private lemma case11 : ∀ s11 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x11 : Fin 7 → Bool => (x11 0 && x11 1) || (x11 0 && x11 2) || (x11 0 && x11 3) || (x11 0 && x11 4) || (x11 5 && x11 6)) s11 ↔ 6 ≤ s11 := by
  let _ : DecidableRel graph11.Adj := inferInstance
  apply forestSize graph11 {0, 5}
  all_goals exact of_decide_eq_true rfl

private abbrev graph12 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 4 ∧ j = 5) ∨ (i = 4 ∧ j = 6))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private lemma case12 : ∀ s12 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x12 : Fin 7 → Bool => (x12 0 && x12 1) || (x12 0 && x12 2) || (x12 0 && x12 3) || (x12 4 && x12 5) || (x12 4 && x12 6)) s12 ↔ 6 ≤ s12 := by
  let _ : DecidableRel graph12.Adj := inferInstance
  apply forestSize graph12 {0, 4}
  all_goals exact of_decide_eq_true rfl

private abbrev graph13 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 5 ∧ j = 6))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private lemma case13 : ∀ s13 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x13 : Fin 7 → Bool => (x13 0 && x13 1) || (x13 0 && x13 2) || (x13 0 && x13 3) || (x13 1 && x13 4) || (x13 5 && x13 6)) s13 ↔ 7 ≤ s13 := by
  let _ : DecidableRel graph13.Adj := inferInstance
  apply forestSize graph13 {0, 1, 5}
  all_goals exact of_decide_eq_true rfl

private abbrev graph14 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨ (i = 5 ∧ j = 6))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private lemma case14 : ∀ s14 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x14 : Fin 7 → Bool => (x14 0 && x14 1) || (x14 0 && x14 2) || (x14 1 && x14 3) || (x14 2 && x14 4) || (x14 5 && x14 6)) s14 ↔ 7 ≤ s14 := by
  let _ : DecidableRel graph14.Adj := inferInstance
  apply forestSize graph14 {1, 2, 5}
  all_goals exact of_decide_eq_true rfl

private abbrev graph15 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 4 ∧ j = 5) ∨ (i = 4 ∧ j = 6))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private lemma case15 : ∀ s15 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x15 : Fin 7 → Bool => (x15 0 && x15 1) || (x15 0 && x15 2) || (x15 1 && x15 3) || (x15 4 && x15 5) || (x15 4 && x15 6)) s15 ↔ 7 ≤ s15 := by
  let _ : DecidableRel graph15.Adj := inferInstance
  apply forestSize graph15 {0, 1, 4}
  all_goals exact of_decide_eq_true rfl

private abbrev graph16 : SimpleGraph (Fin 7) :=
  SimpleGraph.fromRel (fun i j => (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 3 ∧ j = 4) ∨ (i = 5 ∧ j = 6))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private lemma case16 : ∀ s16 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x16 : Fin 7 → Bool => (x16 0 && x16 1) || (x16 0 && x16 2) || (x16 3 && x16 4) || (x16 5 && x16 6)) s16 ↔ 6 ≤ s16 := by
  let _ : DecidableRel graph16.Adj := inferInstance
  apply forestSize graph16 {0, 3, 5}
  all_goals exact of_decide_eq_true rfl

end PEqualNP.Outside.L_meta_902

open PEqualNP.Outside.L_meta_902

theorem PEqualNP.Outside.L_meta_902 :
    (∀ s1 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x1 : Fin 7 → Bool => (x1 0 && x1 1) || (x1 0 && x1 2) || (x1 0 && x1 3) || (x1 0 && x1 4) || (x1 0 && x1 5) || (x1 0 && x1 6)) s1 ↔ 6 ≤ s1) ∧
    (∀ s2 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x2 : Fin 7 → Bool => (x2 0 && x2 1) || (x2 0 && x2 2) || (x2 0 && x2 3) || (x2 0 && x2 4) || (x2 0 && x2 5) || (x2 1 && x2 6)) s2 ↔ 7 ≤ s2) ∧
    (∀ s3 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x3 : Fin 7 → Bool => (x3 0 && x3 1) || (x3 0 && x3 2) || (x3 1 && x3 3) || (x3 1 && x3 4) || (x3 1 && x3 5) || (x3 2 && x3 6)) s3 ↔ 7 ≤ s3) ∧
    (∀ s4 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x4 : Fin 7 → Bool => (x4 0 && x4 1) || (x4 0 && x4 2) || (x4 0 && x4 3) || (x4 0 && x4 4) || (x4 1 && x4 5) || (x4 1 && x4 6)) s4 ↔ 7 ≤ s4) ∧
    (∀ s5 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x5 : Fin 7 → Bool => (x5 0 && x5 1) || (x5 0 && x5 2) || (x5 0 && x5 3) || (x5 0 && x5 4) || (x5 1 && x5 5) || (x5 2 && x5 6)) s5 ↔ 8 ≤ s5) ∧
    (∀ s6 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x6 : Fin 7 → Bool => (x6 0 && x6 1) || (x6 0 && x6 2) || (x6 1 && x6 3) || (x6 1 && x6 4) || (x6 2 && x6 5) || (x6 2 && x6 6)) s6 ↔ 7 ≤ s6) ∧
    (∀ s7 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x7 : Fin 7 → Bool => (x7 0 && x7 1) || (x7 0 && x7 2) || (x7 1 && x7 3) || (x7 1 && x7 4) || (x7 2 && x7 5) || (x7 5 && x7 6)) s7 ↔ 8 ≤ s7) ∧
    (∀ s8 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x8 : Fin 7 → Bool => (x8 0 && x8 1) || (x8 0 && x8 2) || (x8 0 && x8 3) || (x8 1 && x8 4) || (x8 2 && x8 5) || (x8 4 && x8 6)) s8 ↔ 8 ≤ s8) ∧
    (∀ s9 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x9 : Fin 7 → Bool => (x9 0 && x9 1) || (x9 0 && x9 2) || (x9 0 && x9 3) || (x9 1 && x9 4) || (x9 1 && x9 5) || (x9 2 && x9 6)) s9 ↔ 8 ≤ s9) ∧
    (∀ s10 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x10 : Fin 7 → Bool => (x10 0 && x10 1) || (x10 0 && x10 2) || (x10 0 && x10 3) || (x10 1 && x10 4) || (x10 2 && x10 5) || (x10 3 && x10 6)) s10 ↔ 8 ≤ s10) ∧
    (∀ s11 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x11 : Fin 7 → Bool => (x11 0 && x11 1) || (x11 0 && x11 2) || (x11 0 && x11 3) || (x11 0 && x11 4) || (x11 5 && x11 6)) s11 ↔ 6 ≤ s11) ∧
    (∀ s12 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x12 : Fin 7 → Bool => (x12 0 && x12 1) || (x12 0 && x12 2) || (x12 0 && x12 3) || (x12 4 && x12 5) || (x12 4 && x12 6)) s12 ↔ 6 ≤ s12) ∧
    (∀ s13 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x13 : Fin 7 → Bool => (x13 0 && x13 1) || (x13 0 && x13 2) || (x13 0 && x13 3) || (x13 1 && x13 4) || (x13 5 && x13 6)) s13 ↔ 7 ≤ s13) ∧
    (∀ s14 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x14 : Fin 7 → Bool => (x14 0 && x14 1) || (x14 0 && x14 2) || (x14 1 && x14 3) || (x14 2 && x14 4) || (x14 5 && x14 6)) s14 ↔ 7 ≤ s14) ∧
    (∀ s15 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x15 : Fin 7 → Bool => (x15 0 && x15 1) || (x15 0 && x15 2) || (x15 1 && x15 3) || (x15 4 && x15 5) || (x15 4 && x15 6)) s15 ↔ 7 ≤ s15) ∧
    (∀ s16 : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x16 : Fin 7 → Bool => (x16 0 && x16 1) || (x16 0 && x16 2) || (x16 3 && x16 4) || (x16 5 && x16 6)) s16 ↔ 6 ≤ s16) := by
  exact ⟨case1, case2, case3, case4, case5, case6, case7, case8, case9, case10, case11, case12, case13, case14, case15, case16⟩
