import Cslib.Foundations.Data.RelatesInSteps
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Find
import Mathlib.GroupTheory.Perm.List
import Mathlib.Order.WellFoundedSet
import Mathlib.Tactic.Linarith

namespace EconCSLean
namespace Graph

/--
On a finite type, a non-well-founded relation has a directed cycle in its
transitive closure.
-/
theorem exists_transGen_self_of_not_wellFounded
    {α : Type*} [Finite α]
    {r : α → α → Prop} (h : ¬ WellFounded r) :
    ∃ i, Relation.TransGen r i i := by
  classical
  by_contra hcycle
  have hnoCycle : ∀ i, ¬ Relation.TransGen r i i := by
    intro i hi
    exact hcycle ⟨i, hi⟩
  haveI : Std.Irrefl (Relation.TransGen r) := ⟨hnoCycle⟩
  haveI : IsTrans α (Relation.TransGen r) := inferInstance
  have hwfTrans : WellFounded (Relation.TransGen r) :=
    Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen r)
  have hsub : Subrelation r (Relation.TransGen r) := by
    intro i j hij
    exact Relation.TransGen.single hij
  exact h (Subrelation.wf hsub hwfTrans)

/-- Convert a transitive-closure path into a positive step-indexed path. -/
theorem exists_relatesInSteps_pos_of_transGen
    {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.TransGen r a b) :
    ∃ n, 0 < n ∧ Relation.RelatesInSteps r a b n := by
  induction h with
  | single h =>
      exact ⟨1, by decide, Relation.RelatesInSteps.single h⟩
  | tail hab hbc ih =>
      obtain ⟨n, _hnpos, hn⟩ := ih
      exact ⟨n + 1, Nat.succ_pos n,
        Relation.RelatesInSteps.tail _ _ _ n hn hbc⟩

/-- Convert a step-indexed path into a concrete list chain. -/
theorem exists_chain_list_of_relatesInSteps
    {α : Type*} {r : α → α → Prop} {a b : α} :
    ∀ {n}, Relation.RelatesInSteps r a b n →
      ∃ l : List α,
        l.length = n + 1 ∧ l.head? = some a ∧
          l.getLast? = some b ∧ l.IsChain r := by
  intro n h
  induction h with
  | refl =>
      exact ⟨[a], by simp⟩
  | tail t' t'' n h₁ h₂ ih =>
      obtain ⟨l, hlen, hhead, hlast, hchain⟩ := ih
      refine ⟨l ++ [t''], ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · rw [List.head?_append_of_ne_nil]
        · exact hhead
        · intro hnil
          simp [hnil] at hlen
      · simp
      · apply hchain.append (by simp)
        intro x hx y hy
        rw [List.head?_singleton, Option.mem_some_iff] at hy
        subst y
        have hx' : t' = x := by
          simpa [hlast] using hx
        subst x
        exact h₂

/--
In a concrete chain list, earlier entries are related to later entries by a
step-indexed path whose length is the index gap.
-/
theorem isChain_relatesInSteps_getElem
    {α : Type*} {r : α → α → Prop} {l : List α}
    (hchain : l.IsChain r) :
    ∀ {i j : ℕ} (hi : i < l.length) (hj : j < l.length), i ≤ j →
      Relation.RelatesInSteps r (l[i]'hi) (l[j]'hj) (j - i) := by
  intro i j hi hj hij
  induction j generalizing i with
  | zero =>
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hij
      subst i
      exact Relation.RelatesInSteps.refl _
  | succ j ih =>
      rcases Nat.lt_or_eq_of_le hij with hijlt | rfl
      · have hij_le : i ≤ j := Nat.lt_succ_iff.mp hijlt
        have hj_prev : j < l.length := Nat.lt_of_succ_lt hj
        have hprev := ih hi hj_prev hij_le
        have hedge : r (l[j]'hj_prev) (l[j + 1]'hj) := by
          exact hchain.getElem j hj
        have hsub : (j + 1 - i) = (j - i) + 1 := by omega
        simpa [hsub] using
          Relation.RelatesInSteps.tail _ _ _ (j - i) hprev hedge
      · simp

/--
A closed chain over a nodup list induces directed edges along `List.formPerm`.
-/
theorem edge_formPerm_of_closed_nodup_chain
    {α : Type*} [DecidableEq α] {r : α → α → Prop} {l : List α}
    (hnodup : l.Nodup) (hlen : 0 < l.length)
    (hchain : (l ++ [l[0]]).IsChain r) :
    ∀ x, x ∈ l → r x (l.formPerm x) := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  rw [List.formPerm_apply_getElem l hnodup k hk]
  have hrelFull :
      r ((l ++ [l[0]])[k]'(by simp; omega))
        ((l ++ [l[0]])[k + 1]'(by simp [hk])) := by
    exact hchain.getElem k (by simp [hk])
  by_cases hknext : k + 1 < l.length
  · have hmod : (k + 1) % l.length = k + 1 := Nat.mod_eq_of_lt hknext
    simpa [List.getElem_append, hk, hknext, hmod] using hrelFull
  · have hkLast : k + 1 = l.length := by omega
    have hmod : (k + 1) % l.length = 0 := by
      rw [hkLast, Nat.mod_self]
    simpa [List.getElem_append, hk, hkLast, hmod] using hrelFull

/--
Every positive closed walk in an irreflexive relation contains a simple directed
cycle represented as a nodup list whose `formPerm` edges follow the relation.
-/
theorem exists_simple_cycle_list_of_stepCycle
    {α : Type*} [DecidableEq α] {r : α → α → Prop}
    (hirr : ∀ a : α, ¬ r a a)
    (hcycle : ∃ i n, 0 < n ∧ Relation.RelatesInSteps r i i n) :
    ∃ cycle : List α,
      cycle.Nodup ∧ 2 ≤ cycle.length ∧
        ∀ i, i ∈ cycle → r i (cycle.formPerm i) := by
  classical
  let P : ℕ → Prop := fun n => ∃ i : α, 0 < n ∧ Relation.RelatesInSteps r i i n
  have hP : ∃ n, P n := by
    obtain ⟨i, n, hn, hsteps⟩ := hcycle
    exact ⟨n, i, hn, hsteps⟩
  let n := Nat.find hP
  have hnP : P n := Nat.find_spec hP
  obtain ⟨a, hnpos, hsteps⟩ := hnP
  obtain ⟨walk, hwalk_len, hhead, hlast, hchain⟩ :=
    exists_chain_list_of_relatesInSteps (r := r) hsteps
  let cycle : List α := walk.dropLast
  have hcycle_len : cycle.length = n := by
    simp [cycle, List.length_dropLast, hwalk_len]
  have hcycle_pos : 0 < cycle.length := by omega
  have hwalk_nonempty : walk ≠ [] := by
    intro hnil
    simp [hnil] at hwalk_len
  have hcycle_head : cycle[0] = a := by
    have hhead_get : walk.head hwalk_nonempty = a :=
      (List.head_eq_iff_head?_eq_some hwalk_nonempty).2 hhead
    have hwalk0 : walk[0]'(by omega) = a := by
      simpa [List.head_eq_getElem_zero hwalk_nonempty] using hhead_get
    simpa [cycle, List.getElem_dropLast] using hwalk0
  have hwalk_last : walk.getLast hwalk_nonempty = a := by
    have hlast' : some (walk.getLast hwalk_nonempty) = some a := by
      simpa [List.getLast?_eq_getLast_of_ne_nil hwalk_nonempty] using hlast
    exact Option.some.inj hlast'
  have hclosed_chain : (cycle ++ [cycle[0]]).IsChain r := by
    have hdrop : cycle ++ [cycle[0]] = walk := by
      simpa [cycle, hcycle_head, hwalk_last] using
        (List.dropLast_append_getLast hwalk_nonempty :
          walk.dropLast ++ [walk.getLast hwalk_nonempty] = walk)
    simpa [hdrop] using hchain
  have hnodup : cycle.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro p q hpq
    apply Fin.ext
    by_contra hvalne
    have shorter_contra {p q : Fin cycle.length} (hlt : p.1 < q.1)
        (hpq : cycle[p] = cycle[q]) : False := by
      have hpw : p.1 < walk.length := by omega
      have hqw : q.1 < walk.length := by omega
      have heqwalk : walk[p.1]'hpw = walk[q.1]'hqw := by
        simpa [cycle, List.getElem_dropLast] using hpq
      have hsubsteps :=
        isChain_relatesInSteps_getElem (r := r) hchain hpw hqw (le_of_lt hlt)
      have hclosed :
          Relation.RelatesInSteps r (walk[p.1]'hpw) (walk[p.1]'hpw) (q.1 - p.1) := by
        simpa [heqwalk] using hsubsteps
      have hshortP : P (q.1 - p.1) :=
        ⟨walk[p.1]'hpw, Nat.sub_pos_of_lt hlt, hclosed⟩
      have hminle : n ≤ q.1 - p.1 := Nat.find_min' hP hshortP
      have hshort : q.1 - p.1 < n := by omega
      omega
    rcases Nat.lt_or_gt_of_ne hvalne with hp_lt_q | hq_lt_p
    · exact (shorter_contra hp_lt_q hpq).elim
    · exact (shorter_contra hq_lt_p hpq.symm).elim
  have hn_ne_one : n ≠ 1 := by
    intro hn1
    have hsteps1 : Relation.RelatesInSteps r a a (0 + 1) := by
      simpa [hn1] using hsteps
    obtain ⟨t, ht_edge, ht_zero⟩ := Relation.RelatesInSteps.succ' hsteps1
    have hta : t = a := Relation.RelatesInSteps.zero ht_zero
    subst t
    exact hirr a ht_edge
  have hlen_two : 2 ≤ cycle.length := by omega
  exact ⟨cycle, hnodup, hlen_two,
    edge_formPerm_of_closed_nodup_chain (r := r) hnodup hcycle_pos hclosed_chain⟩

end Graph
end EconCSLean
