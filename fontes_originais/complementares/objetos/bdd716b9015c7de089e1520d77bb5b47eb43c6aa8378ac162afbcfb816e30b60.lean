module
public import RequestProject.Sec4.ReLU
@[expose] public section

/-!
# Chains of consecutive atoms are assemblies

If `a 0, …, a (N-1)` are atoms with consecutive cells (`right(a j) = left(a (j+1))`) whose lines
agree at the shared nodes, the continuous function given by the ReLU formula (24) is an assembly
on `[left(a 0), right(a (N-1))]` represented by exactly these `N` leaves.
-/

open Finset

namespace Dyadic.Lib

/-- The function of a chain of atoms, written in the ReLU form (24). -/
noncomputable def chainFun (a : ℕ → Atom) (N : ℕ) (x : ℝ) : ℝ :=
  (a 0).line (a 0).left + (a 0).s * (x - (a 0).left) +
    ∑ j ∈ Finset.Ico 1 N, (((a j).s - (a (j - 1)).s : ℚ) : ℝ) * relu (x - (a j).left)

lemma chainFun_continuous (a : ℕ → Atom) (N : ℕ) : Continuous (chainFun a N) := by
  unfold chainFun relu; fun_prop

section

variable {a : ℕ → Atom} {N : ℕ}

lemma chainFun_eq_line
    (hcons : ∀ j, j + 1 < N → (a j).right = (a (j + 1)).left)
    (hmatch : ∀ j, j + 1 < N → (a j).line (a j).right = (a (j + 1)).line (a (j + 1)).left) :
    ∀ j < N, ∀ x ∈ (a j).cell, chainFun a N x = (a j).line x := by
  intro j hj x hx
  unfold chainFun
  rw [relu_sum_on_cell hcons j hj x hx, line_eq_partial_sum hcons hmatch j hj x]

lemma right_le_left_of_lt (hcons : ∀ j, j + 1 < N → (a j).right = (a (j + 1)).left)
    {i j : ℕ} (hij : i < j) (hj : j < N) : ((a i).right : ℝ) ≤ (a j).left := by
  have h1 : ((a i).right : ℝ) = (a (i + 1)).left := by exact_mod_cast hcons i (by omega)
  rw [h1]; exact left_mono_of_consecutive hcons (i + 1) j hij hj

lemma left_lt_left_of_lt (hcons : ∀ j, j + 1 < N → (a j).right = (a (j + 1)).left)
    {i j : ℕ} (hij : i < j) (hj : j < N) : ((a i).left : ℝ) < (a j).left := by
  have := right_le_left_of_lt hcons hij hj
  have h2 : ((a i).left : ℝ) < (a i).right := by exact_mod_cast (a i).left_lt_right
  linarith

lemma chain_injOn (hcons : ∀ j, j + 1 < N → (a j).right = (a (j + 1)).left) :
    Set.InjOn a (Finset.range N : Set ℕ) := by
  intro i hi j hj h
  simp only [coe_range, Set.mem_Iio] at hi hj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h' | h'
  · have := left_lt_left_of_lt hcons h' hj; rw [h] at this; exact lt_irrefl _ this
  · have := left_lt_left_of_lt hcons h' hi; rw [h] at this; exact lt_irrefl _ this

lemma chain_card (hcons : ∀ j, j + 1 < N → (a j).right = (a (j + 1)).left) :
    ((Finset.range N).image a).card = N := by
  rw [card_image_of_injOn (chain_injOn hcons), card_range]

lemma chain_cover (hN : 1 ≤ N) (hcons : ∀ j, j + 1 < N → (a j).right = (a (j + 1)).left)
    {x : ℝ} (hx : x ∈ Set.Icc ((a 0).left : ℝ) (a (N - 1)).right) :
    ∃ j < N, x ∈ (a j).cell := by
  classical
  let j := Nat.findGreatest (fun i => ((a i).left : ℝ) ≤ x) (N - 1)
  have hjN : j ≤ N - 1 := Nat.findGreatest_le _
  have hjx : ((a j).left : ℝ) ≤ x :=
    Nat.findGreatest_spec (P := fun i => ((a i).left : ℝ) ≤ x) (m := 0) (n := N - 1)
      (Nat.zero_le _) hx.1
  have hxr : x ≤ (a j).right := by
    rcases Nat.lt_or_ge j (N - 1) with h | h
    · have := Nat.findGreatest_is_greatest (P := fun i => ((a i).left : ℝ) ≤ x) (n := N - 1)
        (k := j + 1) (by omega) (by omega)
      have h2 : ((a j).right : ℝ) = (a (j + 1)).left := by exact_mod_cast hcons j (by omega)
      simp only [not_le] at this
      linarith
    · have : j = N - 1 := by omega
      rw [this]; exact hx.2
  exact ⟨j, by omega, hjx, hxr⟩

/-- **Chains are assemblies.** A chain of `N ≥ 1` consecutive atoms whose lines agree at the shared
nodes defines (through the ReLU formula) a continuous assembly on
`K = [left(a 0), right(a (N-1))]`, represented by exactly the `N` leaves `a 0, …, a (N-1)`. -/
theorem chain_isAssemblyRep (hN : 1 ≤ N)
    (hcons : ∀ j, j + 1 < N → (a j).right = (a (j + 1)).left)
    (hmatch : ∀ j, j + 1 < N → (a j).line (a j).right = (a (j + 1)).line (a (j + 1)).left) :
    IsAssemblyRep (Set.Icc ((a 0).left : ℝ) (a (N - 1)).right) (chainFun a N)
      ((Finset.range N).image a) := by
  have hline := chainFun_eq_line hcons hmatch
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb b' hb' hne
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hb
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hb'
    rw [mem_range] at hi hj
    have hij : i ≠ j := fun h => hne (by rw [h])
    simp only [Atom.cell, interior_Icc]
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · have := right_le_left_of_lt hcons h hj
      exact Set.disjoint_left.2 fun x hx hx' => by linarith [hx.2, hx'.1]
    · have := right_le_left_of_lt hcons h hi
      exact Set.disjoint_left.2 fun x hx hx' => by linarith [hx.1, hx'.2]
  · intro x hx
    obtain ⟨j, hj, hxj⟩ := chain_cover hN hcons hx
    exact Set.mem_iUnion₂.2 ⟨a j, mem_image.2 ⟨j, mem_range.2 hj, rfl⟩, hxj⟩
  · intro b hb x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hb
    exact hline i (mem_range.1 hi) x hx.1
  · intro b hb b' hb' x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hb
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hb'
    rw [← hline i (mem_range.1 hi) x hx.1, ← hline j (mem_range.1 hj) x hx.2]

theorem chain_mem_Asm (hN : 1 ≤ N)
    (hcons : ∀ j, j + 1 < N → (a j).right = (a (j + 1)).left)
    (hmatch : ∀ j, j + 1 < N → (a j).line (a j).right = (a (j + 1)).line (a (j + 1)).left) :
    chainFun a N ∈ Asm (Set.Icc ((a 0).left : ℝ) (a (N - 1)).right) :=
  ⟨(chainFun_continuous a N).continuousOn, _, chain_isAssemblyRep hN hcons hmatch⟩

end

end Dyadic.Lib
