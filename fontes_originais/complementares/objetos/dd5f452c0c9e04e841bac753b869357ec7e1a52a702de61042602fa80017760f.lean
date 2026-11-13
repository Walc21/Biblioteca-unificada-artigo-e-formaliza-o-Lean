module
public import RequestProject.Lib.Assembly
@[expose] public section

/-!
# Section 4.1: exact equivalence with rational ReLU networks

Theorem 4.3 (assembly–rational ReLU equivalence) and Proposition 4.4 (parameters and height).
-/

open Finset

namespace Dyadic.Lib

section Forward

variable {N : ℕ} {a : ℕ → Atom}

lemma left_mono_of_consecutive
    (hcons : ∀ j, j + 1 < N → (a j).right = (a (j + 1)).left) :
    ∀ i j, i ≤ j → j < N → ((a i).left : ℝ) ≤ (a j).left := by
  intro i j hij hj
  induction j with
  | zero => obtain rfl : i = 0 := by omega
            exact le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · have h1 := ih (by omega) (by omega)
      have h2 : ((a j).left : ℝ) < (a j).right := by exact_mod_cast (a j).left_lt_right
      have h3 : ((a j).right : ℝ) = (a (j + 1)).left := by exact_mod_cast hcons j hj
      linarith
    · obtain rfl : i = j + 1 := by omega
      exact le_refl _

/-- The partial affine sums of eq. (24) reproduce each leaf line. -/
lemma line_eq_partial_sum
    (hcons : ∀ j, j + 1 < N → (a j).right = (a (j + 1)).left)
    (hmatch : ∀ j, j + 1 < N → (a j).line (a j).right = (a (j + 1)).line (a (j + 1)).left) :
    ∀ j < N, ∀ x : ℝ, (a j).line x = (a 0).line (a 0).left + (a 0).s * (x - (a 0).left) +
      ∑ i ∈ Finset.Ico 1 (j + 1), (((a i).s - (a (i - 1)).s : ℚ) : ℝ) * (x - (a i).left) := by
  intro j hj x
  induction j with
  | zero =>
    simp only [zero_add, Finset.Ico_self, Finset.sum_empty, add_zero]
    simp only [Atom.line]; ring
  | succ j ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    have h1 := hmatch j hj
    have h2 : ((a j).right : ℝ) = (a (j + 1)).left := by exact_mod_cast hcons j hj
    simp only [Nat.add_sub_cancel]
    rw [h2] at h1
    have e1 : (a (j + 1)).line x = (a (j + 1)).line (a (j + 1)).left +
        (a (j + 1)).s * (x - (a (j + 1)).left) := by simp only [Atom.line]; ring
    have e2 : (a j).line (a (j + 1)).left = (a j).line x - (a j).s * (x - (a (j + 1)).left) := by
      simp only [Atom.line]; ring
    rw [e1, ← h1, e2, ih (by omega)]; push_cast; ring

lemma relu_sum_on_cell
    (hcons : ∀ j, j + 1 < N → (a j).right = (a (j + 1)).left) :
    ∀ j < N, ∀ x ∈ (a j).cell,
      ∑ i ∈ Finset.Ico 1 N, (((a i).s - (a (i - 1)).s : ℚ) : ℝ) * relu (x - (a i).left) =
      ∑ i ∈ Finset.Ico 1 (j + 1), (((a i).s - (a (i - 1)).s : ℚ) : ℝ) * (x - (a i).left) := by
  intro j hj x hx
  have hmono := left_mono_of_consecutive hcons
  rcases Nat.lt_or_ge (j + 1) 1 with h0 | h0
  · omega
  rw [← Finset.sum_Ico_consecutive _ h0 (show j + 1 ≤ N by omega)]
  have hz : ∑ i ∈ Finset.Ico (j + 1) N, (((a i).s - (a (i - 1)).s : ℚ) : ℝ) *
      relu (x - (a i).left) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_Ico] at hi
    have h1 := hmono (j + 1) i hi.1 hi.2
    have h2 : ((a j).right : ℝ) = (a (j + 1)).left := by exact_mod_cast hcons j (by omega)
    have h3 : x ≤ (a j).right := hx.2
    simp only [relu, max_eq_left (show x - (a i).left ≤ 0 by linarith), mul_zero]
  rw [hz, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_Ico] at hi
  have h1 := hmono i j (by omega) hj
  have h3 : ((a j).left : ℝ) ≤ x := hx.1
  simp only [relu, max_eq_right (show 0 ≤ x - (a i).left by linarith)]

/-- **Theorem 4.3** (assembly → ReLU). Let an assembly be given on `K` by `N` consecutive leaves
`a 0, …, a (N-1)` (consecutive cells, coinciding values at the shared nodes, `g` equal to the
leaf line on each `J ∩ K`, and `K` contained in the union of the leaves).  With nodes
`t_j = left(a j)` and slopes `s_j`, on `K`
`g(x) = ℓ₀(t₀) + s₀(x - t₀) + ∑_{j=1}^{N-1} (s_j - s_{j-1}) ρ(x - t_j)`  (eq. (24)).
After expansion the affine part is `intercept₀ + s₀ x` with rational coefficients, the internal
breakpoints `t_j` are dyadic, and the formula is a shallow ReLU network with `N-1` hinge units. -/
theorem assembly_eq_relu (K : Set ℝ) (g : ℝ → ℝ) (hN : 1 ≤ N)
    (hcons : ∀ j, j + 1 < N → (a j).right = (a (j + 1)).left)
    (hmatch : ∀ j, j + 1 < N → (a j).line (a j).right = (a (j + 1)).line (a (j + 1)).left)
    (hg : ∀ j < N, ∀ x ∈ (a j).cell ∩ K, g x = (a j).line x)
    (hK : K ⊆ Set.Icc ((a 0).left : ℝ) ((a (N - 1)).right)) :
    ∀ x ∈ K, g x = (a 0).line (a 0).left + (a 0).s * (x - (a 0).left) +
      ∑ j ∈ Finset.Ico 1 N, (((a j).s - (a (j - 1)).s : ℚ) : ℝ) * relu (x - (a j).left) := by
  intro x hx
  have hxI := hK hx
  classical
  let j := Nat.findGreatest (fun i => ((a i).left : ℝ) ≤ x) (N - 1)
  have hjN : j ≤ N - 1 := Nat.findGreatest_le _
  have hjx : ((a j).left : ℝ) ≤ x := by
    have := Nat.findGreatest_spec (P := fun i => ((a i).left : ℝ) ≤ x) (m := 0) (n := N - 1)
      (Nat.zero_le _) hxI.1
    exact this
  have hxr : x ≤ (a j).right := by
    rcases Nat.lt_or_ge j (N - 1) with h | h
    · have := Nat.findGreatest_is_greatest (P := fun i => ((a i).left : ℝ) ≤ x) (n := N - 1)
        (k := j + 1) (by omega) (by omega)
      have h2 : ((a j).right : ℝ) = (a (j + 1)).left := by exact_mod_cast hcons j (by omega)
      simp only [not_le] at this
      linarith
    · have : j = N - 1 := by omega
      rw [this]; exact hxI.2
  have hcell : x ∈ (a j).cell := ⟨hjx, hxr⟩
  rw [hg j (by omega) x ⟨hcell, hx⟩, relu_sum_on_cell hcons j (by omega) x hcell,
    line_eq_partial_sum hcons hmatch j (by omega) x]

/-- Expanded form of the affine part of eq. (24): `ℓ₀(t₀) + s₀(x - t₀) = c + s₀ x` with the rational
intercept `c = y₀ - s₀ x₀`. -/
lemma affine_part_expand (b : Atom) (x : ℝ) :
    b.line b.left + b.s * (x - b.left) = (b.intercept : ℝ) + b.s * x := by
  rw [Atom.line_eq]; ring

end Forward

section Converse

/-- Rational evaluation of a normalized ReLU network (eq. (25)). -/
def reluNetQ (c q : ℚ) (M : ℕ) (w τ : ℕ → ℚ) (x : ℚ) : ℚ :=
  c + q * x + ∑ j ∈ Finset.range M, w j * max 0 (x - τ j)

/-- Real evaluation of a normalized ReLU network (eq. (25)). -/
def reluNet (c q : ℚ) (M : ℕ) (w τ : ℕ → ℚ) (x : ℝ) : ℝ :=
  c + q * x + ∑ j ∈ Finset.range M, (w j : ℝ) * relu (x - τ j)

lemma reluNet_cast (c q : ℚ) (M : ℕ) (w τ : ℕ → ℚ) (x : ℚ) :
    reluNet c q M w τ x = reluNetQ c q M w τ x := by
  simp [reluNet, reluNetQ, relu, Rat.cast_max]

lemma reluNet_continuous (c q : ℚ) (M : ℕ) (w τ : ℕ → ℚ) : Continuous (reluNet c q M w τ) := by
  unfold reluNet relu
  fun_prop

/-- On a mesh cell all of whose breakpoints lie outside its interior, the network is affine. -/
lemma reluNet_affine_on_cell (c q : ℚ) (M : ℕ) (w τ : ℕ → ℚ) (L h : ℚ) (hh : 0 < h)
    (hτ : ∀ j < M, τ j ≤ L ∨ L + h ≤ τ j) (x : ℝ) (hx : x ∈ Set.Icc (L : ℝ) (L + h)) (z : ℝ)
    (hz : z ∈ Set.Icc (L : ℝ) (L + h)) :
    reluNet c q M w τ x = reluNet c q M w τ z +
      ((q + ∑ j ∈ (Finset.range M).filter (fun j => τ j ≤ L), w j : ℚ) : ℝ) * (x - z) := by
  have key : ∀ y ∈ Set.Icc (L : ℝ) (L + h), reluNet c q M w τ y =
      c + q * y + ∑ j ∈ (Finset.range M).filter (fun j => τ j ≤ L), (w j : ℝ) * (y - τ j) := by
    intro y hy
    unfold reluNet
    rw [Finset.sum_filter]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rcases hτ j (Finset.mem_range.1 hj) with h1 | h1
    · rw [if_pos h1]
      have : ((τ j : ℚ) : ℝ) ≤ L := by exact_mod_cast h1
      simp only [relu, max_eq_right (show 0 ≤ y - τ j by linarith [hy.1])]
    · have h2 : ¬ τ j ≤ L := by
        intro h3; have : h ≤ 0 := by linarith
        linarith
      rw [if_neg h2]
      have : ((L : ℚ) : ℝ) + h ≤ τ j := by exact_mod_cast h1
      simp only [relu, max_eq_left (show y - τ j ≤ 0 by linarith [hy.2]), mul_zero]
  rw [key x hx, key z hz]
  push_cast
  have : ∑ j ∈ (Finset.range M).filter (fun j => τ j ≤ L), (w j : ℝ) * (x - τ j) =
      ∑ j ∈ (Finset.range M).filter (fun j => τ j ≤ L), (w j : ℝ) * (z - τ j) +
      ∑ j ∈ (Finset.range M).filter (fun j => τ j ≤ L), (w j : ℝ) * (x - z) := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; ring
  rw [this, _root_.add_mul, Finset.sum_mul]; ring

/-- **Theorem 4.3** (ReLU → assembly). Let `R(x) = c + q x + ∑_{j<M} w_j ρ(x - τ_j)` with
rational `c, q, w_j` and dyadic `τ_j`, and `K = [α, β]`.  If every local slope
`q + ∑_{τ_j < x} w_j` (eq. (26)) at points `x ∈ K` different from the breakpoints is nonzero,
then `R|_K ∈ 𝒜(K)`; the assembly is given by a uniform dyadic mesh refining all `τ_j`. -/
theorem relu_mem_Asm (α β : ℝ) (hαβ : α < β) (c q : ℚ) (M : ℕ) (w τ : ℕ → ℚ)
    (hτ : ∀ j < M, ∃ (u : ℤ) (e : ℕ), τ j = u / 2 ^ e)
    (hslope : ∀ x ∈ Set.Icc α β, (∀ j < M, x ≠ τ j) →
      q + ∑ j ∈ (Finset.range M).filter (fun j => (τ j : ℝ) < x), w j ≠ 0) :
    reluNet c q M w τ ∈ Asm (Set.Icc α β) := by
  classical
  choose! u e hue using hτ
  set k := (Finset.range M).sup e with hk
  have hτk : ∀ j < M, ∃ v : ℤ, τ j = v / 2 ^ k := by
    intro j hj
    have hej : e j ≤ k := Finset.le_sup (f := e) (Finset.mem_range.2 hj)
    refine ⟨u j * 2 ^ (k - e j), ?_⟩
    rw [hue j hj]
    have : (2 : ℚ) ^ k = 2 ^ (k - e j) * 2 ^ e j := by rw [← pow_add]; congr 1; omega
    rw [this]; push_cast; field_simp
  set h : ℚ := 1 / 2 ^ k with hh
  have hhpos : 0 < h := by positivity
  let L : ℤ → ℚ := fun m => m / 2 ^ k
  let slope : ℤ → ℚ := fun m => q + ∑ j ∈ (Finset.range M).filter (fun j => τ j ≤ L m), w j
  let atomOf : ℤ → Atom := fun m =>
    if hs : slope m ≠ 0 then ⟨k, m, reluNetQ c q M w τ ((2 * m + 1) / 2 ^ (k + 1)), slope m, hs⟩
    else ⟨k, m, 0, 1, one_ne_zero⟩
  have hk_atom : ∀ m, (atomOf m).k = k := by intro m; simp only [atomOf]; split_ifs <;> rfl
  have hm_atom : ∀ m, (atomOf m).m = m := by intro m; simp only [atomOf]; split_ifs <;> rfl
  have hLeft : ∀ m, (atomOf m).left = L m := by
    intro m; simp only [Atom.left, hk_atom, hm_atom, L]
  have hRight : ∀ m, (atomOf m).right = L m + h := by
    intro m; simp only [Atom.right, hk_atom, hm_atom, L, hh]; ring
  have hcell : ∀ m, (atomOf m).cell = Set.Icc ((L m : ℚ) : ℝ) ((L m + h : ℚ) : ℝ) := by
    intro m; simp only [Atom.cell, hLeft, hRight]
  have hmesh : ∀ m, ∀ j < M, τ j ≤ L m ∨ L m + h ≤ τ j := by
    intro m j hj
    obtain ⟨v, hv⟩ := hτk j hj
    rcases le_or_gt v m with h1 | h1
    · left; rw [hv]; simp only [L]; gcongr; (try exact_mod_cast h1)
    · right; rw [hv]; simp only [L, hh]
      rw [← add_div]
      gcongr
      have : (m : ℚ) + 1 ≤ v := by exact_mod_cast h1
      exact this
  set lo : ℤ := ⌊α * 2 ^ k⌋
  set hi : ℤ := ⌈β * 2 ^ k⌉
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hLreal : ∀ m : ℤ, ((L m : ℚ) : ℝ) = m / 2 ^ k := by intro m; simp [L]
  have hhreal : ((h : ℚ) : ℝ) = 1 / 2 ^ k := by simp [hh]
  have hslope_ne : ∀ m ∈ Finset.Ico lo hi, slope m ≠ 0 := by
    intro m hm
    simp only [Finset.mem_Ico] at hm
    have hm1 : (m : ℝ) < β * 2 ^ k := by
      have := hm.2; rw [Int.lt_ceil] at this; exact this
    have hm2 : α * 2 ^ k < (m : ℝ) + 1 := by
      have h3 := Int.lt_floor_add_one (α * 2 ^ k)
      have : ((lo : ℤ) : ℝ) ≤ m := by exact_mod_cast hm.1
      linarith
    set A := max ((L m : ℚ) : ℝ) α
    set B := min ((L m + h : ℚ) : ℝ) β
    have hLB : ((L m : ℚ) : ℝ) < ((L m + h : ℚ) : ℝ) := by
      exact_mod_cast (by linarith : L m < L m + h)
    have hAB : A < B := by
      simp only [A, B, max_lt_iff, lt_min_iff]
      refine ⟨⟨hLB, ?_⟩, ?_, hαβ⟩
      · push_cast; rw [hLreal, hhreal, ← add_div, lt_div_iff₀ h2k]; exact hm2
      · rw [hLreal, div_lt_iff₀ h2k]; exact hm1
    set x := (A + B) / 2
    have hxA : A < x := by simp only [x]; linarith
    have hxB : x < B := by simp only [x]; linarith
    have hxK : x ∈ Set.Icc α β := ⟨by linarith [le_max_right ((L m : ℚ) : ℝ) α],
      by linarith [min_le_right ((L m + h : ℚ) : ℝ) β]⟩
    have hxL : ((L m : ℚ) : ℝ) < x := by linarith [le_max_left ((L m : ℚ) : ℝ) α]
    have hxR : x < ((L m + h : ℚ) : ℝ) := by linarith [min_le_left ((L m + h : ℚ) : ℝ) β]
    have hne : ∀ j < M, x ≠ τ j := by
      intro j hj heq
      rcases hmesh m j hj with h1 | h1
      · have : ((τ j : ℚ) : ℝ) ≤ L m := by exact_mod_cast h1
        linarith
      · have : ((L m + h : ℚ) : ℝ) ≤ τ j := by exact_mod_cast h1
        linarith
    have := hslope x hxK hne
    convert this using 3
    apply Finset.filter_congr
    intro j hj
    rcases hmesh m j (Finset.mem_range.1 hj) with h1 | h1
    · have : ((τ j : ℚ) : ℝ) ≤ L m := by exact_mod_cast h1
      simp only [h1, true_iff]; linarith
    · have h2 : ((L m + h : ℚ) : ℝ) ≤ τ j := by exact_mod_cast h1
      have h3 : ¬ τ j ≤ L m := by
        intro h4
        have : ((τ j : ℚ) : ℝ) ≤ L m := by exact_mod_cast h4
        linarith
      simp only [h3, false_iff, not_lt]; linarith
  have hline : ∀ m ∈ Finset.Ico lo hi, ∀ x ∈ (atomOf m).cell,
      reluNet c q M w τ x = (atomOf m).line x := by
    intro m hm x hx
    have hs := hslope_ne m hm
    have hcenter : (((2 * m + 1) / 2 ^ (k + 1) : ℚ) : ℝ) ∈
        Set.Icc ((L m : ℚ) : ℝ) (((L m : ℚ) : ℝ) + ((h : ℚ) : ℝ)) := by
      constructor
      · push_cast; rw [hLreal, pow_succ, div_le_div_iff₀ h2k (by positivity)]; nlinarith
      · push_cast; rw [hLreal, hhreal, ← add_div, pow_succ,
          div_le_div_iff₀ (by positivity) h2k]; nlinarith
    rw [hcell] at hx
    push_cast at hx
    rw [reluNet_affine_on_cell c q M w τ (L m) h hhpos (hmesh m) x hx _ hcenter, reluNet_cast]
    simp only [atomOf, dif_pos hs, Atom.line, Atom.center, slope]
  have hmem : ∀ b ∈ (Finset.Ico lo hi).image atomOf, ∃ m ∈ Finset.Ico lo hi, b = atomOf m := by
    intro b hb
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hb
    exact ⟨m, hm, rfl⟩
  refine ⟨(reluNet_continuous c q M w τ).continuousOn, (Finset.Ico lo hi).image atomOf,
    ?_, ?_, ?_, ?_⟩
  · intro b hb b' hb' hne
    obtain ⟨m, hm, rfl⟩ := hmem b hb
    obtain ⟨m', hm', rfl⟩ := hmem b' hb'
    have hmm : m ≠ m' := fun h => hne (by rw [h])
    rw [hcell, hcell, interior_Icc, interior_Icc]
    rw [Set.disjoint_iff]
    rintro x ⟨⟨h1, h2⟩, h3, h4⟩
    push_cast at h1 h2 h3 h4
    simp only [hLreal, hhreal] at h1 h2 h3 h4
    rw [← add_div] at h2 h4
    rw [div_lt_iff₀ h2k] at h1 h3
    rw [lt_div_iff₀ h2k] at h2 h4
    rcases lt_or_gt_of_ne hmm with h5 | h5
    · have : (m : ℝ) + 1 ≤ m' := by exact_mod_cast h5
      linarith
    · have : (m' : ℝ) + 1 ≤ m := by exact_mod_cast h5
      linarith
  · intro x hx
    simp only [Set.mem_iUnion]
    have hx2k : α * 2 ^ k ≤ x * 2 ^ k := by nlinarith [hx.1]
    have hx2k' : x * 2 ^ k ≤ β * 2 ^ k := by nlinarith [hx.2]
    by_cases hcase : ⌊x * 2 ^ k⌋ < hi
    · refine ⟨atomOf ⌊x * 2 ^ k⌋, Finset.mem_image_of_mem _ (Finset.mem_Ico.2
        ⟨Int.floor_mono hx2k, hcase⟩), ?_⟩
      rw [hcell]
      constructor
      · rw [hLreal, div_le_iff₀ h2k]; exact Int.floor_le _
      · push_cast; rw [hLreal, hhreal, ← add_div, le_div_iff₀ h2k]
        exact (Int.lt_floor_add_one _).le
    · push_neg at hcase
      have e1 : (hi : ℝ) ≤ x * 2 ^ k := by
        have := Int.floor_le (x * 2 ^ k)
        have : (hi : ℝ) ≤ ⌊x * 2 ^ k⌋ := by exact_mod_cast hcase
        linarith
      have e2 : β * 2 ^ k ≤ hi := Int.le_ceil _
      have e3 : x * 2 ^ k = hi := by linarith
      have e4 : α * 2 ^ k < x * 2 ^ k := by
        have : α < x := by
          have : β * 2 ^ k ≤ x * 2 ^ k := by linarith
          have : β ≤ x := le_of_mul_le_mul_right this h2k
          linarith
        nlinarith
      refine ⟨atomOf (hi - 1), Finset.mem_image_of_mem _ (Finset.mem_Ico.2 ⟨?_, by omega⟩), ?_⟩
      · have : (lo : ℝ) < hi := by
          have := Int.floor_le (α * 2 ^ k); linarith
        have : lo < hi := by exact_mod_cast this
        omega
      · rw [hcell]
        constructor
        · rw [hLreal, div_le_iff₀ h2k]; push_cast; linarith
        · push_cast; rw [hLreal, hhreal, ← add_div, le_div_iff₀ h2k]; push_cast; linarith
  · intro b hb x hx
    obtain ⟨m, hm, rfl⟩ := hmem b hb
    exact hline m hm x hx.1
  · intro b hb b' hb' x hx
    obtain ⟨m, hm, rfl⟩ := hmem b hb
    obtain ⟨m', hm', rfl⟩ := hmem b' hb'
    rw [← hline m hm x hx.1, ← hline m' hm' x hx.2]

end Converse

/-! ### Proposition 4.4 -/

/-- **Proposition 4.4** (parameters and height). The normalized ReLU conversion of an assembly
with `N` leaves `a 0, …, a (N-1)` stores `2N` rationals: the initial intercept and slope, and a
node `t_j` and a slope jump `s_j - s_{j-1}` for each of the `N-1` units.  If all atoms have height
`≤ H` (`H ≥ 2`), every parameter has height `≤ 2^{H+1} H²` (eq. (27)). -/
theorem relu_parameters_height {N H : ℕ} (hN : 1 ≤ N) (a : ℕ → Atom)
    (ha : ∀ j < N, (a j).height ≤ H) :
    (2 + 2 * (N - 1) = 2 * N) ∧
    ratHeight (a 0).intercept ≤ 2 ^ (H + 1) * H ^ 2 ∧
    ratHeight (a 0).s ≤ 2 ^ (H + 1) * H ^ 2 ∧
    ∀ j ∈ Finset.Ico 1 N, ratHeight (a j).left ≤ 2 ^ (H + 1) * H ^ 2 ∧
      ratHeight ((a j).s - (a (j - 1)).s) ≤ 2 ^ (H + 1) * H ^ 2 := by
  have h0 := ha 0 hN
  have hH2 : 2 ≤ H := (a 0).two_le_height.trans h0
  have hH1 : 1 ≤ H ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hpow : H ≤ 2 ^ (H + 1) := (Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine ⟨by omega, (height_calculus (a 0) (a 0) h0 h0).2.2.2, ?_, fun j hj => ?_⟩
  · have := (Atom.height_le_iff _).1 h0
    calc ratHeight (a 0).s ≤ H := this.2.2.2.2
      _ ≤ 2 ^ (H + 1) := hpow
      _ ≤ 2 ^ (H + 1) * H ^ 2 := Nat.le_mul_of_pos_right _ (by omega)
  · simp only [Finset.mem_Ico] at hj
    have hj' := ha j hj.2
    have hj1 := ha (j - 1) (by omega)
    obtain ⟨-, h60, -, -⟩ := height_calculus (a (j - 1)) (a j) hj1 hj'
    constructor
    · calc ratHeight (a j).left ≤ 2 ^ H := (a j).ratHeight_left_le hj'
        _ ≤ 2 ^ (H + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ 2 ^ (H + 1) * H ^ 2 := Nat.le_mul_of_pos_right _ (by omega)
    · calc ratHeight ((a j).s - (a (j - 1)).s) ≤ 2 * H ^ 2 := h60
        _ ≤ 2 ^ (H + 1) * H ^ 2 := Nat.mul_le_mul_right _ (by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (H + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))

end Dyadic.Lib
