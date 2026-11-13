module

public import Unified.Fase2.DyadicCells

/-!
# Section 4 (up to Equation (23)): continuous assemblies and their density

Formalization of Definition 4.1 (continuous assembly), Theorem 4.2 (density of assemblies)
and Equation (23) (number of cells of the uniform cover).
-/

@[expose] public section

namespace Dyadic2

open Set Function

/-- **Definition 4.1 (continuous assembly).** For `K = [α, β]`, `𝒜(K)` is the set of
`g ∈ C(K)` for which there is a finite collection `Λ` of dyadic cells `J_{k,m}` (indexed by
`(k, m)`) with pairwise disjoint interiors whose union contains `K`, and addresses `n(J)`,
`J ∈ Λ`, such that the atom of address `n(J)` lives on `J` and `g = ℓ_{n(J)}` on `J ∩ K`.
(Agreement on shared boundaries is automatic since `g` is a function.) -/
def Asm (α β : ℝ) : Set C(Icc α β, ℝ) :=
  {g | ∃ (Λ : Finset (ℕ × ℤ)) (addr : ℕ × ℤ → ℕ),
      (∀ J ∈ Λ, ∀ J' ∈ Λ, J ≠ J' →
        Disjoint (interior (cellJ J.1 J.2)) (interior (cellJ J'.1 J'.2))) ∧
      Icc α β ⊆ ⋃ J ∈ Λ, cellJ J.1 J.2 ∧
      ∀ J ∈ Λ, scale (addr J) = J.1 ∧ cellIdx (addr J) = J.2 ∧
        ∀ x : Icc α β, (x : ℝ) ∈ cellJ J.1 J.2 → g x = line (addr J) x}

/-! ### Auxiliary constructions for the proof of Theorem 4.2 -/

/-- The hat function `max(0, 1 - |y|)`. -/
noncomputable def hat (y : ℝ) : ℝ := max 0 (1 - |y|)

/-- The linear interpolant of nodal values `v` on the nodes `j 2^{-k}`, `A ≤ j ≤ B + 1`,
written as a finite sum of hat functions. -/
noncomputable def interp (k : ℕ) (v : ℤ → ℝ) (A B : ℤ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc A (B + 1), v i * hat (2 ^ k * x - i)

lemma interp_continuous (k : ℕ) (v : ℤ → ℝ) (A B : ℤ) : Continuous (interp k v A B) := by
  unfold interp hat
  fun_prop

lemma interp_eq (k : ℕ) (v : ℤ → ℝ) (A B j : ℤ) (hA : A ≤ j) (hB : j ≤ B) (x : ℝ)
    (h1 : (j : ℝ) ≤ 2 ^ k * x) (h2 : 2 ^ k * x ≤ j + 1) :
    interp k v A B x = v j * (j + 1 - 2 ^ k * x) + v (j + 1) * (2 ^ k * x - j) := by
  unfold interp
  rw [Finset.sum_eq_add j (j + 1) (by omega)]
  · have e1 : hat (2 ^ k * x - (j : ℤ)) = j + 1 - 2 ^ k * x := by
      unfold hat; rw [abs_of_nonneg (by linarith)]; rw [max_eq_right (by linarith)]; ring
    have e2 : hat (2 ^ k * x - ((j + 1 : ℤ) : ℝ)) = 2 ^ k * x - j := by
      unfold hat; push_cast; rw [abs_of_nonpos (by linarith)]; rw [max_eq_right (by linarith)]
      ring
    rw [e1, e2]
  · intro i _ hi
    have : hat (2 ^ k * x - i) = 0 := by
      unfold hat
      apply max_eq_left
      rcases lt_or_gt_of_ne hi.1 with h | h
      · have : (i : ℝ) ≤ j - 1 := by exact_mod_cast (show i ≤ j - 1 by omega)
        rw [abs_of_nonneg (by linarith)]; linarith
      · have : (i : ℝ) ≥ j + 2 := by
          have := hi.2
          exact_mod_cast (show i ≥ j + 2 by omega)
        rw [abs_of_nonpos (by linarith)]; linarith
    rw [this, mul_zero]
  · intro h; exact absurd (Finset.mem_Icc.2 ⟨hA, by omega⟩) h
  · intro h; exact absurd (Finset.mem_Icc.2 ⟨by omega, by omega⟩) h

/-- Rational nodal values `v_j` approximating given reals `a_j`, with `v_{j+1} ≠ v_j`. -/
lemma exists_rat_nodes (a : ℤ → ℝ) (η : ℝ) (hη : 0 < η) :
    ∃ v : ℤ → ℚ, (∀ j, |(v j : ℝ) - a j| < η) ∧ ∀ j, v (j + 1) ≠ v j := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
  have hNpos : (0 : ℝ) < N + 1 := by positivity
  refine ⟨fun j => ((2 * ⌊((N : ℝ) + 1) * a j⌋ + j % 2 : ℤ) : ℚ) / (2 * ((N : ℚ) + 1)),
    fun j => ?_, fun j => ?_⟩
  · have hm0 : 0 ≤ j % 2 := Int.emod_nonneg _ (by norm_num)
    have hm1 : j % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
    have hm0' : (0 : ℝ) ≤ ((j % 2 : ℤ) : ℝ) := by exact_mod_cast hm0
    have hm1' : ((j % 2 : ℤ) : ℝ) ≤ 1 := by exact_mod_cast (show j % 2 ≤ 1 by omega)
    have hf1 := Int.floor_le (((N : ℝ) + 1) * a j)
    have hf2 := Int.lt_floor_add_one (((N : ℝ) + 1) * a j)
    push_cast
    rw [abs_lt]
    have e : (2 * (⌊((N : ℝ) + 1) * a j⌋ : ℝ) + ((j % 2 : ℤ) : ℝ)) / (2 * ((N : ℝ) + 1)) - a j =
        (2 * (⌊((N : ℝ) + 1) * a j⌋ : ℝ) + ((j % 2 : ℤ) : ℝ) - 2 * (((N : ℝ) + 1) * a j)) /
          (2 * ((N : ℝ) + 1)) := by field_simp
    rw [e]
    have hη' : 1 / ((N : ℝ) + 1) < η := hN
    rw [div_lt_iff₀ hNpos] at hη'
    constructor
    · rw [lt_div_iff₀ (by positivity)]; nlinarith
    · rw [div_lt_iff₀ (by positivity)]; nlinarith
  · intro h
    have hN0 : (2 * ((N : ℚ) + 1)) ≠ 0 := by positivity
    rw [div_left_inj' hN0] at h
    have h' := Int.cast_injective h
    omega

/-- The number of cells of the uniform cover, Equation (23). -/
noncomputable def Ncells (α β : ℝ) (k : ℕ) : ℤ := ⌈β * 2 ^ k⌉ - ⌊α * 2 ^ k⌋

/-- **Equation (23).** `N_k = ⌈β 2^k⌉ - ⌊α 2^k⌋ = (β - α) 2^k + O(1)`; precisely,
`0 ≤ N_k - (β - α) 2^k < 2`. -/
theorem Ncells_asymptotic (α β : ℝ) (k : ℕ) :
    0 ≤ (Ncells α β k : ℝ) - (β - α) * 2 ^ k ∧ (Ncells α β k : ℝ) - (β - α) * 2 ^ k < 2 := by
  unfold Ncells
  have h1 := Int.le_ceil (β * 2 ^ k)
  have h2 := Int.ceil_lt_add_one (β * 2 ^ k)
  have h3 := Int.floor_le (α * 2 ^ k)
  have h4 := Int.lt_floor_add_one (α * 2 ^ k)
  push_cast
  constructor <;> nlinarith

/-- **Equation (23), the cover.** The uniform cover of `[α, β]` by the cells `J_{k,j}`,
`⌊α 2^k⌋ ≤ j < ⌈β 2^k⌉`, covers `[α, β]` (when `α < β`) and has exactly `N_k` cells. -/
theorem uniform_cover (α β : ℝ) (hαβ : α < β) (k : ℕ) :
    Icc α β ⊆ ⋃ j ∈ Finset.Ico ⌊α * 2 ^ k⌋ ⌈β * 2 ^ k⌉, cellJ k j ∧
      ((Finset.Ico ⌊α * 2 ^ k⌋ ⌈β * 2 ^ k⌉).card : ℤ) = Ncells α β k := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  constructor
  · intro x ⟨hx1, hx2⟩
    simp only [mem_iUnion, Finset.mem_Ico, exists_prop]
    have hfl : ⌊α * 2 ^ k⌋ ≤ ⌊x * 2 ^ k⌋ := Int.floor_mono (by nlinarith)
    have hfx := Int.floor_le (x * 2 ^ k)
    have hfx2 := Int.lt_floor_add_one (x * 2 ^ k)
    have hcx : ⌊x * 2 ^ k⌋ ≤ ⌈β * 2 ^ k⌉ := by
      have := Int.le_ceil (β * 2 ^ k)
      have : (⌊x * 2 ^ k⌋ : ℝ) ≤ ⌈β * 2 ^ k⌉ := by nlinarith
      exact_mod_cast this
    rcases lt_or_eq_of_le hcx with hlt | heq
    · refine ⟨⌊x * 2 ^ k⌋, ⟨hfl, hlt⟩, ?_, ?_⟩
      · rw [div_le_iff₀ hp]; linarith
      · rw [le_div_iff₀ hp]; linarith
    · -- `x 2^k` is the integer `⌈β 2^k⌉`; use the cell to its left
      have hxe : x * 2 ^ k = ⌈β * 2 ^ k⌉ := by
        have := Int.le_ceil (β * 2 ^ k)
        have h' : (⌊x * 2 ^ k⌋ : ℝ) = ⌈β * 2 ^ k⌉ := by exact_mod_cast heq
        nlinarith
      have hαlt : ⌊α * 2 ^ k⌋ < ⌈β * 2 ^ k⌉ := by
        have : (⌊α * 2 ^ k⌋ : ℝ) < ⌈β * 2 ^ k⌉ := by
          have := Int.le_ceil (β * 2 ^ k)
          have : α * 2 ^ k < β * 2 ^ k := by nlinarith
          linarith [Int.floor_le (α * 2 ^ k)]
        exact_mod_cast this
      refine ⟨⌈β * 2 ^ k⌉ - 1, ⟨by omega, by omega⟩, ?_, ?_⟩
      · rw [div_le_iff₀ hp]; push_cast; linarith
      · rw [le_div_iff₀ hp]; push_cast; linarith
  · rw [Int.card_Ico, Ncells]
    have : ⌊α * 2 ^ k⌋ ≤ ⌈β * 2 ^ k⌉ := by
      have : (⌊α * 2 ^ k⌋ : ℝ) ≤ ⌈β * 2 ^ k⌉ := by
        have := Int.le_ceil (β * 2 ^ k)
        have : α * 2 ^ k ≤ β * 2 ^ k := by nlinarith
        linarith [Int.floor_le (α * 2 ^ k)]
      exact_mod_cast this
    omega

/-- **Theorem 4.2 (density of assemblies).** For every `f ∈ C[α, β]` and every `ε > 0` there is
`g ∈ 𝒜([α, β])` with `‖f - g‖_{∞, [α, β]} < ε`. (By Definition 4.1, all pieces of `g` are
lines `ℓ_n` of the library, hence with nonzero slope; see `Gamma_wellformed`.) -/
theorem assemblies_dense (α β : ℝ) (hαβ : α < β) (f : C(Icc α β, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g ∈ Asm α β, ‖f - g‖ < ε := by
  -- the extension of `f` by constants
  set F : ℝ → ℝ := Set.IccExtend hαβ.le f with hF
  have hFf : ∀ x : Icc α β, F x = f x := fun x => Set.IccExtend_val hαβ.le f x
  have hFuc : UniformContinuous F :=
    (CompactSpace.uniformContinuous_of_continuous f.continuous).comp
      (LipschitzWith.projIcc hαβ.le).uniformContinuous
  obtain ⟨δ, hδ, hFδ⟩ := Metric.uniformContinuous_iff.1 hFuc (ε / 4) (by positivity)
  -- choose the scale `k` with `2^{-k} < δ`
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / δ) (by norm_num : (1 : ℝ) < 2)
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hkδ : 1 / (2 : ℝ) ^ k < δ := by
    rw [div_lt_iff₀ hp]; rw [div_lt_iff₀ hδ] at hk; linarith
  -- rational nodal values
  obtain ⟨v, hv, hvne⟩ := exists_rat_nodes (fun j => F ((j : ℝ) / 2 ^ k)) (ε / 4) (by positivity)
  set A := ⌊α * 2 ^ k⌋ with hA
  set B := ⌊β * 2 ^ k⌋ with hB
  set G : ℝ → ℝ := interp k (fun j => (v j : ℝ)) A B with hG
  -- addresses of the pieces
  have hslope : ∀ j : ℤ, (v (j + 1) - v j) * 2 ^ k ≠ 0 := fun j =>
    mul_ne_zero (sub_ne_zero.2 (hvne j)) (by positivity)
  choose addr haddr using fun j : ℤ =>
    exists_address k j ((v j + v (j + 1)) / 2) ((v (j + 1) - v j) * 2 ^ k) (hslope j)
  -- the piece on `J_{k,j}` is the atom `addr j`
  have hpiece : ∀ j : ℤ, A ≤ j → j ≤ B → ∀ x : ℝ, x ∈ cellJ k j → G x = line (addr j) x := by
    intro j hjA hjB x hx
    obtain ⟨h1, h2, h3, h4⟩ := haddr j
    have hx1 : (j : ℝ) ≤ 2 ^ k * x := by
      have := hx.1; rw [div_le_iff₀ hp] at this; linarith
    have hx2 : 2 ^ k * x ≤ j + 1 := by
      have := hx.2; rw [le_div_iff₀ hp] at this; linarith
    rw [hG, interp_eq k _ A B j hjA hjB x hx1 hx2, line_eq_anchored, x0n, h1, h2, h3, h4,
      center]
    push_cast
    field_simp
    ring
  -- the error estimate
  have herr : ∀ x : Icc α β, |f x - G x| ≤ ε / 2 := by
    intro x
    set j := ⌊2 ^ k * (x : ℝ)⌋ with hj
    have hx1 := Int.floor_le (2 ^ k * (x : ℝ))
    have hx2 := Int.lt_floor_add_one (2 ^ k * (x : ℝ))
    have hjA : A ≤ j := Int.floor_mono (by nlinarith [x.2.1])
    have hjB : j ≤ B := Int.floor_mono (by nlinarith [x.2.2])
    rw [hG, interp_eq k _ A B j hjA hjB x hx1 hx2.le, ← hFf]
    set θ := 2 ^ k * (x : ℝ) - j with hθ
    have hθ0 : 0 ≤ θ := by linarith
    have hθ1 : θ ≤ 1 := by linarith
    have key : ∀ y : ℝ, (x : ℝ) - y / 2 ^ k = (2 ^ k * x - y) / 2 ^ k := by
      intro y; field_simp
    have hd1 : |(x : ℝ) - j / 2 ^ k| < δ := by
      rw [key, abs_div, abs_of_pos hp, div_lt_iff₀ hp, abs_of_nonneg (by linarith)]
      rw [div_lt_iff₀ hp] at hkδ; linarith
    have hd2 : |(x : ℝ) - ((j + 1 : ℤ) : ℝ) / 2 ^ k| < δ := by
      rw [key, abs_div, abs_of_pos hp, div_lt_iff₀ hp, abs_of_nonpos (by push_cast; linarith)]
      rw [div_lt_iff₀ hp] at hkδ; push_cast; linarith
    have hE1 : |F x - v j| < ε / 2 := by
      have a1 : |F x - F (j / 2 ^ k)| < ε / 4 := by
        have := hFδ (a := (x : ℝ)) (b := j / 2 ^ k) (by rwa [Real.dist_eq]); rwa [Real.dist_eq] at this
      have a2 := hv j
      calc |F x - v j| = |(F x - F (j / 2 ^ k)) - ((v j : ℝ) - F (j / 2 ^ k))| := by ring_nf
        _ ≤ |F x - F (j / 2 ^ k)| + |(v j : ℝ) - F (j / 2 ^ k)| := abs_sub _ _
        _ < ε / 4 + ε / 4 := add_lt_add a1 a2
        _ = ε / 2 := by ring
    have hE2 : |F x - v (j + 1)| < ε / 2 := by
      have a1 : |F x - F (((j + 1 : ℤ) : ℝ) / 2 ^ k)| < ε / 4 := by
        have := hFδ (a := (x : ℝ)) (b := ((j + 1 : ℤ) : ℝ) / 2 ^ k) (by rwa [Real.dist_eq])
        rwa [Real.dist_eq] at this
      have a2 := hv (j + 1)
      calc |F x - v (j + 1)| = |(F x - F (((j + 1 : ℤ) : ℝ) / 2 ^ k)) -
            ((v (j + 1) : ℝ) - F (((j + 1 : ℤ) : ℝ) / 2 ^ k))| := by ring_nf
        _ ≤ |F x - F (((j + 1 : ℤ) : ℝ) / 2 ^ k)| +
            |(v (j + 1) : ℝ) - F (((j + 1 : ℤ) : ℝ) / 2 ^ k)| := abs_sub _ _
        _ < ε / 4 + ε / 4 := add_lt_add a1 a2
        _ = ε / 2 := by ring
    have e : F x - ((v j : ℝ) * (j + 1 - 2 ^ k * x) + (v (j + 1) : ℝ) * (2 ^ k * x - j)) =
        (1 - θ) * (F x - v j) + θ * (F x - v (j + 1)) := by rw [hθ]; ring
    rw [e]
    calc |(1 - θ) * (F x - v j) + θ * (F x - v (j + 1))|
        ≤ |(1 - θ) * (F x - v j)| + |θ * (F x - v (j + 1))| := abs_add_le _ _
      _ = (1 - θ) * |F x - v j| + θ * |F x - v (j + 1)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hθ0]
      _ ≤ (1 - θ) * (ε / 2) + θ * (ε / 2) := by gcongr; linarith
      _ = ε / 2 := by ring
  -- the assembly
  let g : C(Icc α β, ℝ) := ⟨fun x => G x, (interp_continuous k _ A B).comp continuous_subtype_val⟩
  refine ⟨g, ?_, ?_⟩
  · refine ⟨(Finset.Icc A B).image (fun j => (k, j)), fun J => addr J.2, ?_, ?_, ?_⟩
    · intro J hJ J' hJ' hne
      simp only [Finset.mem_image] at hJ hJ'
      obtain ⟨j, -, rfl⟩ := hJ
      obtain ⟨j', -, rfl⟩ := hJ'
      have hjj : j ≠ j' := fun h => hne (by rw [h])
      simp only [cellJ, interior_Icc]
      rw [Set.disjoint_left]
      rintro x ⟨a1, a2⟩ ⟨b1, b2⟩
      rw [div_lt_iff₀ hp] at a1 b1
      rw [lt_div_iff₀ hp] at a2 b2
      have c1 : (j : ℝ) < j' + 1 := by linarith
      have c2 : (j' : ℝ) < j + 1 := by linarith
      have d1 : j < j' + 1 := by exact_mod_cast c1
      have d2 : j' < j + 1 := by exact_mod_cast c2
      omega
    · intro x hx
      simp only [mem_iUnion, Finset.mem_image, exists_prop]
      have hx1 := Int.floor_le (2 ^ k * x)
      have hx2 := Int.lt_floor_add_one (2 ^ k * x)
      refine ⟨(k, ⌊2 ^ k * x⌋), ⟨⌊2 ^ k * x⌋, Finset.mem_Icc.2 ⟨Int.floor_mono (by nlinarith [hx.1]),
        Int.floor_mono (by nlinarith [hx.2])⟩, rfl⟩, ?_, ?_⟩
      · rw [div_le_iff₀ hp]; linarith
      · rw [le_div_iff₀ hp]; linarith
    · intro J hJ
      simp only [Finset.mem_image, Finset.mem_Icc] at hJ
      obtain ⟨j, ⟨hjA, hjB⟩, rfl⟩ := hJ
      obtain ⟨h1, h2, -, -⟩ := haddr j
      exact ⟨h1, h2, fun x hx => hpiece j hjA hjB x hx⟩
  · have : ‖f - g‖ ≤ ε / 2 := by
      rw [ContinuousMap.norm_le _ (by positivity)]
      intro x
      simpa [g, Real.norm_eq_abs] using herr x
    linarith

end Dyadic2
