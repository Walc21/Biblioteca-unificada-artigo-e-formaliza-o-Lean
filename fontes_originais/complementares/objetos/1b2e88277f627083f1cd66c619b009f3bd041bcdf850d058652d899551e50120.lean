module
public import RequestProject.Sec7.EntropyLower
public import RequestProject.Sec7.Interp
@[expose] public section

/-!
# Theorem 7.18, upper bound: the explicit codebook of assemblies

For `N = 2^k` and `δ = 2^{-q}`, every `f ∈ 𝓕_{R,M}` is quantised at the nodes `t_j = j/N` on the
alternating grids `δ(ℤ + (j mod 2)/2)` (nearest point, ties towards the smaller one):
`v_j = b_j δ/2` with `b_j ≡ j (mod 2)`.  The interpolant of the `v_j` is an assembly with `N`
leaves.  The codebook is the (finite) set of these interpolants; it is counted through
`(b_0, b_1 - b_0, (b_{j+2} - 2 b_{j+1} + b_j)_j)`, the second differences being bounded by the
curvature constraint.
-/

open Set Finset

namespace Dyadic.Lib

attribute [local instance] Classical.propDecidable

/-! ### Second differences -/

/-- `|f(t+h) - 2 f(t) + f(t-h)| ≤ M h²` for `f ∈ 𝓕_{R,M}`. -/
lemma FRM.second_diff {R M : ℝ} {f : ℝ → ℝ} (hf : f ∈ FRM R M) {t h : ℝ} (hh : 0 < h)
    (h0 : 0 ≤ t - h) (h1 : t + h ≤ 1) : |f (t + h) - 2 * f t + f (t - h)| ≤ M * h ^ 2 := by
  have hC := FRM.c2bound hf h0 h1
  have ht : t ∈ Ioo (t - h) (t + h) := ⟨by linarith, by linarith⟩
  have hA := taylor1_bound hC ht (x := t + h) ⟨by linarith, le_rfl⟩
  have hB := taylor1_bound hC ht (x := t - h) ⟨le_rfl, by linarith⟩
  rw [show t + h - t = h by ring] at hA
  rw [show t - h - t = -h by ring] at hB
  rw [abs_le] at hA hB ⊢
  constructor <;> nlinarith [hA.1, hA.2, hB.1, hB.2]

/-! ### Quantisation and reconstruction -/

/-- The quantised numerator `b_j = gridNum(2^{q+1} f(j/2^k), j mod 2)`, so that
`v_j = b_j / 2^{q+1}` is the nearest point of `δ(ℤ + (j mod 2)/2)` to `f(t_j)`, `δ = 2^{-q}`. -/
noncomputable def bq (q k : ℕ) (f : ℝ → ℝ) (j : ℕ) : ℤ :=
  gridNum (2 ^ (q + 1) * f (j / 2 ^ k)) (j % 2)

/-- Extension of a numerator sequence beyond the last node `N` by unit steps. -/
def extW (N : ℕ) (w : ℕ → ℤ) (j : ℕ) : ℤ := if j ≤ N then w j else w N + (j - N : ℕ)

/-- The rational nodal values `w_j / 2^{q+1}`. -/
def valQ (q : ℕ) (w : ℕ → ℤ) (j : ℕ) : ℚ := (w j : ℚ) / 2 ^ (q + 1)

/-- The interpolating assembly with `2^k` leaves of the nodal values `w_j / 2^{q+1}`
(`0` if two consecutive values coincide). -/
noncomputable def Gk (q k : ℕ) (w : ℕ → ℤ) : ℝ → ℝ :=
  if h : ∀ j, valQ q (extW (2 ^ k) w) (j + 1) ≠ valQ q (extW (2 ^ k) w) j then
    chainFun (interpAtom k (valQ q (extW (2 ^ k) w)) h) (2 ^ k) else 0

/-- Reconstruction of a sequence from `b_0`, `b_1 - b_0` and the second differences. -/
def recon (b0 e1 : ℤ) (d : ℕ → ℤ) : ℕ → ℤ
  | 0 => b0
  | 1 => b0 + e1
  | (j + 2) => 2 * recon b0 e1 d (j + 1) - recon b0 e1 d j + d j

lemma extW_congr {N : ℕ} {w w' : ℕ → ℤ} (h : ∀ j ≤ N, w j = w' j) : extW N w = extW N w' := by
  funext j; unfold extW; split_ifs with hj
  · exact h j hj
  · rw [h N le_rfl]

lemma Gk_congr {q k : ℕ} {w w' : ℕ → ℤ} (h : ∀ j ≤ 2 ^ k, w j = w' j) : Gk q k w = Gk q k w' := by
  unfold Gk; rw [extW_congr h]

lemma bq_mod (q k : ℕ) (f : ℝ → ℝ) (j : ℕ) : bq q k f j ≡ (j % 2 : ℕ) [ZMOD 2] :=
  gridNum_mod _ _

lemma bq_sub_le (q k : ℕ) (f : ℝ → ℝ) (j : ℕ) :
    |(bq q k f j : ℝ) - 2 ^ (q + 1) * f (j / 2 ^ k)| ≤ 1 :=
  gridNum_sub_le _ _

lemma bq_cons (q k : ℕ) (f : ℝ → ℝ) :
    ∀ j, valQ q (extW (2 ^ k) (bq q k f)) (j + 1) ≠ valQ q (extW (2 ^ k) (bq q k f)) j := by
  intro j
  unfold valQ
  rw [Ne, div_left_inj' (by positivity)]
  norm_cast
  unfold extW
  split_ifs with h1 h2 h2
  · intro h
    have a1 := bq_mod q k f (j + 1)
    have a2 := bq_mod q k f j
    rw [h] at a1
    have := a1.symm.trans a2
    have h3 := Int.ModEq.dvd this
    omega
  · omega
  · have : j = 2 ^ k := by omega
    subst this; simp
  · omega

lemma recon_eq {N : ℕ} (b : ℕ → ℤ) (d : ℕ → ℤ)
    (hd : ∀ j, j + 2 ≤ N → d j = b (j + 2) - 2 * b (j + 1) + b j) :
    ∀ j ≤ N, recon (b 0) (b 1 - b 0) d j = b j := by
  have key : ∀ j, j + 1 ≤ N →
      recon (b 0) (b 1 - b 0) d j = b j ∧ recon (b 0) (b 1 - b 0) d (j + 1) = b (j + 1) := by
    intro j
    induction j with
    | zero => intro _; simp [recon]
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2⟩ := ih (by omega)
      refine ⟨h2, ?_⟩
      show 2 * recon (b 0) (b 1 - b 0) d (j + 1) - recon (b 0) (b 1 - b 0) d j + d j = b (j + 2)
      rw [h1, h2, hd j (by omega)]; ring
  intro j hj
  rcases j with _ | j
  · simp [recon]
  · exact (key j hj).2

/-! ### The codebook for fixed `k, q` -/

/-- The bound `B₀ = ⌈2^{q+1} R⌉ + 1` on `|b_0|`. -/
noncomputable def B0c (R : ℝ) (q : ℕ) : ℕ := ⌈2 ^ (q + 1) * R⌉₊ + 1

/-- The bound `B₁ = ⌈2^{q+1} C₀ / 2^k⌉ + 2` on `|b_1 - b_0|`. -/
noncomputable def B1c (R M : ℝ) (q k : ℕ) : ℕ := ⌈2 ^ (q + 1) * C0 R M / 2 ^ k⌉₊ + 2

/-- The parameter box `[-B₀, B₀] × [-B₁, B₁] × [-20, 20]^N`. -/
noncomputable def parBox (R M : ℝ) (q k : ℕ) : Finset (ℤ × ℤ × (Fin (2 ^ k) → ℤ)) :=
  Finset.Icc (-(B0c R q : ℤ)) (B0c R q) ×ˢ Finset.Icc (-(B1c R M q k : ℤ)) (B1c R M q k) ×ˢ
    Fintype.piFinset (fun _ => Finset.Icc (-20 : ℤ) 20)

/-- The reconstruction map from the parameter box to numerator sequences. -/
def parRecon {N : ℕ} (p : ℤ × ℤ × (Fin N → ℤ)) : ℕ → ℤ :=
  recon p.1 p.2.1 (fun j => if h : j < N then p.2.2 ⟨j, h⟩ else 0)

/-- The codebook `𝒞`: the interpolating assemblies coming from the parameter box. -/
noncomputable def codebook (R M : ℝ) (q k : ℕ) : Finset (ℝ → ℝ) :=
  (((parBox R M q k).image parRecon).image (Gk q k)).filter (· ∈ Asm (Icc 0 1))

lemma card_parBox (R M : ℝ) (q k : ℕ) :
    (parBox R M q k).card = (2 * B0c R q + 1) * (2 * B1c R M q k + 1) * 41 ^ (2 ^ k) := by
  simp only [parBox, card_product, Fintype.card_piFinset, Int.card_Icc, prod_const, card_univ,
    Fintype.card_fin]
  have e : ∀ n : ℕ, ((n : ℤ) + 1 - -(n : ℤ)).toNat = 2 * n + 1 := by intro n; omega
  rw [e, e, show ((20 : ℤ) + 1 - -20).toNat = 41 by rfl]
  ring

lemma card_codebook_le (R M : ℝ) (q k : ℕ) :
    (codebook R M q k).card ≤ (2 * B0c R q + 1) * (2 * B1c R M q k + 1) * 41 ^ (2 ^ k) := by
  rw [← card_parBox]
  unfold codebook
  exact (card_filter_le _ _).trans (card_image_le.trans card_image_le)

lemma codebook_subset_Asm (R M : ℝ) (q k : ℕ) : (codebook R M q k : Set (ℝ → ℝ)) ⊆ Asm (Icc 0 1) := by
  intro g hg
  unfold codebook at hg
  exact (mem_filter.1 hg).2

lemma int_mem_Icc_of_abs {b : ℤ} {B : ℕ} (h : |(b : ℝ)| ≤ B) : b ∈ Finset.Icc (-(B : ℤ)) B := by
  rw [abs_le] at h
  rw [Finset.mem_Icc]
  constructor
  · have : (-(B : ℝ)) ≤ b := h.1
    exact_mod_cast this
  · have : (b : ℝ) ≤ B := h.2
    exact_mod_cast this

/-- **Codebook for fixed `N = 2^k`, `δ = 2^{-q}`.** If `M/(8N²) + δ/2 ≤ ε` and `2^{q+1} M / N² ≤ 16`,
every `f ∈ 𝓕_{R,M}` is within `ε` of a member of the codebook on `[0,1]`. -/
theorem codebook_distortion {R M ε : ℝ} {q k : ℕ} (hM : 0 ≤ M)
    (herr : M / (8 * ((2 : ℝ) ^ k) ^ 2) + 1 / 2 ^ (q + 1) ≤ ε)
    (hcurv : 2 ^ (q + 1) * M / ((2 : ℝ) ^ k) ^ 2 ≤ 16) :
    ∀ f ∈ FRM R M, ∃ g ∈ codebook R M q k, ∀ x ∈ Icc (0 : ℝ) 1, |f x - g x| ≤ ε := by
  classical
  intro f hf
  set N := 2 ^ k with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have h2q : (0 : ℝ) < 2 ^ (q + 1) := by positivity
  set b := bq q k f
  have hcons := bq_cons q k f
  set g := chainFun (interpAtom k (valQ q (extW N b)) hcons) N
  have hg : Gk q k b = g := by unfold Gk; rw [dif_pos hcons]
  have hval : ∀ j ≤ N, ((valQ q (extW N b) j : ℚ) : ℝ) = (b j : ℝ) / 2 ^ (q + 1) := by
    intro j hj; simp [valQ, extW, hj]
  -- error
  have herr' : ∀ x ∈ Icc (0 : ℝ) 1, |f x - g x| ≤ ε := by
    intro x hx
    have := interp_error (r := k) (v := valQ q (extW N b)) (hv := hcons) (f := f) (M := M)
      (η := 1 / 2 ^ (q + 1)) hM (fun p q hp hq => FRM.c2bound hf hp hq) (fun j hj => by
        rw [hval j hj]
        have h1 := bq_sub_le q k f j
        rw [show (b j : ℝ) / 2 ^ (q + 1) - f (j / 2 ^ k) =
          ((b j : ℝ) - 2 ^ (q + 1) * f (j / 2 ^ k)) / 2 ^ (q + 1) by field_simp, abs_div,
          abs_of_pos h2q]
        exact div_le_div_of_nonneg_right h1 h2q.le) x hx
    exact this.trans herr
  -- membership
  have hR : 0 ≤ R := (abs_nonneg _).trans (hf.2.1 0 (by simp))
  have hX : ∀ j : ℕ, |(b j : ℝ) - 2 ^ (q + 1) * f (j / 2 ^ k)| ≤ 1 := bq_sub_le q k f
  set p : ℤ × ℤ × (Fin N → ℤ) := (b 0, b 1 - b 0,
    fun j => if (j : ℕ) + 2 ≤ N then b (j + 2) - 2 * b (j + 1) + b j else 0) with hp
  have hrec : ∀ j ≤ N, parRecon p j = b j := by
    show ∀ j ≤ N, recon (b 0) (b 1 - b 0) _ j = b j
    refine recon_eq b _ (fun j hj => ?_)
    rw [hp]
    simp only [show j < N by omega, dif_pos, hj, if_true]
  have hpP : p ∈ parBox R M q k := by
    simp only [parBox, Finset.mem_product, Fintype.mem_piFinset, hp]
    refine ⟨?_, ?_, ?_⟩
    · apply int_mem_Icc_of_abs
      have h1 := hX 0
      have h2 := hf.2.1 (((0 : ℕ) : ℝ) / 2 ^ k) (by simp)
      have h3 := Nat.le_ceil (2 ^ (q + 1) * R)
      simp only [B0c]; push_cast
      have h4 : |2 ^ (q + 1) * f (((0 : ℕ) : ℝ) / 2 ^ k)| ≤ 2 ^ (q + 1) * R := by
        rw [abs_mul, abs_of_pos h2q]
        exact mul_le_mul_of_nonneg_left h2 h2q.le
      have h5 := abs_sub_abs_le_abs_sub (b 0 : ℝ) (2 ^ (q + 1) * f (((0 : ℕ) : ℝ) / 2 ^ k))
      linarith
    · apply int_mem_Icc_of_abs
      have h1 := hX 0
      have h1' := hX 1
      have hL := FRM.lipschitz hf (x := ((0 : ℕ) : ℝ) / 2 ^ k) (y := ((1 : ℕ) : ℝ) / 2 ^ k)
        (by simp) (by
          refine ⟨by positivity, ?_⟩
          rw [div_le_one h2k]; exact_mod_cast hN1)
      have h3 := Nat.le_ceil (2 ^ (q + 1) * C0 R M / 2 ^ k)
      simp only [B1c]; push_cast
      simp only [Nat.cast_zero, Nat.cast_one, zero_div, sub_zero] at h1 h1' hL h3 ⊢
      rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ k)] at hL
      have h4 : |2 ^ (q + 1) * f (1 / 2 ^ k) - 2 ^ (q + 1) * f 0| ≤ 2 ^ (q + 1) * C0 R M / 2 ^ k := by
        rw [← mul_sub, abs_mul, abs_of_pos h2q]
        calc 2 ^ (q + 1) * |f (1 / 2 ^ k) - f 0| ≤ 2 ^ (q + 1) * (C0 R M * (1 / 2 ^ k)) :=
              mul_le_mul_of_nonneg_left hL h2q.le
          _ = _ := by ring
      rw [abs_le] at h1 h1' h4 ⊢
      constructor <;> linarith [h1.1, h1.2, h1'.1, h1'.2, h4.1, h4.2]
    · intro j
      split_ifs with hj
      · rw [Finset.mem_Icc]
        have hA := hX j
        have hB := hX (j + 1)
        have hC := hX (j + 2)
        have hS := FRM.second_diff hf (t := ((j : ℝ) + 1) / 2 ^ k) (h := 1 / 2 ^ k)
          (by positivity) (by rw [← sub_div]; ring_nf; positivity) (by
            rw [← add_div, div_le_one h2k]
            have : ((j : ℝ) + 2) ≤ (2 ^ k : ℕ) := by exact_mod_cast hj
            push_cast at this; linarith)
        have e1 : ((j + 1 : ℕ) : ℝ) / 2 ^ k = ((j : ℝ) + 1) / 2 ^ k := by push_cast; ring
        have e2 : ((j + 2 : ℕ) : ℝ) / 2 ^ k = ((j : ℝ) + 1) / 2 ^ k + 1 / 2 ^ k := by
          push_cast; ring
        have e0 : ((j : ℕ) : ℝ) / 2 ^ k = ((j : ℝ) + 1) / 2 ^ k - 1 / 2 ^ k := by ring
        rw [e1] at hB; rw [e2] at hC; rw [e0] at hA
        set t := ((j : ℝ) + 1) / 2 ^ k
        set h := (1 : ℝ) / 2 ^ k
        have hcurv' : 2 ^ (q + 1) * (M * h ^ 2) ≤ 16 := by
          simp only [h]; rw [div_pow, one_pow]
          calc 2 ^ (q + 1) * (M * (1 / ((2 : ℝ) ^ k) ^ 2)) = 2 ^ (q + 1) * M / (2 ^ k) ^ 2 := by
                ring
            _ ≤ 16 := hcurv
        have h4 : |2 ^ (q + 1) * f (t + h) - 2 * (2 ^ (q + 1) * f t) + 2 ^ (q + 1) * f (t - h)| ≤ 16 := by
          rw [show 2 ^ (q + 1) * f (t + h) - 2 * (2 ^ (q + 1) * f t) + 2 ^ (q + 1) * f (t - h) =
            2 ^ (q + 1) * (f (t + h) - 2 * f t + f (t - h)) by ring, abs_mul, abs_of_pos h2q]
          exact (mul_le_mul_of_nonneg_left hS h2q.le).trans hcurv'
        rw [abs_le] at hA hB hC h4
        constructor
        · have : (-20 : ℝ) ≤ (b (j + 2) : ℝ) - 2 * b (j + 1) + b j := by
            linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2, h4.1, h4.2]
          exact_mod_cast this
        · have : (b (j + 2) : ℝ) - 2 * b (j + 1) + b j ≤ 20 := by
            linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2, h4.1, h4.2]
          exact_mod_cast this
      · simp
  have hmem : g ∈ codebook R M q k := by
    unfold codebook
    rw [mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_image]
      refine ⟨parRecon p, mem_image_of_mem _ hpP, ?_⟩
      rw [Gk_congr hrec, hg]
    · exact (interp_isAssemblyRep (r := k) (v := valQ q (extW N b)) (hv := hcons)).2.2
  exact ⟨g, hmem, herr'⟩

end Dyadic.Lib
