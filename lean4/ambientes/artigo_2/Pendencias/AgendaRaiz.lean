import Pendencias.Direta

/-! Agenda nesting, dyadic reduction and the arithmetic floor on an arbitrary dyadic root. -/

namespace Pendencias.Jackson

open Set Artigo LTree Pendencias.Agenda

section Root

variable {k₀ : ℕ} {m₀ : ℤ}

/-- The height and leaf budgets reduce the pointed catalogue to a finite set. -/
private lemma sigmaK_finite (H : ℕ → ℕ) (N : ℕ) : (SigmaK k₀ m₀ H N).Finite := by
  apply ((Set.finite_singleton (0 : ℝ → ℝ)).union
    ((RepCat (H N) N k₀ m₀).finite_toSet.image (fun T ↦ T.eval k₀ m₀))).subset
  rintro g (rfl | ⟨T, hT, rfl⟩)
  · exact Or.inl (Set.mem_singleton _)
  · refine Or.inr ⟨T, Finset.mem_coe.mpr (mem_RepCat.mpr ⟨hT.1, ?_, hT.2.2⟩), rfl⟩
    exact (depth_lt_numLeaves' T).le.trans hT.2.1

/-- IV.3.1 for any root. The zero candidate makes the finite pointed catalogue nonempty. -/
theorem schedule_nesting_K {H : ℕ → ℕ} (hH : Monotone H) (N : ℕ) (f : ℝ → ℝ) :
    SigmaK k₀ m₀ H N ⊆ SigmaK k₀ m₀ H (N + 1) ∧
      pErrK k₀ m₀ H (N + 1) f ≤ pErrK k₀ m₀ H N f ∧
      pErrK k₀ m₀ H N f ≤ distK k₀ m₀ f 0 ∧
      ∃ g ∈ SigmaK k₀ m₀ H N, pErrK k₀ m₀ H N f = distK k₀ m₀ f g := by
  refine ⟨SigmaK_mono hH (Nat.le_succ N), pErrK_antitone hH f (Nat.le_succ N),
    pErrK_le_dist0 k₀ m₀ H N f, ?_⟩
  obtain ⟨g, hg, hmin⟩ := Set.exists_min_image (SigmaK k₀ m₀ H N) (distK k₀ m₀ f)
    (sigmaK_finite H N) ⟨0, zero_mem_SigmaK k₀ m₀ H N⟩
  exact ⟨g, hg, le_antisymm (iInf₂_le g hg) (le_iInf₂ fun x hx ↦ hmin x hx)⟩

/-- IV.3.2 on an arbitrary root, for the weighted rate with finite exponent. -/
theorem dyadic_reduction_K {α q : ℝ} (hα : 0 < α) (hq : 0 < q) {H : ℕ → ℕ}
    (hH : Monotone H) (f : ℝ → ℝ) :
    let a := (∑' r : ℕ,
      (ENNReal.ofReal (((2 : ℝ) ^ r) ^ α) * pErrK k₀ m₀ H (2 ^ r) f) ^ q) ^ (1 / q)
    rateQK k₀ m₀ α q H f ≤ ENNReal.ofReal (2 ^ α) * a ∧
      a ≤ (1 + 2 * ENNReal.ofReal (2 ^ α) ^ q) ^ (1 / q) * rateQK k₀ m₀ α q H f :=
  ⟨rate_q_le_dyadic hα hq (pErrK_antitone hH f),
    dyadic_sequence_le_weighted hα hq (pErrK_antitone hH f)⟩

/-- IV.3.2 on an arbitrary root, for the supremum rate. -/
theorem dyadic_reduction_inf_K {α : ℝ} (hα : 0 < α) {H : ℕ → ℕ}
    (hH : Monotone H) (f : ℝ → ℝ) :
    let a := ⨆ r : ℕ, ENNReal.ofReal (((2 : ℝ) ^ r) ^ α) * pErrK k₀ m₀ H (2 ^ r) f
    a ≤ rateInfK k₀ m₀ α H f ∧ rateInfK k₀ m₀ α H f ≤ ENNReal.ofReal (2 ^ α) * a := by
  refine ⟨iSup_le fun r ↦ ?_, rate_inf_le_dyadic hα (pErrK_antitone hH f)⟩
  unfold rateInfK
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    (le_iSup₂ (f := fun (N : ℕ) (_ : 1 ≤ N) ↦
      ENNReal.ofReal ((N : ℝ) ^ α) * pErrK k₀ m₀ H N f) (2 ^ r) Nat.one_le_two_pow)

/-- IV.4.6, with the sample at an actual leaf centre of the given root. -/
theorem arithmetic_floor_K (H : ℕ → ℕ) (N : ℕ) (hH : 2 ≤ H N) :
    ENNReal.ofReal (1 / (2 * (H N : ℝ))) ≤ pErrK k₀ m₀ H N (fun _ => 1 / (2 * (H N : ℝ))) := by
  set a : ℝ := 1 / (2 * (H N : ℝ)) with ha
  have hH0 : (0 : ℝ) < H N := by exact_mod_cast (by omega : 0 < H N)
  have hpos : 0 < a := by rw [ha]; positivity
  unfold pErrK
  refine le_iInf₂ fun g hg => ?_
  -- A point of the root witnesses the lower bound.
  obtain ⟨x, hx, hgx⟩ : ∃ x ∈ cellIcc k₀ m₀, a ≤ |a - g x| := by
    rcases hg with rfl | ⟨T, ⟨hw, -, hh⟩, rfl⟩
    · exact ⟨cL k₀ m₀, ⟨le_rfl, (cL_lt_cR k₀ m₀).le⟩, by simp [abs_of_pos hpos]⟩
    · obtain ⟨L, hL⟩ := T.leaves_eq_cons
      have hmem : T.firstLeaf ∈ T.leaves := by rw [hL]; exact List.mem_cons_self
      set b := T.firstLeaf
      have hx0 : ((b.x0 : ℚ) : ℝ) ∈ cellIcc b.k b.m := by
        have e : ((b.x0 : ℚ) : ℝ) = ((b.m : ℝ) + 1 / 2) / 2 ^ b.k := by simp [Atom.x0]
        rw [e, cellIcc_eq, cL, cR]
        exact ⟨(div_le_div_iff_of_pos_right (by positivity)).mpr (by linarith),
          (div_le_div_iff_of_pos_right (by positivity)).mpr (by linarith)⟩
      have hval : T.eval k₀ m₀ (b.x0 : ℝ) = (b.y0 : ℝ) := by
        rw [eval_leaf hw b hmem _ hx0]
        simp [Atom.eval]
      have hht : ht b.y0 ≤ H N := by
        have h1 : ht b.y0 ≤ b.height := by unfold Atom.height; omega
        exact h1.trans ((le_maxHeight hmem).trans hh)
      refine ⟨(b.x0 : ℝ), ?_, ?_⟩
      · exact leaves_cell_sub hw b hmem hx0
      · rw [hval]; exact half_inv_le_dist hH hht
  change ENNReal.ofReal a ≤ ⨆ x ∈ cellIcc k₀ m₀, ENNReal.ofReal |a - g x|
  exact (ENNReal.ofReal_le_ofReal hgx).trans
    (le_iSup₂ (f := fun x (_ : x ∈ cellIcc k₀ m₀) => ENNReal.ofReal |a - g x|) x hx)

/-- Uniform rate bounds force the height schedule in IV.4.6. -/
theorem height_lower_bound_K (H : ℕ → ℕ) (F : Set (ℝ → ℝ)) {C s : ℝ}
    (hconst : ∀ a : ℝ, |a| ≤ 1 / 4 → (fun _ => a) ∈ F)
    (hrate : ∀ N : ℕ, 1 ≤ N → ∀ f ∈ F, pErrK k₀ m₀ H N f ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-s)))
    {N : ℕ} (hN : 1 ≤ N) (hHN : 2 ≤ H N) :
    (2 * C)⁻¹ * (N : ℝ) ^ s ≤ H N := by
  have hh : (0 : ℝ) < H N := by exact_mod_cast (by omega : 0 < H N)
  have hh2 : (2 : ℝ) ≤ H N := by exact_mod_cast hHN
  have hmemF : (fun _ => 1 / (2 * (H N : ℝ))) ∈ F := hconst _ (by
    rw [abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith)
  have h1 := (arithmetic_floor_K H N hHN).trans (hrate N hN _ hmemF)
  rw [ENNReal.ofReal_le_ofReal_iff'] at h1
  have hP : (0 : ℝ) < (N : ℝ) ^ s := Real.rpow_pos_of_pos (by exact_mod_cast hN) s
  rcases h1 with h1 | h1
  · rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv,
      div_le_div_iff₀ (by positivity) hP] at h1
    have hC : 0 < C := by nlinarith
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith
  · exact absurd h1 (not_le.mpr (by positivity))

end Root

end Pendencias.Jackson
