module
public import Unified.Fase3.Rates

/-!
# Section 6: certified adaptive dyadic refinement (Algorithm 6.3, Theorem 6.4)

The refinement loop of Algorithm 6.3 is modelled by an explicit recursion with a fuel
parameter (the maximal number of subdivision levels).  Termination is expressed by the fact
that the output is stable for all fuels beyond `r*` and that no leaf violates the stopping
criterion, i.e. the `while` condition of step (iii) is false on the output.
-/

@[expose] public section

namespace Fase3

open Set

/-- The certificate `η_cert(J) = |J|² M(J) / 8` (equation (41)). -/
noncomputable def cert (M : ℕ × ℤ → ℝ) (J : ℕ × ℤ) : ℝ := mesh J.1 ^ 2 * M J / 8

/-- Left child `J_{k+1,2m}`. -/
def child0 (J : ℕ × ℤ) : ℕ × ℤ := (J.1 + 1, 2 * J.2)
/-- Right child `J_{k+1,2m+1}`. -/
def child1 (J : ℕ × ℤ) : ℕ × ℤ := (J.1 + 1, 2 * J.2 + 1)

/-- Step (iii) of Algorithm 6.3 applied below one cell, with at most `r` levels:
a leaf with `η_cert(J) > ε` is replaced by its two children. -/
noncomputable def refineCell (M : ℕ × ℤ → ℝ) (ε : ℝ) : ℕ → ℕ × ℤ → List (ℕ × ℤ)
  | 0, J => [J]
  | r + 1, J => if cert M J ≤ ε then [J] else
      refineCell M ε r (child0 J) ++ refineCell M ε r (child1 J)

/-- Algorithm 6.3, steps (i)–(iii): refine every root of the initial cover. -/
noncomputable def refineAll (M : ℕ × ℤ → ℝ) (ε : ℝ) (roots : List (ℕ × ℤ)) (r : ℕ) :
    List (ℕ × ℤ) := roots.flatMap (refineCell M ε r)

/-- The depth bound `r* = max{0, ⌈½ log₂(h₀² M* / (8 ε_I))⌉}` (equation (43)). -/
noncomputable def rStar (h0 Mstar εI : ℝ) : ℕ := (max 0 ⌈1 / 2 * Real.logb 2 (h0 ^ 2 * Mstar / (8 * εI))⌉).toNat

/-- If `M* = 0` one may take `r* = 0` (and indeed the formula gives `0`). -/
theorem rStar_zero (h0 εI : ℝ) : rStar h0 0 εI = 0 := by simp [rStar]

/-- Interiors of two cells are disjoint. -/
def DisjInt (A B : ℕ × ℤ) : Prop := Disjoint (Ioo (cL A) (cR A)) (Ioo (cL B) (cR B))

lemma disjInt_symm : Symmetric DisjInt := fun _ _ h => Disjoint.symm h

lemma cC_child0 (J : ℕ × ℤ) : cC (child0 J) ⊆ cC J := by
  simp only [cC, child0]; rw [cell_refine J.1 J.2]; exact subset_union_left

lemma cC_child1 (J : ℕ × ℤ) : cC (child1 J) ⊆ cC J := by
  simp only [cC, child1]; rw [cell_refine J.1 J.2]; exact subset_union_right

lemma cC_children (J : ℕ × ℤ) : cC J = cC (child0 J) ∪ cC (child1 J) := cell_refine J.1 J.2

lemma disjInt_children (J : ℕ × ℤ) : DisjInt (child0 J) (child1 J) := by
  have : cR (child0 J) = cL (child1 J) := by
    simp only [cR, cL, child0, child1, cellR, cellL]; push_cast; ring
  unfold DisjInt
  rw [Set.disjoint_left]
  rintro x ⟨-, h1⟩ ⟨h2, -⟩
  rw [this] at h1; linarith

lemma Ioo_subset_of_cC_subset {A B : ℕ × ℤ} (h : cC A ⊆ cC B) :
    Ioo (cL A) (cR A) ⊆ Ioo (cL B) (cR B) := by
  have hA := cellL_lt_cellR A.1 A.2
  have h1 := h ⟨le_rfl, hA.le⟩
  have h2 := h ⟨hA.le, le_rfl⟩
  exact Ioo_subset_Ioo h1.1 h2.2

section
variable (M : ℕ × ℤ → ℝ) (ε : ℝ)

lemma mem_refineCell {r : ℕ} {J L : ℕ × ℤ} (hL : L ∈ refineCell M ε r J) :
    J.1 ≤ L.1 ∧ L.1 ≤ J.1 + r ∧ cC L ⊆ cC J := by
  induction r generalizing J with
  | zero =>
    simp only [refineCell, List.mem_singleton] at hL; subst hL; simp
  | succ r ih =>
    simp only [refineCell] at hL
    split_ifs at hL with h
    · simp only [List.mem_singleton] at hL; subst hL; simp
    · rcases List.mem_append.1 hL with hL | hL
      · obtain ⟨a, b, c⟩ := ih hL
        simp only [child0] at a b
        exact ⟨by omega, by omega, c.trans (cC_child0 J)⟩
      · obtain ⟨a, b, c⟩ := ih hL
        simp only [child1] at a b
        exact ⟨by omega, by omega, c.trans (cC_child1 J)⟩

lemma length_refineCell (r : ℕ) (J : ℕ × ℤ) : (refineCell M ε r J).length ≤ 2 ^ r := by
  induction r generalizing J with
  | zero => simp [refineCell]
  | succ r ih =>
    simp only [refineCell]
    split_ifs
    · simp only [List.length_singleton]; exact Nat.one_le_two_pow
    · rw [List.length_append, pow_succ]; linarith [ih (child0 J), ih (child1 J)]

lemma pairwise_refineCell (r : ℕ) (J : ℕ × ℤ) : (refineCell M ε r J).Pairwise DisjInt := by
  induction r generalizing J with
  | zero => simp [refineCell]
  | succ r ih =>
    simp only [refineCell]
    split_ifs
    · simp
    · rw [List.pairwise_append]
      refine ⟨ih _, ih _, fun a ha b hb => ?_⟩
      have h1 := Ioo_subset_of_cC_subset (mem_refineCell M ε ha).2.2
      have h2 := Ioo_subset_of_cC_subset (mem_refineCell M ε hb).2.2
      exact Disjoint.mono h1 h2 (disjInt_children J)

lemma cover_refineCell (r : ℕ) (J : ℕ × ℤ) : cC J ⊆ ⋃ L ∈ refineCell M ε r J, cC L := by
  induction r generalizing J with
  | zero => simp [refineCell]
  | succ r ih =>
    simp only [refineCell]
    split_ifs
    · simp
    · intro x hx
      rw [cC_children] at hx
      simp only [List.mem_append, mem_iUnion, exists_prop]
      rcases hx with hx | hx
      · have := ih (child0 J) hx
        simp only [mem_iUnion, exists_prop] at this
        obtain ⟨L, hL, hxL⟩ := this
        exact ⟨L, Or.inl hL, hxL⟩
      · have := ih (child1 J) hx
        simp only [mem_iUnion, exists_prop] at this
        obtain ⟨L, hL, hxL⟩ := this
        exact ⟨L, Or.inr hL, hxL⟩

lemma cert_refineCell {r : ℕ} {J : ℕ × ℤ}
    (h : ∀ D : ℕ × ℤ, D.1 = J.1 + r → cC D ⊆ cC J → cert M D ≤ ε) :
    ∀ L ∈ refineCell M ε r J, cert M L ≤ ε := by
  induction r generalizing J with
  | zero =>
    intro L hL
    simp only [refineCell, List.mem_singleton] at hL; subst hL
    exact h L (by simp) subset_rfl
  | succ r ih =>
    intro L hL
    simp only [refineCell] at hL
    split_ifs at hL with hc
    · simp only [List.mem_singleton] at hL; subst hL; exact hc
    · rcases List.mem_append.1 hL with hL | hL
      · refine ih (fun D hD hsub => h D ?_ (hsub.trans (cC_child0 J))) L hL
        simp only [child0] at hD; omega
      · refine ih (fun D hD hsub => h D ?_ (hsub.trans (cC_child1 J))) L hL
        simp only [child1] at hD; omega

lemma refineCell_stable {r : ℕ} {J : ℕ × ℤ}
    (h : ∀ D : ℕ × ℤ, D.1 = J.1 + r → cC D ⊆ cC J → cert M D ≤ ε) (s : ℕ) :
    refineCell M ε (r + s) J = refineCell M ε r J := by
  induction r generalizing J with
  | zero =>
    have hc := h J (by simp) subset_rfl
    rcases s with _ | s
    · rfl
    · simp [refineCell, hc]
  | succ r ih =>
    rw [show r + 1 + s = (r + s) + 1 by ring]
    simp only [refineCell]
    split_ifs
    · rfl
    · rw [ih (J := child0 J) (fun D hD hsub => h D (by simp only [child0] at hD; omega)
          (hsub.trans (cC_child0 J))),
        ih (J := child1 J) (fun D hD hsub => h D (by simp only [child1] at hD; omega)
          (hsub.trans (cC_child1 J)))]

lemma mesh_add (a r : ℕ) : mesh (a + r) = mesh a * (1 / 2) ^ r := by
  simp only [mesh, pow_add, mul_inv, one_div, inv_pow]

/-- The key estimate: at depth `r*` below a root of width `≤ h₀`, every certificate is
`≤ ε_I`. -/
lemma cert_le_of_rStar {Mstar h0 : ℝ} (hM : ∀ J, M J ≤ Mstar) (hε : 0 < ε) {J0 : ℕ × ℤ}
    (hJ0 : mesh J0.1 ≤ h0) (D : ℕ × ℤ) (hD : D.1 = J0.1 + rStar h0 Mstar ε) :
    cert M D ≤ ε := by
  unfold cert
  have hm := mesh_pos D.1
  rcases le_or_gt Mstar 0 with hMs | hMs
  · have : mesh D.1 ^ 2 * M D ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_trans (hM D) hMs)
    linarith
  set r := rStar h0 Mstar ε
  have hh0 : 0 < h0 := lt_of_lt_of_le (mesh_pos _) hJ0
  set X := h0 ^ 2 * Mstar / (8 * ε)
  have hX : 0 < X := by positivity
  have hr : 1 / 2 * Real.logb 2 X ≤ r := by
    have h1 := Int.le_ceil (1 / 2 * Real.logb 2 X)
    have h2 : (⌈1 / 2 * Real.logb 2 X⌉ : ℝ) ≤ ((max 0 ⌈1 / 2 * Real.logb 2 X⌉).toNat : ℤ) := by
      exact_mod_cast le_trans (le_max_right _ _) (Int.self_le_toNat _)
    simp only [r, rStar]
    push_cast at h2 ⊢
    linarith
  have h4 : X ≤ 4 ^ r := by
    have : Real.logb 2 X ≤ ((2 * r : ℕ) : ℝ) := by push_cast; linarith
    rw [Real.logb_le_iff_le_rpow (by norm_num) hX, Real.rpow_natCast, pow_mul] at this
    norm_num at this; exact this
  have hmD : mesh D.1 ^ 2 ≤ h0 ^ 2 / 4 ^ r := by
    rw [hD, mesh_add, mul_pow, ← pow_mul, show (1 / 2 : ℝ) ^ (r * 2) = 1 / 4 ^ r by
      rw [one_div_pow, mul_comm, pow_mul]; norm_num]
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (mesh_pos _).le hJ0 2) (by positivity)
  have : mesh D.1 ^ 2 * M D ≤ h0 ^ 2 / 4 ^ r * Mstar := by
    rcases le_total 0 (M D) with hMD | hMD
    · exact mul_le_mul hmD (hM D) hMD (by positivity)
    · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) hMD) (by positivity)
  have h5 : h0 ^ 2 / 4 ^ r * Mstar ≤ 8 * ε := by
    have h4' : h0 ^ 2 * Mstar ≤ 8 * ε * 4 ^ r := by
      simp only [X] at h4; rw [div_le_iff₀ (by positivity)] at h4; linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; linarith
  linarith

end

/-- **Theorem 6.4 (termination and size).** With `M(J) ≤ M*` for every cell and roots of
width at most `h₀`, the refinement (run with `r*` levels) is stable — running it longer does
not change the output, i.e. the loop of step (iii) has terminated — every leaf satisfies
`η_cert ≤ ε_I`, no branch exceeds `r*` levels, and there are at most `R₀ 2^{r*}` leaves. -/
theorem refine_terminates (M : ℕ × ℤ → ℝ) {Mstar εI h0 : ℝ} (hM : ∀ J, M J ≤ Mstar)
    (hεI : 0 < εI) (roots : List (ℕ × ℤ)) (hh0 : ∀ J ∈ roots, mesh J.1 ≤ h0) :
    (∀ s, refineAll M εI roots (rStar h0 Mstar εI + s) = refineAll M εI roots (rStar h0 Mstar εI)) ∧
    (∀ L ∈ refineAll M εI roots (rStar h0 Mstar εI), cert M L ≤ εI) ∧
    (∀ L ∈ refineAll M εI roots (rStar h0 Mstar εI), ∃ J0 ∈ roots,
        J0.1 ≤ L.1 ∧ L.1 ≤ J0.1 + rStar h0 Mstar εI ∧ cC L ⊆ cC J0) ∧
    (refineAll M εI roots (rStar h0 Mstar εI)).length ≤ roots.length * 2 ^ rStar h0 Mstar εI := by
  refine ⟨fun s => ?_, fun L hL => ?_, fun L hL => ?_, ?_⟩
  · unfold refineAll
    apply List.flatMap_congr
    intro J hJ
    exact refineCell_stable M εI (fun D hD _ => cert_le_of_rStar M εI hM hεI (hh0 J hJ) D hD) s
  · simp only [refineAll, List.mem_flatMap] at hL
    obtain ⟨J, hJ, hL⟩ := hL
    exact cert_refineCell M εI (fun D hD _ => cert_le_of_rStar M εI hM hεI (hh0 J hJ) D hD) L hL
  · simp only [refineAll, List.mem_flatMap] at hL
    obtain ⟨J, hJ, hL⟩ := hL
    exact ⟨J, hJ, mem_refineCell M εI hL⟩
  · unfold refineAll
    rw [List.length_flatMap]
    calc (roots.map fun J => (refineCell M εI (rStar h0 Mstar εI) J).length).sum
        ≤ (roots.map fun _ => 2 ^ rStar h0 Mstar εI).sum :=
          List.sum_le_sum (fun J _ => length_refineCell M εI _ J)
      _ = roots.length * 2 ^ rStar h0 Mstar εI := by simp

lemma disjointInteriors_toFinset {l : List (ℕ × ℤ)} (h : l.Pairwise DisjInt) :
    DisjointInteriors l.toFinset := by
  intro J hJ J' hJ' hne
  rw [List.mem_toFinset] at hJ hJ'
  exact h.forall disjInt_symm hJ hJ' hne

lemma pairwise_refineAll (M : ℕ × ℤ → ℝ) (ε : ℝ) {roots : List (ℕ × ℤ)}
    (hroots : roots.Pairwise DisjInt) (r : ℕ) : (refineAll M ε roots r).Pairwise DisjInt := by
  unfold refineAll
  rw [List.pairwise_flatMap]
  refine ⟨fun J _ => pairwise_refineCell M ε r J, ?_⟩
  refine hroots.imp (fun {A B} hAB => fun x hx y hy => ?_)
  exact Disjoint.mono (Ioo_subset_of_cC_subset (mem_refineCell M ε hx).2.2)
    (Ioo_subset_of_cC_subset (mem_refineCell M ε hy).2.2) hAB

lemma cover_refineAll (M : ℕ × ℤ → ℝ) (ε : ℝ) (roots : List (ℕ × ℤ)) (r : ℕ) :
    (⋃ J ∈ roots, cC J) ⊆ ⋃ L ∈ (refineAll M ε roots r).toFinset, cC L := by
  intro x hx
  simp only [mem_iUnion, exists_prop] at hx
  obtain ⟨J, hJ, hxJ⟩ := hx
  have := cover_refineCell M ε r J hxJ
  simp only [mem_iUnion, exists_prop] at this ⊢
  obtain ⟨L, hL, hxL⟩ := this
  refine ⟨L, ?_, hxL⟩
  rw [List.mem_toFinset]
  simp only [refineAll, List.mem_flatMap]
  exact ⟨J, hJ, hL⟩

/-- Address uniqueness for the emitted atoms: the atom on a cell with a given line is unique
(a consequence of Theorem 3.5). -/
theorem atom_unique {n n' : ℕ} (hk : gK n = gK n') (hm : gM n = gM n')
    (hl : ∀ x, atomLine n x = atomLine n' x) : n = n' := by
  apply gen_injective
  have ha : coefA n = coefA n' := by have := hl 0; simpa [atomLine] using this
  have hb : coefB n = coefB n' := by have := hl 1; simp only [atomLine, mul_one] at this; linarith
  have hxL : xL n = xL n' := by unfold xL; rw [hk, hm]
  have hxR : xR n = xR n' := by unfold xR; rw [hk, hm]
  simp only [gen, cLo, dHi, hl, hxL, hxR, ha, hb]

/-- **Theorem 6.4 (correctness).** Under the validated-majorant contract (40)
`‖F''‖_{∞,J} ≤ M(J) ≤ M*`, steps (iv)–(v) of Algorithm 6.3 can be carried out — rational
nodal values within `ε_R` of `F` with distinct values at the two ends of every leaf exist —
and, for **any** such choice, the emitted interpolant is a continuous assembly
`g ∈ 𝒜([α,β])` whose leaf atoms have unique addresses and with
`‖f - g‖_∞ ≤ ε_I + ε_R` (equation (42)). -/
theorem refine_correct {f : ℝ → ℝ} {α β : ℝ} (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β))
    (M : ℕ × ℤ → ℝ) {Mstar εI εR h0 : ℝ}
    (hM : ∀ J, (∀ x ∈ cC J, |deriv (deriv (extF f α β)) x| ≤ M J) ∧ M J ≤ Mstar)
    (hεI : 0 < εI) (hεR : 0 < εR) (roots : List (ℕ × ℤ)) (hroots : roots.Pairwise DisjInt)
    (hcov : Icc α β ⊆ ⋃ J ∈ roots, cC J) (hh0 : ∀ J ∈ roots, mesh J.1 ≤ h0) :
    (∃ v : ℝ → ℚ, (∀ J ∈ refineAll M εI roots (rStar h0 Mstar εI),
        |(v (cL J) : ℝ) - extF f α β (cL J)| < εR ∧ |(v (cR J) : ℝ) - extF f α β (cR J)| < εR) ∧
      ∀ J ∈ refineAll M εI roots (rStar h0 Mstar εI), v (cL J) ≠ v (cR J)) ∧
    ∀ v : ℝ → ℚ, (∀ J ∈ refineAll M εI roots (rStar h0 Mstar εI),
        |(v (cL J) : ℝ) - extF f α β (cL J)| < εR ∧ |(v (cR J) : ℝ) - extF f α β (cR J)| < εR) →
      (∀ J ∈ refineAll M εI roots (rStar h0 Mstar εI), v (cL J) ≠ v (cR J)) →
      IsAssembly α β (cellInterp (refineAll M εI roots (rStar h0 Mstar εI)).toFinset
          (fun t => (v t : ℝ))) ∧
      (∀ J ∈ refineAll M εI roots (rStar h0 Mstar εI), ∃! n, gK n = J.1 ∧ gM n = J.2 ∧
          ∀ x, atomLine n x = lin J (fun t => (v t : ℝ)) x) ∧
      supNormOn (Icc α β) (fun x => f x - cellInterp (refineAll M εI roots (rStar h0 Mstar εI)).toFinset
          (fun t => (v t : ℝ)) x) ≤ εI + εR := by
  set leaves := refineAll M εI roots (rStar h0 Mstar εI)
  set Λ := leaves.toFinset
  have hΛ : DisjointInteriors Λ := disjointInteriors_toFinset (pairwise_refineAll M εI hroots _)
  have hcovΛ : Icc α β ⊆ ⋃ J ∈ Λ, cC J := hcov.trans (cover_refineAll M εI roots _)
  obtain ⟨-, hcert, -, -⟩ := refine_terminates M (fun J => (hM J).2) hεI roots hh0
  refine ⟨?_, fun v hv hne => ⟨?_, ?_, ?_⟩⟩
  · obtain ⟨v, hv, hinj⟩ := exists_rat_nodes (nodes Λ) (extF f α β) hεR
    refine ⟨v, fun J hJ => ?_, fun J hJ h => ?_⟩
    · have hJ' : J ∈ Λ := List.mem_toFinset.2 hJ
      exact ⟨hv _ (cL_mem_nodes hJ'), hv _ (cR_mem_nodes hJ')⟩
    · have hJ' : J ∈ Λ := List.mem_toFinset.2 hJ
      exact (cellL_lt_cellR J.1 J.2).ne (hinj (cL_mem_nodes hJ') (cR_mem_nodes hJ') h)
  · exact isAssembly_cellInterp hΛ hcovΛ v (fun J hJ => hne J (List.mem_toFinset.1 hJ))
  · intro J hJ
    obtain ⟨n, hk, hm, hn⟩ := lin_eq_atom J v (hne J hJ)
    refine ⟨n, ⟨hk, hm, fun x => (hn x).symm⟩, fun n' ⟨hk', hm', hn'⟩ => ?_⟩
    exact atom_unique (hk'.trans hk.symm) (hm'.trans hm.symm) (fun x => by rw [hn', hn])
  · refine supNormOn_le ⟨α, le_rfl, hαβ.le⟩ ?_
    intro x hx
    have hxU := hcovΛ hx
    simp only [mem_iUnion, exists_prop] at hxU
    obtain ⟨J, hJ, hxJ⟩ := hxU
    have hJl : J ∈ leaves := List.mem_toFinset.1 hJ
    have h1 : |extF f α β x - lin J (extF f α β) x| ≤ εI := by
      have := abs_interp_err_le (cellL_lt_cellR J.1 J.2) (hasDerivAt_extF hαβ hf)
        (hasDerivAt_extF1 hαβ hf) (M := M J)
        (fun t ht => by rw [← deriv2_extF hαβ hf]; exact (hM J).1 t ht) hxJ
      have hw := cell_width J
      simp only [cR, cL] at hw
      rw [hw] at this
      have := le_trans this (le_of_eq (by unfold cert; ring) |>.trans (hcert J hJl))
      exact this
    have h2 : |lin J (extF f α β) x - lin J (fun t => (v t : ℝ)) x| < εR := by
      rw [lin_sub]
      apply abs_lin_lt hxJ
      · rw [abs_sub_comm]; exact (hv J hJl).1
      · rw [abs_sub_comm]; exact (hv J hJl).2
    rw [cellInterp_eq hΛ _ hJ hxJ, ← extF_of_mem (f := f) hx]
    calc |extF f α β x - lin J (fun t => (v t : ℝ)) x|
        = |(extF f α β x - lin J (extF f α β) x) + (lin J (extF f α β) x - lin J (fun t => (v t : ℝ)) x)| := by
          ring_nf
      _ ≤ |extF f α β x - lin J (extF f α β) x| + |lin J (extF f α β) x - lin J (fun t => (v t : ℝ)) x| :=
          abs_add_le _ _
      _ ≤ εI + εR := by linarith

end Fase3
