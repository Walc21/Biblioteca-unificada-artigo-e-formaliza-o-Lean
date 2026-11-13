module
public import RequestProject.Cells

/-!
# Section 4: continuous assemblies and density

Definition 4.1 (continuous assembly), Theorem 4.2 (density of assemblies) and the cell count
(23), together with the interpolation machinery reused in Sections 5 and 6.
-/

@[expose] public section

namespace Fase3

open Set

/-! ## Uniform norm on a set -/

/-- `‖u‖_{∞,K} = sup_{x ∈ K} |u x|`. -/
noncomputable def supNormOn (K : Set ℝ) (u : ℝ → ℝ) : ℝ := sSup ((fun x => |u x|) '' K)

lemma supNormOn_le {K : Set ℝ} {u : ℝ → ℝ} {c : ℝ} (hK : K.Nonempty) (h : ∀ x ∈ K, |u x| ≤ c) :
    supNormOn K u ≤ c :=
  csSup_le (hK.image _) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

lemma le_supNormOn {K : Set ℝ} {u : ℝ → ℝ} {c : ℝ} (h : ∀ x ∈ K, |u x| ≤ c) {x : ℝ}
    (hx : x ∈ K) : |u x| ≤ supNormOn K u :=
  le_csSup ⟨c, by rintro _ ⟨y, hy, rfl⟩; exact h y hy⟩ ⟨x, hx, rfl⟩

lemma supNormOn_nonneg {K : Set ℝ} {u : ℝ → ℝ} (hK : K.Nonempty) (hb : BddAbove ((fun x => |u x|) '' K)) :
    0 ≤ supNormOn K u := by
  obtain ⟨x, hx⟩ := hK
  exact le_trans (abs_nonneg (u x)) (le_csSup hb ⟨x, hx, rfl⟩)

/-! ## Cells as pairs and disjoint interiors -/

/-- Left endpoint of the cell `J = (k,m)`. -/
noncomputable abbrev cL (J : ℕ × ℤ) : ℝ := cellL J.1 J.2
/-- Right endpoint of the cell `J = (k,m)`. -/
noncomputable abbrev cR (J : ℕ × ℤ) : ℝ := cellR J.1 J.2
/-- The closed cell `J = (k,m)` as a set. -/
abbrev cC (J : ℕ × ℤ) : Set ℝ := cell J.1 J.2

/-- A finite family of dyadic cells with pairwise disjoint interiors. -/
def DisjointInteriors (Λ : Finset (ℕ × ℤ)) : Prop :=
  ∀ J ∈ Λ, ∀ J' ∈ Λ, J ≠ J' → Disjoint (Ioo (cL J) (cR J)) (Ioo (cL J') (cR J'))

/-- **Definition 4.1 (continuous assembly).** For `K = [α, β]`, `g ∈ 𝒜(K)` iff `g` is
continuous on `K` and there is a finite collection `Λ` of dyadic cells with disjoint interiors
whose union contains `K`, and addresses `n(J)` whose atom lives on the cell `J`, with
`g = ℓ_{n(J)}` on `J ∩ K`. (Agreement at shared boundaries is automatic since `g` is a
function.) -/
def IsAssembly (α β : ℝ) (g : ℝ → ℝ) : Prop :=
  ContinuousOn g (Icc α β) ∧
  ∃ Λ : Finset (ℕ × ℤ), DisjointInteriors Λ ∧ Icc α β ⊆ (⋃ J ∈ Λ, cC J) ∧
    ∃ addr : ℕ × ℤ → ℕ, ∀ J ∈ Λ, gK (addr J) = J.1 ∧ gM (addr J) = J.2 ∧
      ∀ x ∈ cC J ∩ Icc α β, g x = atomLine (addr J) x

/-- The modulus of continuity `ω(f; δ)` (equation (21)). -/
noncomputable def modCont (f : ℝ → ℝ) (K : Set ℝ) (δ : ℝ) : ℝ :=
  sSup {e | ∃ x ∈ K, ∃ y ∈ K, |x - y| ≤ δ ∧ e = |f x - f y|}

/-! ## Linear interpolation on a cell -/

/-- Linear interpolation between `(a, va)` and `(b, vb)`. -/
noncomputable def linInterp (a b va vb x : ℝ) : ℝ := va + (vb - va) / (b - a) * (x - a)

/-- The linear interpolant of nodal values `v` on the cell `J`. -/
noncomputable def lin (J : ℕ × ℤ) (v : ℝ → ℝ) (x : ℝ) : ℝ := linInterp (cL J) (cR J) (v (cL J)) (v (cR J)) x

lemma linInterp_left (a b va vb : ℝ) : linInterp a b va vb a = va := by simp [linInterp]

lemma linInterp_right (a b va vb : ℝ) (h : a ≠ b) : linInterp a b va vb b = vb := by
  unfold linInterp; field_simp [sub_ne_zero.2 h.symm]; ring

lemma lin_left (J : ℕ × ℤ) (v : ℝ → ℝ) : lin J v (cL J) = v (cL J) := linInterp_left _ _ _ _

lemma lin_right (J : ℕ × ℤ) (v : ℝ → ℝ) : lin J v (cR J) = v (cR J) :=
  linInterp_right _ _ _ _ (cellL_lt_cellR _ _).ne

lemma linInterp_convex (a b va vb x : ℝ) :
    linInterp a b va vb x = (1 - (x - a) / (b - a)) * va + ((x - a) / (b - a)) * vb := by
  unfold linInterp; ring

lemma abs_linInterp_le {a b va vb x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    |linInterp a b va vb x| ≤ max |va| |vb| := by
  rw [linInterp_convex a b va vb x]
  have hθ0 : 0 ≤ (x - a) / (b - a) := div_nonneg (by linarith [hx.1]) (by linarith)
  have hθ1 : (x - a) / (b - a) ≤ 1 := by rw [div_le_one (by linarith)]; linarith [hx.2]
  calc |(1 - (x - a) / (b - a)) * va + ((x - a) / (b - a)) * vb|
      ≤ (1 - (x - a) / (b - a)) * |va| + ((x - a) / (b - a)) * |vb| := by
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hθ0]
    _ ≤ (1 - (x - a) / (b - a)) * max |va| |vb| + ((x - a) / (b - a)) * max |va| |vb| := by
        gcongr
        · linarith
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = max |va| |vb| := by ring

lemma linInterp_sub (a b va vb wa wb x : ℝ) :
    linInterp a b va vb x - linInterp a b wa wb x = linInterp a b (va - wa) (vb - wb) x := by
  unfold linInterp; ring

lemma lin_sub (J : ℕ × ℤ) (v w : ℝ → ℝ) (x : ℝ) :
    lin J v x - lin J w x = lin J (fun t => v t - w t) x := linInterp_sub _ _ _ _ _ _ _

lemma abs_lin_le {J : ℕ × ℤ} {v : ℝ → ℝ} {x : ℝ} (hx : x ∈ cC J) :
    |lin J v x| ≤ max |v (cL J)| |v (cR J)| := abs_linInterp_le (cellL_lt_cellR _ _) hx

lemma abs_lin_lt {J : ℕ × ℤ} {v : ℝ → ℝ} {x c : ℝ} (hx : x ∈ cC J)
    (hL : |v (cL J)| < c) (hR : |v (cR J)| < c) : |lin J v x| < c :=
  lt_of_le_of_lt (abs_lin_le hx) (max_lt hL hR)

lemma abs_lin_le' {J : ℕ × ℤ} {v : ℝ → ℝ} {x c : ℝ} (hx : x ∈ cC J)
    (hL : |v (cL J)| ≤ c) (hR : |v (cR J)| ≤ c) : |lin J v x| ≤ c :=
  le_trans (abs_lin_le hx) (max_le hL hR)

lemma continuous_lin (J : ℕ × ℤ) (v : ℝ → ℝ) : Continuous (lin J v) := by
  unfold lin linInterp; fun_prop

/-! ## Interpolation on a family of cells -/

lemma common_point_endpoint {J J' : ℕ × ℤ} (hd : Disjoint (Ioo (cL J) (cR J)) (Ioo (cL J') (cR J')))
    {x : ℝ} (hx : x ∈ cC J) (hx' : x ∈ cC J') :
    (x = cR J ∧ x = cL J') ∨ (x = cL J ∧ x = cR J') := by
  have h1 := cellL_lt_cellR J.1 J.2
  have h2 := cellL_lt_cellR J'.1 J'.2
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hx1', hx2'⟩ := hx'
  rw [Set.disjoint_left] at hd
  by_cases hA : cR J ≤ cL J'
  · left; constructor <;> linarith
  by_cases hB : cR J' ≤ cL J
  · right; constructor <;> linarith
  exfalso
  push_neg at hA hB
  set lo := max (cL J) (cL J')
  set hi := min (cR J) (cR J')
  have hlh : lo < hi := by
    simp only [lo, hi, max_lt_iff, lt_min_iff]; exact ⟨⟨h1, hA⟩, hB, h2⟩
  have hm : (lo + hi) / 2 ∈ Ioo (cL J) (cR J) := by
    constructor
    · have : cL J ≤ lo := le_max_left _ _; linarith
    · have : hi ≤ cR J := min_le_left _ _; linarith
  have hm' : (lo + hi) / 2 ∈ Ioo (cL J') (cR J') := by
    constructor
    · have : cL J' ≤ lo := le_max_right _ _; linarith
    · have : hi ≤ cR J' := min_le_right _ _; linarith
  exact hd hm hm'

open Classical in
/-- The interpolant of nodal values `v` on the finite family of cells `Λ`. -/
noncomputable def cellInterp (Λ : Finset (ℕ × ℤ)) (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  if h : ∃ J ∈ Λ, x ∈ cC J then lin (Classical.choose h) v x else 0

lemma cellInterp_eq {Λ : Finset (ℕ × ℤ)} (hΛ : DisjointInteriors Λ) (v : ℝ → ℝ) {J : ℕ × ℤ}
    (hJ : J ∈ Λ) {x : ℝ} (hx : x ∈ cC J) : cellInterp Λ v x = lin J v x := by
  have h : ∃ J ∈ Λ, x ∈ cC J := ⟨J, hJ, hx⟩
  unfold cellInterp
  rw [dif_pos h]
  obtain ⟨hJ', hx'⟩ := Classical.choose_spec h
  set J' := Classical.choose h
  by_cases hEq : J' = J
  · rw [hEq]
  rcases common_point_endpoint (hΛ J' hJ' J hJ hEq) hx' hx with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, lin_right, ← e1, e2, lin_left]
  · rw [e1, lin_left, ← e1, e2, lin_right]

lemma cellInterp_continuousOn {Λ : Finset (ℕ × ℤ)} (hΛ : DisjointInteriors Λ) (v : ℝ → ℝ) :
    ContinuousOn (cellInterp Λ v) (⋃ J ∈ Λ, cC J) := by
  have : (⋃ J ∈ Λ, cC J) = ⋃ J : Λ, cC J.1 := by
    ext x; simp
  rw [this]
  apply LocallyFinite.continuousOn_iUnion (locallyFinite_of_finite _)
  · intro J; exact isClosed_Icc
  · intro J
    exact ((continuous_lin J.1 v).continuousOn).congr (fun x hx => cellInterp_eq hΛ v J.2 hx)

/-- Cellwise error transfer: if nodal values differ by at most `c` at every cell endpoint,
the interpolants differ by at most `c` on the union of the cells. -/
lemma cellInterp_sub_le {Λ : Finset (ℕ × ℤ)} (hΛ : DisjointInteriors Λ) (v w : ℝ → ℝ) {c : ℝ}
    (hc : ∀ J ∈ Λ, |v (cL J) - w (cL J)| ≤ c ∧ |v (cR J) - w (cR J)| ≤ c)
    {x : ℝ} (hx : x ∈ ⋃ J ∈ Λ, cC J) : |cellInterp Λ v x - cellInterp Λ w x| ≤ c := by
  simp only [mem_iUnion] at hx
  obtain ⟨J, hJ, hxJ⟩ := hx
  rw [cellInterp_eq hΛ v hJ hxJ, cellInterp_eq hΛ w hJ hxJ, lin_sub]
  exact abs_lin_le' hxJ (hc J hJ).1 (hc J hJ).2

/-! ## Rational nodal values and the assembly built from them -/

lemma exists_rat_avoiding (w δ : ℝ) (hδ : 0 < δ) (S : Finset ℚ) :
    ∃ q : ℚ, |(q : ℝ) - w| < δ ∧ q ∉ S := by
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show w - δ < w by linarith)
  obtain ⟨p', hp1', hp2'⟩ := exists_rat_btwn (show w < w + δ by linarith)
  have hpp : p < p' := by exact_mod_cast (lt_trans hp2 hp1')
  obtain ⟨q, hq, hqS⟩ := (Set.Ioo_infinite hpp).exists_notMem_finset S
  refine ⟨q, ?_, hqS⟩
  have h1 : (p : ℝ) < q := by exact_mod_cast hq.1
  have h2 : (q : ℝ) < p' := by exact_mod_cast hq.2
  rw [abs_lt]; constructor <;> linarith

/-- Rational nodal values within `δ` of prescribed values, injective on a finite set of nodes
(so in particular adjacent values are distinct). -/
lemma exists_rat_nodes (S : Finset ℝ) (w : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ v : ℝ → ℚ, (∀ t ∈ S, |(v t : ℝ) - w t| < δ) ∧ Set.InjOn v S := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨v, hv, hinj⟩ := ih
    obtain ⟨q, hq, hqS⟩ := exists_rat_avoiding (w a) δ hδ (S.image v)
    refine ⟨fun t => if t = a then q else v t, ?_, ?_⟩
    · intro t ht
      rcases Finset.mem_insert.1 ht with rfl | ht
      · simpa using hq
      · have : t ≠ a := fun h => ha (h ▸ ht)
        simpa [this] using hv t ht
    · intro s hs t ht hst
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hs ht
      rcases hs with rfl | hs <;> rcases ht with rfl | ht
      · rfl
      · have : t ≠ s := fun h => ha (h ▸ ht)
        simp [this] at hst
        exact absurd (Finset.mem_image.2 ⟨t, ht, hst.symm⟩) hqS
      · have : s ≠ t := fun h => ha (h ▸ hs)
        simp [this] at hst
        exact absurd (Finset.mem_image.2 ⟨s, hs, hst⟩) hqS
      · have h1 : s ≠ a := fun h => ha (h ▸ hs)
        have h2 : t ≠ a := fun h => ha (h ▸ ht)
        simp [h1, h2] at hst
        exact hinj hs ht hst

/-- The endpoints of the cells of `Λ`. -/
noncomputable def nodes (Λ : Finset (ℕ × ℤ)) : Finset ℝ := Λ.image cL ∪ Λ.image cR

lemma cL_mem_nodes {Λ : Finset (ℕ × ℤ)} {J : ℕ × ℤ} (hJ : J ∈ Λ) : cL J ∈ nodes Λ :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ hJ)

lemma cR_mem_nodes {Λ : Finset (ℕ × ℤ)} {J : ℕ × ℤ} (hJ : J ∈ Λ) : cR J ∈ nodes Λ :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ hJ)

/-- On a single cell, the interpolant of rational values with distinct endpoints is an atom. -/
lemma lin_eq_atom (J : ℕ × ℤ) (v : ℝ → ℚ) (hne : v (cL J) ≠ v (cR J)) :
    ∃ n, gK n = J.1 ∧ gM n = J.2 ∧ ∀ x, lin J (fun t => (v t : ℝ)) x = atomLine n x := by
  have hs : (v (cR J) - v (cL J)) * 2 ^ J.1 ≠ 0 :=
    mul_ne_zero (sub_ne_zero.2 hne.symm) (by positivity)
  obtain ⟨n, hk, hm, hn⟩ := exists_atom J.1 J.2 ((v (cL J) + v (cR J)) / 2)
    ((v (cR J) - v (cL J)) * 2 ^ J.1) hs
  refine ⟨n, hk, hm, fun x => ?_⟩
  rw [hn]
  unfold lin linInterp
  rw [center_eq]
  simp only [cL, cR]
  rw [cellR_sub_cellL]
  push_cast
  have : cellR J.1 J.2 = cellL J.1 J.2 + 1 / 2 ^ J.1 := by rw [← cellR_sub_cellL]; ring
  rw [this]
  field_simp
  ring

/-- **Assembly builder.** Rational nodal values with distinct endpoint values on each cell of a
finite dyadic cover with disjoint interiors give a continuous assembly. -/
theorem isAssembly_cellInterp {α β : ℝ} {Λ : Finset (ℕ × ℤ)} (hΛ : DisjointInteriors Λ)
    (hcov : Icc α β ⊆ ⋃ J ∈ Λ, cC J) (v : ℝ → ℚ) (hne : ∀ J ∈ Λ, v (cL J) ≠ v (cR J)) :
    IsAssembly α β (cellInterp Λ (fun t => (v t : ℝ))) := by
  classical
  refine ⟨(cellInterp_continuousOn hΛ _).mono hcov, Λ, hΛ, hcov, ?_⟩
  have hex : ∀ J, ∃ n, J ∈ Λ → gK n = J.1 ∧ gM n = J.2 ∧
      ∀ x, lin J (fun t => (v t : ℝ)) x = atomLine n x := by
    intro J
    by_cases hJ : J ∈ Λ
    · obtain ⟨n, h⟩ := lin_eq_atom J v (hne J hJ)
      exact ⟨n, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hJ⟩
  choose addr haddr using hex
  refine ⟨addr, fun J hJ => ⟨(haddr J hJ).1, (haddr J hJ).2.1, fun x hx => ?_⟩⟩
  rw [cellInterp_eq hΛ _ hJ hx.1, (haddr J hJ).2.2]

/-- **Rationalisation.** Given a finite dyadic cover with disjoint interiors and real nodal
values `w`, there is an assembly within `δ` of the real interpolant on `[α, β]`. -/
theorem exists_assembly_near {α β : ℝ} {Λ : Finset (ℕ × ℤ)} (hΛ : DisjointInteriors Λ)
    (hcov : Icc α β ⊆ ⋃ J ∈ Λ, cC J) (w : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ g, IsAssembly α β g ∧ ∀ x ∈ Icc α β, |g x - cellInterp Λ w x| < δ := by
  obtain ⟨v, hv, hinj⟩ := exists_rat_nodes (nodes Λ) w (half_pos hδ)
  have hne : ∀ J ∈ Λ, v (cL J) ≠ v (cR J) := by
    intro J hJ h
    have := hinj (cL_mem_nodes hJ) (cR_mem_nodes hJ) h
    exact (cellL_lt_cellR J.1 J.2).ne this
  refine ⟨_, isAssembly_cellInterp hΛ hcov v hne, fun x hx => ?_⟩
  have := cellInterp_sub_le hΛ (fun t => (v t : ℝ)) w (c := δ / 2)
    (fun J hJ => ⟨(hv _ (cL_mem_nodes hJ)).le, (hv _ (cR_mem_nodes hJ)).le⟩) (hcov hx)
  linarith

/-! ## The uniform cover of scale `k` and its cell count (equation (23)) -/

/-- The cells `J_{k,j}`, `⌊α 2^k⌋ ≤ j < ⌈β 2^k⌉`, of the uniform cover of `[α, β]`. -/
noncomputable def uniformCover (α β : ℝ) (k : ℕ) : Finset (ℕ × ℤ) :=
  (Finset.Ico ⌊α * 2 ^ k⌋ ⌈β * 2 ^ k⌉).image (fun j => (k, j))

/-- `N_k = ⌈β 2^k⌉ - ⌊α 2^k⌋` (equation (23)). -/
noncomputable def numCells (α β : ℝ) (k : ℕ) : ℤ := ⌈β * 2 ^ k⌉ - ⌊α * 2 ^ k⌋

lemma uniformCover_disjoint (α β : ℝ) (k : ℕ) : DisjointInteriors (uniformCover α β k) := by
  intro J hJ J' hJ' hne
  simp only [uniformCover, Finset.mem_image] at hJ hJ'
  obtain ⟨j, -, rfl⟩ := hJ
  obtain ⟨j', -, rfl⟩ := hJ'
  have hjj : j ≠ j' := fun h => hne (by rw [h])
  rw [Set.disjoint_left]
  rintro x ⟨h1, h2⟩ ⟨h1', h2'⟩
  simp only [cL, cR, cellL, cellR] at h1 h2 h1' h2'
  rw [div_lt_iff₀ (by positivity)] at h1 h1'
  rw [lt_div_iff₀ (by positivity)] at h2 h2'
  have a1 : (j : ℝ) < j' + 1 := by linarith
  have a2 : (j' : ℝ) < j + 1 := by linarith
  have b1 : j < j' + 1 := by exact_mod_cast a1
  have b2 : j' < j + 1 := by exact_mod_cast a2
  omega

lemma uniformCover_cover {α β : ℝ} (hαβ : α < β) (k : ℕ) :
    Icc α β ⊆ ⋃ J ∈ uniformCover α β k, cC J := by
  intro x hx
  simp only [mem_iUnion, uniformCover, Finset.mem_image, Finset.mem_Ico]
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hxa : α * 2 ^ k ≤ x * 2 ^ k := by nlinarith [hx.1]
  have hxb : x * 2 ^ k ≤ β * 2 ^ k := by nlinarith [hx.2]
  have hab : α * 2 ^ k < β * 2 ^ k := by nlinarith
  by_cases h : x * 2 ^ k < ⌈β * 2 ^ k⌉
  · refine ⟨(k, ⌊x * 2 ^ k⌋), ⟨⌊x * 2 ^ k⌋, ⟨Int.floor_mono hxa, ?_⟩, rfl⟩, ?_⟩
    · exact Int.floor_lt.2 h
    · simp only [cC, cell, cellL, cellR, mem_Icc]
      rw [div_le_iff₀ hp, le_div_iff₀ hp]
      exact ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
  · push_neg at h
    have heq : x * 2 ^ k = ⌈β * 2 ^ k⌉ := le_antisymm (le_trans hxb (Int.le_ceil _)) h
    refine ⟨(k, ⌈β * 2 ^ k⌉ - 1), ⟨⌈β * 2 ^ k⌉ - 1, ⟨?_, by omega⟩, rfl⟩, ?_⟩
    · have : ⌊α * 2 ^ k⌋ < ⌈β * 2 ^ k⌉ := by
        rw [Int.floor_lt]; exact lt_of_lt_of_le hab (Int.le_ceil _)
      omega
    · simp only [cC, cell, cellL, cellR, mem_Icc]
      rw [div_le_iff₀ hp, le_div_iff₀ hp]
      push_cast
      constructor <;> linarith

/-- **Equation (23).** `N_k = (β - α) 2^k + O(1)`; precisely `(β-α)2^k ≤ N_k < (β-α)2^k + 2`,
and `N_k` is the number of cells of the uniform cover. -/
theorem numCells_bounds (α β : ℝ) (k : ℕ) :
    (β - α) * 2 ^ k ≤ numCells α β k ∧ (numCells α β k : ℝ) < (β - α) * 2 ^ k + 2 := by
  unfold numCells
  push_cast
  have h1 := Int.le_ceil (β * 2 ^ k)
  have h2 := Int.floor_le (α * 2 ^ k)
  have h3 := Int.ceil_lt_add_one (β * 2 ^ k)
  have h4 := Int.lt_floor_add_one (α * 2 ^ k)
  constructor <;> nlinarith

theorem card_uniformCover (α β : ℝ) (k : ℕ) :
    ((uniformCover α β k).card : ℤ) = max (numCells α β k) 0 := by
  unfold uniformCover numCells
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h), Int.card_Ico]
  omega

/-! ## Theorem 4.2: density of assemblies -/

/-- Clamping to `[α, β]`, used for the extension by constants. -/
noncomputable def clamp (α β x : ℝ) : ℝ := max α (min x β)

lemma clamp_mem {α β : ℝ} (h : α ≤ β) (x : ℝ) : clamp α β x ∈ Icc α β :=
  ⟨le_max_left _ _, max_le h (min_le_right _ _)⟩

lemma clamp_of_mem {α β x : ℝ} (hx : x ∈ Icc α β) : clamp α β x = x := by
  unfold clamp; rw [min_eq_left hx.2, max_eq_right hx.1]

lemma abs_clamp_sub_le (α β x y : ℝ) : |clamp α β x - clamp α β y| ≤ |x - y| := by
  unfold clamp
  rw [max_comm α, max_comm α]
  exact le_trans (abs_max_sub_max_le_abs _ _ _) (abs_inf_sub_inf_le_abs x y β)

lemma continuous_clamp (α β : ℝ) : Continuous (clamp α β) := by
  unfold clamp; fun_prop

/-- **Theorem 4.2 (density of assemblies).** For every `f ∈ C[α, β]` and `ε > 0` there is an
assembly `g ∈ 𝒜([α, β])` with `‖f - g‖_{∞,[α,β]} < ε`; by construction all its pieces are
atoms of `𝓛` (with nonzero slope). -/
theorem assembly_dense {α β : ℝ} (hαβ : α < β) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc α β))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g, IsAssembly α β g ∧ supNormOn (Icc α β) (fun x => f x - g x) < ε := by
  set F := fun x => f (clamp α β x)
  have huc : UniformContinuousOn f (Icc α β) := isCompact_Icc.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδf⟩ := huc (ε / 4) (by linarith)
  have hFuc : ∀ x y, |x - y| < δ → |F x - F y| < ε / 4 := by
    intro x y hxy
    have := hδf _ (clamp_mem hαβ.le x) _ (clamp_mem hαβ.le y)
      (by rw [Real.dist_eq]; exact lt_of_le_of_lt (abs_clamp_sub_le _ _ _ _) hxy)
    rwa [Real.dist_eq] at this
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  set Λ := uniformCover α β k
  have hΛ := uniformCover_disjoint α β k
  have hcov := uniformCover_cover hαβ k
  obtain ⟨g, hg, hgclose⟩ := exists_assembly_near hΛ hcov F (show 0 < ε / 4 by linarith)
  refine ⟨g, hg, lt_of_le_of_lt (supNormOn_le ⟨α, le_refl α, hαβ.le⟩ (c := 3 * ε / 4) ?_) (by linarith)⟩
  intro x hx
  have hxU := hcov hx
  simp only [mem_iUnion] at hxU
  obtain ⟨J, hJ, hxJ⟩ := hxU
  have hlen : cR J - cL J < δ := by
    simp only [uniformCover, Finset.mem_image] at hJ
    obtain ⟨j, -, rfl⟩ := hJ
    simp only [cR, cL]; rw [cellR_sub_cellL, ← one_div_pow]; exact hk
  have hPF : |F x - cellInterp Λ F x| < ε / 4 := by
    rw [cellInterp_eq hΛ F hJ hxJ]
    have : F x - lin J F x = lin J (fun t => F x - F t) x := by
      unfold lin linInterp; ring
    rw [this]
    apply abs_lin_lt hxJ
    · apply hFuc; rw [abs_lt]; constructor <;> linarith [hxJ.1, hxJ.2]
    · apply hFuc; rw [abs_lt]; constructor <;> linarith [hxJ.1, hxJ.2]
  have hFx : F x = f x := by simp [F, clamp_of_mem hx]
  have h2 := hgclose x hx
  rw [hFx] at hPF
  calc |f x - g x| = |(f x - cellInterp Λ F x) - (g x - cellInterp Λ F x)| := by ring_nf
    _ ≤ |f x - cellInterp Λ F x| + |g x - cellInterp Λ F x| := abs_sub _ _
    _ ≤ 3 * ε / 4 := by linarith

end Fase3
