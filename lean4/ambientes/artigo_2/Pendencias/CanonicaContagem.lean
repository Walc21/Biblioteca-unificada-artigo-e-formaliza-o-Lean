import Pendencias.Canonica

/-!
# Contagem de folhas da árvore separadora de quebras

Auxiliares para o item IV.5.2. As contagens usam as quebras distintas da forma
reduzida; a ligação entre a árvore separadora e a função realizada é separada.
-/

noncomputable section

namespace Pendencias.Marcada

open Artigo Finset Classical

/-- Quebras de `S` estritamente no interior de `J_{k,m}`, como no critério de subdivisão
da árvore `𝒯(S)` do TeX. O filtro apenas explicita o mesmo predicado de `canonShape`. -/
def interiorBreaks (S : Finset ℚ) (k : ℕ) (m : ℤ) : Finset ℚ :=
  S.filter fun τ ↦ cL k m < τ ∧ (τ : ℝ) < cR k m

/-- Ponto médio racional de `J_{k,m}`: a fronteira comum dos dois filhos diádicos.
É o ponto estrutural inserido por uma subdivisão na construção de `𝒯(S)` do TeX. -/
def splitPoint (k : ℕ) (m : ℤ) : ℚ := ((2 * m + 1 : ℤ) : ℚ) / 2 ^ (k + 1)

lemma splitPoint_cast (k : ℕ) (m : ℤ) :
    (splitPoint k m : ℝ) = cL (k + 1) (2 * m + 1) := by
  simp [splitPoint, cL]

lemma interiorBreaks_sub_children (S : Finset ℚ) (k : ℕ) (m : ℤ) :
    interiorBreaks S k m ⊆
      interiorBreaks S (k + 1) (2 * m) ∪
        interiorBreaks S (k + 1) (2 * m + 1) ∪ {splitPoint k m} := by
  intro τ hτ
  obtain ⟨hS, hL, hR⟩ := Finset.mem_filter.mp hτ
  rcases lt_trichotomy (τ : ℝ) (cL (k + 1) (2 * m + 1)) with h | h | h
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hS, by rwa [cL_child_left], by rwa [cR_child_left]⟩
  · apply Finset.mem_union_right
    apply Finset.mem_singleton.mpr
    exact_mod_cast h.trans (splitPoint_cast k m).symm
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨hS, h, by rwa [cR_child_right]⟩

lemma card_interiorBreaks_split (S : Finset ℚ) (k : ℕ) (m : ℤ) :
    (interiorBreaks S k m).card ≤
      (interiorBreaks S (k + 1) (2 * m)).card +
        (interiorBreaks S (k + 1) (2 * m + 1)).card + 1 := by
  calc
    _ ≤ (interiorBreaks S (k + 1) (2 * m) ∪
          interiorBreaks S (k + 1) (2 * m + 1) ∪ {splitPoint k m}).card :=
      Finset.card_le_card (interiorBreaks_sub_children S k m)
    _ ≤ (interiorBreaks S (k + 1) (2 * m) ∪
          interiorBreaks S (k + 1) (2 * m + 1)).card + 1 := by
      simpa using Finset.card_union_le
        (interiorBreaks S (k + 1) (2 * m) ∪
          interiorBreaks S (k + 1) (2 * m + 1)) {splitPoint k m}
    _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) 1

/-- Uma árvore que separa as quebras interiores precisa de pelo menos uma folha a mais
do que o número dessas quebras. Esta é a contagem inferior geométrica do TeX. -/
theorem leavesAvoid_card_le (S : Finset ℚ) (T : DShape) :
    ∀ (k : ℕ) (m : ℤ), LeavesAvoid S T k m →
      (interiorBreaks S k m).card + 1 ≤ T.numLeaves := by
  induction T with
  | leaf =>
      intro k m h
      have he : interiorBreaks S k m = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro τ hτ
        obtain ⟨hS, hi⟩ := Finset.mem_filter.mp hτ
        exact (leavesAvoid_leaf S k m).mp h τ hS hi
      simp [he, DShape.numLeaves]
  | node l r ihl ihr =>
      intro k m h
      obtain ⟨hl, hr⟩ := (leavesAvoid_node S l r k m).mp h
      have h1 := ihl _ _ hl
      have h2 := ihr _ _ hr
      have h3 := card_interiorBreaks_split S k m
      simp only [DShape.numLeaves]
      omega

/-- Carga de inserção de uma quebra: dentro de `J_{k,m}` ainda podem ser necessárias
`d(τ)-k` subdivisões para que ela vire fronteira; fora do interior a carga é zero.
Esta é a contagem por ancestrais da prova da cota superior no TeX. -/
def depthCharge (d : ℚ → ℕ) (τ : ℚ) (k : ℕ) (m : ℤ) : ℕ :=
  if cL k m < τ ∧ (τ : ℝ) < cR k m then d τ - k else 0

/-- Soma das cargas de inserção das quebras de `S`, usada para contar subdivisões da
árvore do TeX. Na raiz `[0,1]`, com todas as quebras interiores, é `∑τ∈S, d(τ)`. -/
def depthWeight (S : Finset ℚ) (d : ℚ → ℕ) (k : ℕ) (m : ℤ) : ℕ :=
  ∑ τ ∈ S, depthCharge d τ k m

lemma interior_depth_lt {τ : ℚ} {d k : ℕ} {m : ℤ} (hd : τ.den ∣ 2 ^ d)
    (hi : cL k m < τ ∧ (τ : ℝ) < cR k m) : k < d := by
  by_contra h
  exact not_interior_of_den_dvd (hd.trans (pow_dvd_pow 2 (by omega : d ≤ k))) m hi

lemma depthCharge_split (d : ℚ → ℕ) (τ : ℚ) (k : ℕ) (m : ℤ)
    (hd : τ.den ∣ 2 ^ d τ) :
    depthCharge d τ (k + 1) (2 * m) + depthCharge d τ (k + 1) (2 * m + 1) +
        (if cL k m < τ ∧ (τ : ℝ) < cR k m then 1 else 0) ≤
      depthCharge d τ k m := by
  have hml : cL k m < cL (k + 1) (2 * m + 1) := by
    simpa only [cL_child_left, cR_child_left] using cL_lt_cR (k + 1) (2 * m)
  have hmr : cL (k + 1) (2 * m + 1) < cR k m := by
    simpa only [cR_child_right] using cL_lt_cR (k + 1) (2 * m + 1)
  by_cases hl : cL k m < τ ∧ (τ : ℝ) < cL (k + 1) (2 * m + 1)
  · have hr : ¬ (cL (k + 1) (2 * m + 1) < τ ∧ (τ : ℝ) < cR k m) := by
      intro h; linarith [hl.2, h.1]
    have hi : cL k m < τ ∧ (τ : ℝ) < cR k m := ⟨hl.1, hl.2.trans hmr⟩
    have hdk := interior_depth_lt hd hi
    simp only [depthCharge, cL_child_left, cR_child_left, cR_child_right,
      if_pos hl, if_neg hr, if_pos hi]
    omega
  · by_cases hr : cL (k + 1) (2 * m + 1) < τ ∧ (τ : ℝ) < cR k m
    · have hi : cL k m < τ ∧ (τ : ℝ) < cR k m := ⟨hml.trans hr.1, hr.2⟩
      have hdk := interior_depth_lt hd hi
      simp only [depthCharge, cL_child_left, cR_child_left, cR_child_right,
        if_neg hl, if_pos hr, if_pos hi]
      omega
    · by_cases hi : cL k m < τ ∧ (τ : ℝ) < cR k m
      · have hdk := interior_depth_lt hd hi
        simp only [depthCharge, cL_child_left, cR_child_left, cR_child_right,
          if_neg hl, if_neg hr, if_pos hi]
        omega
      · simp only [depthCharge, cL_child_left, cR_child_left, cR_child_right,
          if_neg hl, if_neg hr, if_neg hi]
        omega

lemma depthWeight_split (S : Finset ℚ) (d : ℚ → ℕ) (k : ℕ) (m : ℤ)
    (hd : ∀ τ ∈ S, τ.den ∣ 2 ^ d τ)
    (hex : ∃ τ ∈ S, cL k m < τ ∧ (τ : ℝ) < cR k m) :
    depthWeight S d (k + 1) (2 * m) + depthWeight S d (k + 1) (2 * m + 1) + 1 ≤
      depthWeight S d k m := by
  have hsum := Finset.sum_le_sum fun τ hτ ↦ depthCharge_split d τ k m (hd τ hτ)
  simp only [Finset.sum_add_distrib] at hsum
  obtain ⟨τ, hτ, hi⟩ := hex
  have hone : 1 ≤ ∑ x ∈ S, (if cL k m < x ∧ (x : ℝ) < cR k m then 1 else 0 : ℕ) := by
    have h := Finset.single_le_sum (fun x (_ : x ∈ S) ↦
      Nat.zero_le (if cL k m < x ∧ (x : ℝ) < cR k m then 1 else 0)) hτ
    simpa only [if_pos hi] using h
  unfold depthWeight
  omega

/-- Cada subdivisão consome ao menos uma unidade da carga das quebras. Portanto a
árvore canônica tem no máximo uma folha mais a carga inicial. -/
theorem canonShape_numLeaves_le_weight (S : Finset ℚ) (f : ℚ → ℕ)
    (hf : ∀ τ ∈ S, τ.den ∣ 2 ^ f τ) :
    ∀ (d k : ℕ) (m : ℤ),
      (canonShape S d k m).numLeaves ≤ 1 + depthWeight S f k m := by
  intro d
  induction d with
  | zero => intro k m; simp [canonShape, DShape.numLeaves]
  | succ d ih =>
      intro k m
      unfold canonShape
      split_ifs with hex
      · have hl := ih (k + 1) (2 * m)
        have hr := ih (k + 1) (2 * m + 1)
        have hs := depthWeight_split S f k m hf hex
        simp only [DShape.numLeaves]
        omega
      · simp [DShape.numLeaves]

/-- As duas cotas explícitas de folhas da árvore `𝒯(S)` no TeX, para quebras distintas
diádicas em `(0,1)`. A profundidade reduzida é `log₂` do denominador reduzido, pois
`IsDyadic τ` afirma que esse denominador é uma potência de dois. -/
theorem canonShape_leaf_bounds (S : Finset ℚ)
    (hdy : ∀ τ ∈ S, IsDyadic τ)
    (hi : ∀ τ ∈ S, (0 : ℝ) < τ ∧ (τ : ℝ) < 1) :
    S.card + 1 ≤ (canonShape S (S.sup fun τ ↦ Nat.log 2 τ.den) 0 0).numLeaves ∧
      (canonShape S (S.sup fun τ ↦ Nat.log 2 τ.den) 0 0).numLeaves ≤
        1 + ∑ τ ∈ S, Nat.log 2 τ.den := by
  have hden : ∀ τ ∈ S, τ.den ∣ 2 ^ Nat.log 2 τ.den := by
    intro τ hτ
    obtain ⟨d, hd⟩ := hdy τ hτ
    rw [hd, Nat.log_pow (by norm_num)]
  have hmax : ∀ τ ∈ S, τ.den ∣ 2 ^ (0 + S.sup fun τ ↦ Nat.log 2 τ.den) := by
    intro τ hτ
    apply (hden τ hτ).trans
    apply pow_dvd_pow 2
    simpa using (Finset.le_sup (f := fun τ ↦ Nat.log 2 τ.den) hτ)
  have hfilter : interiorBreaks S 0 0 = S := by
    apply Finset.filter_true_of_mem
    intro τ hτ
    simpa [cL, cR] using hi τ hτ
  constructor
  · simpa only [hfilter] using leavesAvoid_card_le S _ 0 0
      (canonShape_no_interior S _ 0 0 hmax)
  · have hweight : depthWeight S (fun τ ↦ Nat.log 2 τ.den) 0 0 =
        ∑ τ ∈ S, Nat.log 2 τ.den := by
      apply Finset.sum_congr rfl
      intro τ hτ
      have hτi : cL 0 0 < τ ∧ (τ : ℝ) < cR 0 0 := by simpa [cL, cR] using hi τ hτ
      simp only [depthCharge, if_pos hτi, Nat.sub_zero]
    simpa only [hweight] using canonShape_numLeaves_le_weight S _ hden _ 0 0

end Pendencias.Marcada
