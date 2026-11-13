import Pendencias.Inversa

/-!
# IV.5.9 — Agudeza por um pente de tendas

-- ITEM: IV.5.9

Formalização do Teorema IV.5.9 (`\label{map:artigo_3:5.9}`,
`\label{artigo_3:thm:critical-tent-comb}` em `tex/partes/artigo_3.tex`):

Para todo `0 < α ≤ γ`, com `θ* = α / (α + γ)`, existem `f ∈ C([0,1])` e uma constante `C > 0`
tais que, na **biblioteca original** (`Pendencias.Agenda.pErr`, átomos `Artigo.Atom` com
inclinação `s ≠ 0` em `Artigo.LTree`) sob a agenda `H(N) = ⌈C N^γ⌉`:
1. `e_N^{𝓛,H}(f) ≤ C N^{-α}` para todo `N ≥ 1` (`critical_tent_comb`);
2. `f ∉ B^θ_{∞,∞}([0,1])` (`¬ BesovInf θ f`) para todo `θ > θ*`;
3. `f ∉ B^{θ*}_{∞,r}([0,1])` (`¬ BesovQ θ* r f`) para todo `0 < r < ∞`.

## Correspondência com as definições do TeX

* `tent a b h`: função tenda contínua em `ℝ`, nula fora de `(a, b)`, de altura `h` no ponto médio
  `(a+b)/2` e afim em cada metade `[a, (a+b)/2]` e `[(a+b)/2, b]`. Corresponde às tendas
  originais `φ_j` (em `J_{r_j, 1}`, altura `2^{-a_j}`) e às pequenas tendas perturbadoras `ψ_{J,j}`
  (altura `δ_j = 2^{-a_{j+1}-2}`).
* `tentTree d m h hh`: árvore diádica de duas folhas (`LTree.node` de dois `Atom.ofEndpoints`)
  sobre a célula `J_{d,m}`, com valores extremos nulos, valor médio `h ≠ 0` e inclinações
  `± 2^{d+1} h ≠ 0`. Pertence à biblioteca original `𝓛` (sem átomos marcados).
* `aSeq α J₀ j = ⌈J₀ α j⌉₊`, `bSeq γ J₀ j = ⌊J₀ γ j⌋₊`, `rSeq α γ J₀ j = a_j + b_j - 1`:
  sequências da demonstração no TeX.
* `combFun α γ J₀`: soma `∑_{j ≥ 1} φ_j` (indexada como `∑' n, phi (n + 1)`), contínua em `ℝ`
  (e em particular em `[0,1]`).
* `combFrom α γ J₀ j k`: subárvore do pente refinado enraizada em `J_{k,0}` (`0 ≤ k ≤ r_j`),
  que isola cada `J_{d,1}` (`k < d ≤ r_j`) e a folha profunda `J_{r_j,0}` com uma `tentTree`,
  colocando `φ_i` quando `d = r_i` (`1 ≤ i ≤ j`) e `ψ_{J,j}` de altura `δ_j` nas folhas planas.
  Em `k = 0`, possui `2 r_j + 2` folhas e todas as inclinações não nulas.
-/

namespace Pendencias.PenteGemini

open Set Artigo LTree Pendencias Pendencias.Agenda

/-! ## 1. Tenda contínua e árvore de tenda em `LTree` -/

/-- Tenda contínua suportada em `[a, b]` com valor `h` no ponto médio `(a + b) / 2` e nula fora
de `(a, b)` (corresponde às tendas `φ_j` e `ψ_{J,j}` do TeX). -/
noncomputable def tent (a b h : ℝ) (x : ℝ) : ℝ :=
  h * max 0 (1 - |2 * x - (a + b)| / (b - a))

lemma tent_continuous (a b h : ℝ) : Continuous (tent a b h) := by
  unfold tent
  refine continuous_const.mul (continuous_const.max (continuous_const.sub ?_))
  exact (((continuous_const.mul continuous_id).sub continuous_const).abs).div_const _

lemma tent_nonneg {a b h : ℝ} (hh : 0 ≤ h) (x : ℝ) : 0 ≤ tent a b h x :=
  mul_nonneg hh (le_max_left _ _)

lemma tent_le {a b h : ℝ} (hh : 0 ≤ h) (hab : a < b) (x : ℝ) : tent a b h x ≤ h := by
  unfold tent
  have hden : 0 < b - a := sub_pos.mpr hab
  have h1 : 1 - |2 * x - (a + b)| / (b - a) ≤ 1 := by
    have : 0 ≤ |2 * x - (a + b)| / (b - a) := div_nonneg (abs_nonneg _) hden.le
    linarith
  have hmax : max 0 (1 - |2 * x - (a + b)| / (b - a)) ≤ 1 := max_le (by norm_num) h1
  calc h * max 0 (1 - |2 * x - (a + b)| / (b - a)) ≤ h * 1 := mul_le_mul_of_nonneg_left hmax hh
    _ = h := mul_one h

lemma tent_eq_zero_of_le {a b h x : ℝ} (hab : a < b) (hx : x ≤ a) : tent a b h x = 0 := by
  unfold tent
  have hden : 0 < b - a := sub_pos.mpr hab
  have habs : b - a ≤ |2 * x - (a + b)| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hle : 1 ≤ |2 * x - (a + b)| / (b - a) := (one_le_div hden).mpr habs
  rw [max_eq_left (by linarith), mul_zero]

lemma tent_eq_zero_of_ge {a b h x : ℝ} (hab : a < b) (hx : b ≤ x) : tent a b h x = 0 := by
  unfold tent
  have hden : 0 < b - a := sub_pos.mpr hab
  have habs : b - a ≤ |2 * x - (a + b)| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hle : 1 ≤ |2 * x - (a + b)| / (b - a) := (one_le_div hden).mpr habs
  rw [max_eq_left (by linarith), mul_zero]

lemma tent_midpoint (a b h : ℝ) : tent a b h ((a + b) / 2) = h := by
  unfold tent
  have : 2 * ((a + b) / 2) - (a + b) = 0 := by ring
  simp [this]

lemma tent_left_half {a b h x : ℝ} (hab : a < b) (ha : a ≤ x) (hm : x ≤ (a + b) / 2) :
    tent a b h x = 2 * h * (x - a) / (b - a) := by
  unfold tent
  have hden : 0 < b - a := sub_pos.mpr hab
  have hnonpos : 2 * x - (a + b) ≤ 0 := by linarith
  rw [abs_of_nonpos hnonpos]
  have hge : 0 ≤ 1 - -(2 * x - (a + b)) / (b - a) := by
    rw [sub_nonneg, div_le_one hden]
    linarith
  rw [max_eq_right hge]
  field_simp
  ring

lemma tent_right_half {a b h x : ℝ} (hab : a < b) (hm : (a + b) / 2 ≤ x) (hb : x ≤ b) :
    tent a b h x = 2 * h * (b - x) / (b - a) := by
  unfold tent
  have hden : 0 < b - a := sub_pos.mpr hab
  have hnonneg : 0 ≤ 2 * x - (a + b) := by linarith
  rw [abs_of_nonneg hnonneg]
  have hge : 0 ≤ 1 - (2 * x - (a + b)) / (b - a) := by
    rw [sub_nonneg, div_le_one hden]
    linarith
  rw [max_eq_right hge]
  field_simp
  ring

/-- Árvore diádica de duas folhas em `J_{d,m}` que realiza a tenda de altura racional `h ≠ 0`
no ponto médio e valores nulos nos extremos. Todos os átomos pertencem à biblioteca original `𝓛`. -/
def tentTree (d : ℕ) (m : ℤ) (h : ℚ) (hh : h ≠ 0) : LTree :=
  LTree.node
    (LTree.leaf (Atom.ofEndpoints (d + 1) (2 * m) 0 h hh.symm))
    (LTree.leaf (Atom.ofEndpoints (d + 1) (2 * m + 1) h 0 hh))

lemma tentTree_WF (d : ℕ) (m : ℤ) (h : ℚ) (hh : h ≠ 0) :
    LTree.WF d m (tentTree d m h hh) := by
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_⟩
  simp [LTree.rval, LTree.lval, Atom.ofEndpoints_rval, Atom.ofEndpoints_lval]

lemma tentTree_lval (d : ℕ) (m : ℤ) (h : ℚ) (hh : h ≠ 0) :
    (tentTree d m h hh).lval = 0 := by
  simp [tentTree, LTree.lval, Atom.ofEndpoints_lval]

lemma tentTree_rval (d : ℕ) (m : ℤ) (h : ℚ) (hh : h ≠ 0) :
    (tentTree d m h hh).rval = 0 := by
  simp [tentTree, LTree.rval, Atom.ofEndpoints_rval]

lemma tentTree_numLeaves (d : ℕ) (m : ℤ) (h : ℚ) (hh : h ≠ 0) :
    (tentTree d m h hh).numLeaves = 2 := by
  simp [tentTree, LTree.numLeaves, LTree.leaves]

lemma cL_mid_eq (d : ℕ) (m : ℤ) : cL (d + 1) (2 * m + 1) = (cL d m + cR d m) / 2 := by
  unfold cL cR
  push_cast
  rw [pow_succ]
  field_simp
  ring

lemma cell_len_eq (d : ℕ) (m : ℤ) : cR d m - cL d m = 1 / (2 : ℝ) ^ d := by
  unfold cL cR
  ring

lemma tentTree_eval (d : ℕ) (m : ℤ) (h : ℚ) (hh : h ≠ 0) {x : ℝ} (hx : x ∈ cellIcc d m) :
    (tentTree d m h hh).eval d m x = tent (cL d m) (cR d m) (h : ℝ) x := by
  have hab := cL_lt_cR d m
  have hmid := cL_mid_eq d m
  have hlen := cell_len_eq d m
  rw [cellIcc_eq] at hx
  simp only [tentTree, LTree.eval]
  split_ifs with hlt
  · rw [tent_left_half hab hx.1 (by linarith [hlt.le])]
    rw [Atom.eval_interp, Atom.ofEndpoints_lval, Atom.ofEndpoints_rval]
    have hk : (Atom.ofEndpoints (d + 1) (2 * m) 0 h hh.symm).k = d + 1 := rfl
    have hm : (Atom.ofEndpoints (d + 1) (2 * m) 0 h hh.symm).m = 2 * m := rfl
    rw [hk, hm, cL_child_left, hlen]
    push_cast
    rw [pow_succ]
    field_simp
    ring
  · rw [tent_right_half hab (by linarith [not_lt.mp hlt]) hx.2]
    rw [Atom.eval_interp, Atom.ofEndpoints_lval, Atom.ofEndpoints_rval]
    have hk : (Atom.ofEndpoints (d + 1) (2 * m + 1) h 0 hh).k = d + 1 := rfl
    have hm : (Atom.ofEndpoints (d + 1) (2 * m + 1) h 0 hh).m = 2 * m + 1 := rfl
    have hcR : cR d m = cL d m + 1 / (2 : ℝ) ^ d := by linarith [hlen]
    rw [hk, hm, hmid, hlen, hcR]
    push_cast
    rw [pow_succ]
    field_simp
    ring

lemma ht_pow2_inv (e : ℕ) : ht ((1 : ℚ) / 2 ^ e) ≤ 2 ^ e := by
  have h := ht_div_le 1 (2 ^ e) (by positivity)
  have hpow : (((2 ^ e : ℕ) : ℚ)) = (2 : ℚ) ^ e := by push_cast; rfl
  rw [← hpow]
  simpa using h.trans (max_le (Nat.one_le_two_pow) le_rfl)

lemma ht_pow2_div (d e : ℕ) :
    ht ((2 : ℚ) ^ d * ((1 : ℚ) / 2 ^ e)) ≤ if e ≤ d then 2 ^ (d - e) else 2 ^ (e - d) := by
  split_ifs with h
  · have heq : (2 : ℚ) ^ d * ((1 : ℚ) / 2 ^ e) = (((2 ^ (d - e) : ℕ) : ℤ) : ℚ) := by
      have : d = (d - e) + e := (Nat.sub_add_cancel h).symm
      conv_lhs => rw [this, pow_add]
      push_cast
      field_simp
    rw [heq, ht_intCast]
    exact max_le (by simp) Nat.one_le_two_pow
  · have hlt : d < e := Nat.lt_of_not_le h
    have heq : (2 : ℚ) ^ d * ((1 : ℚ) / 2 ^ e) = (1 : ℚ) / 2 ^ (e - d) := by
      have : e = (e - d) + d := (Nat.sub_add_cancel hlt.le).symm
      conv_lhs => rw [this, pow_add]
      field_simp
    rw [heq]
    exact ht_pow2_inv (e - d)

lemma tentTree_pow2_height (d e : ℕ) (hd : 1 ≤ d) {m : ℤ} (hm : m = 0 ∨ m = 1)
    (hq : (1 : ℚ) / 2 ^ e ≠ 0) :
    ∀ a ∈ (tentTree d m ((1 : ℚ) / 2 ^ e) hq).leaves,
      a.height ≤ max (max 4 (d + 2)) (max (2 ^ (e + 1)) (if e ≤ d + 1 then 2 ^ (d + 1 - e) else 2 ^
        (e - 2))) := by
  intro a ha
  have hm_bound : ∀ m' : ℤ, (m' = 2 * m ∨ m' = 2 * m + 1) → m'.natAbs + 1 ≤ 4 := by
    intro m' hm'
    rcases hm with rfl | rfl <;> rcases hm' with rfl | rfl <;> omega
  have hy0 : ht (((0 : ℚ) + (1 : ℚ) / 2 ^ e) / 2) ≤ 2 ^ (e + 1) := by
    have : ((0 : ℚ) + (1 : ℚ) / 2 ^ e) / 2 = (1 : ℚ) / 2 ^ (e + 1) := by
      rw [zero_add, pow_succ]; field_simp
    rw [this]
    exact ht_pow2_inv (e + 1)
  have hs : ht ((2 : ℚ) ^ (d + 1) * ((1 : ℚ) / 2 ^ e - 0)) ≤
      if e ≤ d + 1 then 2 ^ (d + 1 - e) else 2 ^ (e - 2) := by
    rw [sub_zero]
    refine (ht_pow2_div (d + 1) e).trans ?_
    split_ifs with h
    · exact le_rfl
    · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [tentTree, LTree.leaves, List.singleton_append, List.mem_cons, List.not_mem_nil,
    or_false] at ha
  rcases ha with rfl | rfl
  · rw [Atom.height_le_iff]
    refine ⟨by omega, by simp [Atom.ofEndpoints], ?_, ?_, ?_⟩
    · exact (hm_bound (2 * m) (Or.inl rfl)).trans (by omega)
    · exact hy0.trans (le_max_of_le_right (le_max_left _ _))
    · exact hs.trans (le_max_of_le_right (le_max_right _ _))
  · rw [Atom.height_le_iff]
    refine ⟨by omega, by simp [Atom.ofEndpoints], ?_, ?_, ?_⟩
    · exact (hm_bound (2 * m + 1) (Or.inr rfl)).trans (by omega)
    · have hmid_ht : ht (((1 : ℚ) / 2 ^ e + 0) / 2) = ht (((0 : ℚ) + (1 : ℚ) / 2 ^ e) / 2) := by
        congr 1; ring
      dsimp only [Atom.ofEndpoints]
      rw [hmid_ht]
      exact hy0.trans (le_max_of_le_right (le_max_left _ _))
    · have : (0 : ℚ) - (1 : ℚ) / 2 ^ e = -((1 : ℚ) / 2 ^ e - 0) := by ring
      simp only [Atom.ofEndpoints]
      rw [this, mul_neg, ht_neg]
      exact hs.trans (le_max_of_le_right (le_max_right _ _))

/-! ## 2. Escolha de `J₀` e das sequências `aⱼ, bⱼ, rⱼ` -/

lemma nat_sq_le_two_pow : ∀ k : ℕ, 4 ≤ k → k ^ 2 ≤ 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 : (k + 1) ^ 2 ≤ 2 * k ^ 2 := by nlinarith
    have h2 : (k + 1) ^ 2 ≤ 2 * 2 ^ k := h1.trans (Nat.mul_le_mul_left 2 ih)
    simpa [pow_succ'] using h2

lemma exists_J0 {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) :
    ∃ J₀ : ℕ, 2 ≤ J₀ ∧ 3 < (J₀ : ℝ) * (α + γ) ∧ 2 * (J₀ : ℝ) * (α + γ) + 2 ≤ (2 : ℝ) ^ J₀ := by
  have hsum : 0 < α + γ := by linarith
  set J₀ : ℕ := max 4 (⌈2 * (α + γ) + 2⌉₊ + ⌈3 / (α + γ)⌉₊ + 1)
  have hJ4 : 4 ≤ J₀ := le_max_left _ _
  have hJ_gt : 3 / (α + γ) < J₀ := by
    have h1 : 3 / (α + γ) ≤ ⌈3 / (α + γ)⌉₊ := Nat.le_ceil _
    have h2 : (⌈3 / (α + γ)⌉₊ : ℝ) + 1 ≤ J₀ := by
      exact_mod_cast le_trans (by omega) (le_max_right 4 (⌈2 * (α + γ) + 2⌉₊ + ⌈3 / (α + γ)⌉₊ + 1))
    linarith
  have hJ_lin : 2 * (α + γ) + 2 ≤ J₀ := by
    have h1 : 2 * (α + γ) + 2 ≤ ⌈2 * (α + γ) + 2⌉₊ := Nat.le_ceil _
    have h2 : (⌈2 * (α + γ) + 2⌉₊ : ℝ) ≤ J₀ := by
      exact_mod_cast le_trans (by omega) (le_max_right 4 (⌈2 * (α + γ) + 2⌉₊ + ⌈3 / (α + γ)⌉₊ + 1))
    linarith
  refine ⟨J₀, by omega, (div_lt_iff₀ hsum).mp hJ_gt, ?_⟩
  have hsq : (J₀ : ℝ) ^ 2 ≤ (2 : ℝ) ^ J₀ := by
    have := nat_sq_le_two_pow J₀ hJ4
    exact_mod_cast this
  have hJ1 : (1 : ℝ) ≤ J₀ := by exact_mod_cast (by omega : 1 ≤ J₀)
  calc 2 * (J₀ : ℝ) * (α + γ) + 2 ≤ (J₀ : ℝ) * (2 * (α + γ) + 2) := by nlinarith
    _ ≤ (J₀ : ℝ) * J₀ := mul_le_mul_of_nonneg_left hJ_lin (by positivity)
    _ = (J₀ : ℝ) ^ 2 := by ring
    _ ≤ (2 : ℝ) ^ J₀ := hsq

/-- Sequência `aⱼ = ⌈J₀ α j⌉` do TeX. -/
noncomputable def aSeq (α : ℝ) (J₀ j : ℕ) : ℕ := ⌈(J₀ : ℝ) * α * j⌉₊

/-- Sequência `bⱼ = ⌊J₀ γ j⌋` do TeX. -/
noncomputable def bSeq (γ : ℝ) (J₀ j : ℕ) : ℕ := ⌊(J₀ : ℝ) * γ * j⌋₊

/-- Sequência `rⱼ = aⱼ + bⱼ - 1` do TeX. -/
noncomputable def rSeq (α γ : ℝ) (J₀ j : ℕ) : ℕ := aSeq α J₀ j + bSeq γ J₀ j - 1

lemma aSeq_mono {α : ℝ} (hα : 0 ≤ α) (J₀ : ℕ) : Monotone (aSeq α J₀) := by
  intro i j hij
  apply Nat.ceil_mono
  have hJ0 : 0 ≤ (J₀ : ℝ) := Nat.cast_nonneg J₀
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  gcongr

section Sequences

variable {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) {J₀ : ℕ} (hJ₀ : 3 < (J₀ : ℝ) * (α + γ))

include hα hαγ hJ₀

lemma J0_pos_real : (0 : ℝ) < J₀ := by
  by_contra h
  have hle : (J₀ : ℝ) ≤ 0 := not_lt.mp h
  have : (J₀ : ℝ) * (α + γ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle (by linarith)
  linarith

lemma one_le_aSeq {j : ℕ} (hj : 1 ≤ j) : 1 ≤ aSeq α J₀ j := by
  have hJpos := J0_pos_real hα hαγ hJ₀
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hpos : 0 < (J₀ : ℝ) * α * j := by positivity
  exact Nat.one_le_iff_ne_zero.mpr (by
    intro h
    have := Nat.ceil_eq_zero.mp h
    linarith)

omit hα in
lemma one_le_bSeq {j : ℕ} (hj : 1 ≤ j) : 1 ≤ bSeq γ J₀ j := by
  have h1 : (1 : ℝ) ≤ (J₀ : ℝ) * γ := by nlinarith
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  exact Nat.le_floor (by push_cast; nlinarith)

lemma one_le_rSeq {j : ℕ} (hj : 1 ≤ j) : 1 ≤ rSeq α γ J₀ j := by
  have ha := one_le_aSeq hα hαγ hJ₀ hj
  have hb := one_le_bSeq hαγ hJ₀ hj
  unfold rSeq
  omega

lemma rSeq_add_two_le_succ {j : ℕ} (hj : 1 ≤ j) :
    rSeq α γ J₀ j + 2 ≤ rSeq α γ J₀ (j + 1) := by
  have hJpos := J0_pos_real hα hαγ hJ₀
  have ha := one_le_aSeq hα hαγ hJ₀ hj
  have hb := one_le_bSeq hαγ hJ₀ hj
  have ha' := one_le_aSeq hα hαγ hJ₀ (by omega : 1 ≤ j + 1)
  have hb' := one_le_bSeq hαγ hJ₀ (by omega : 1 ≤ j + 1)
  have h1 : (J₀ : ℝ) * α * ((j : ℝ) + 1) ≤ aSeq α J₀ (j + 1) := by
    simpa [aSeq] using Nat.le_ceil ((J₀ : ℝ) * α * ((j : ℝ) + 1))
  have h2 : (J₀ : ℝ) * γ * ((j : ℝ) + 1) - 1 < bSeq γ J₀ (j + 1) := by
    have := Nat.lt_floor_add_one ((J₀ : ℝ) * γ * ((j : ℝ) + 1))
    unfold bSeq
    push_cast
    linarith
  have h3 : (aSeq α J₀ j : ℝ) < (J₀ : ℝ) * α * j + 1 := by
    unfold aSeq
    exact Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg hJpos.le hα.le) (Nat.cast_nonneg j))
  have h4 : (bSeq γ J₀ j : ℝ) ≤ (J₀ : ℝ) * γ * j := by
    unfold bSeq
    exact Nat.floor_le (mul_nonneg (mul_nonneg hJpos.le (by linarith)) (Nat.cast_nonneg j))
  have hdiff : (1 : ℝ) < (aSeq α J₀ (j + 1) : ℝ) + bSeq γ J₀ (j + 1) - (aSeq α J₀ j + bSeq γ J₀ j)
    := by
    linarith
  have hnat : aSeq α J₀ j + bSeq γ J₀ j + 2 ≤ aSeq α J₀ (j + 1) + bSeq γ J₀ (j + 1) := by
    by_contra h
    have hle : aSeq α J₀ (j + 1) + bSeq γ J₀ (j + 1) ≤ aSeq α J₀ j + bSeq γ J₀ j + 1 := by omega
    have hleR : (aSeq α J₀ (j + 1) : ℝ) + bSeq γ J₀ (j + 1) ≤ (aSeq α J₀ j : ℝ) + bSeq γ J₀ j + 1 :=
      by
      exact_mod_cast hle
    linarith
  unfold rSeq
  omega

lemma rSeq_gap_of_lt {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) :
    rSeq α γ J₀ i + 2 ≤ rSeq α γ J₀ j := by
  induction j, hij using Nat.le_induction with
  | base => exact rSeq_add_two_le_succ hα hαγ hJ₀ hi
  | succ k hk ih =>
    exact ih.trans (by
      have := rSeq_add_two_le_succ hα hαγ hJ₀ (by omega : 1 ≤ k)
      omega)

lemma rSeq_strictMonoOn : ∀ {i j : ℕ}, 1 ≤ i → i < j → rSeq α γ J₀ i < rSeq α γ J₀ j :=
  fun hi hij => by have := rSeq_gap_of_lt hα hαγ hJ₀ hi hij; omega

lemma rSeq_ge_two_mul_sub_one {j : ℕ} (hj : 1 ≤ j) : 2 * j - 1 ≤ rSeq α γ J₀ j := by
  induction j, hj using Nat.le_induction with
  | base => simpa using one_le_rSeq hα hαγ hJ₀ le_rfl
  | succ k hk ih =>
    have := rSeq_add_two_le_succ hα hαγ hJ₀ hk
    omega

end Sequences

lemma pow_ge_mul {x : ℝ} (hx : 2 ≤ x) : ∀ j : ℕ, 1 ≤ j → x * j ≤ x ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [pow_succ']
    have hx0 : 0 ≤ x := by linarith
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have h2 : x ≤ x ^ k := by
      have : x = x * 1 := by ring
      nlinarith
    push_cast
    nlinarith

lemma two_rSeq_add_two_le {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) {J₀ : ℕ}
    (hJ₀ : 3 < (J₀ : ℝ) * (α + γ))
    (hJl : 2 * (J₀ : ℝ) * (α + γ) + 2 ≤ (2 : ℝ) ^ J₀) {j : ℕ} (hj : 1 ≤ j) :
    2 * rSeq α γ J₀ j + 2 ≤ 2 ^ (J₀ * j) := by
  have hJpos := J0_pos_real hα hαγ hJ₀
  have hr : (rSeq α γ J₀ j : ℝ) ≤ (J₀ : ℝ) * (α + γ) * j := by
    have ha1 : 1 ≤ aSeq α J₀ j := one_le_aSeq hα hαγ hJ₀ hj
    have hb1 : 1 ≤ bSeq γ J₀ j := one_le_bSeq hαγ hJ₀ hj
    have hcast : (rSeq α γ J₀ j : ℝ) = (aSeq α J₀ j : ℝ) + bSeq γ J₀ j - 1 := by
      unfold rSeq
      have hge : 1 ≤ aSeq α J₀ j + bSeq γ J₀ j := by omega
      rw [Nat.cast_sub hge, Nat.cast_add, Nat.cast_one]
    have ha : (aSeq α J₀ j : ℝ) < (J₀ : ℝ) * α * j + 1 := by
      unfold aSeq; exact Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg hJpos.le hα.le)
        (Nat.cast_nonneg j))
    have hb : (bSeq γ J₀ j : ℝ) ≤ (J₀ : ℝ) * γ * j := by
      unfold bSeq; exact Nat.floor_le (mul_nonneg (mul_nonneg hJpos.le (by linarith))
        (Nat.cast_nonneg j))
    linarith
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h2pow : (2 : ℝ) ≤ (2 : ℝ) ^ J₀ := by
    have hJ1 : 1 ≤ J₀ := by
      by_contra h
      have h0 : J₀ = 0 := by omega
      subst h0
      simp at hJpos
    have : (2 : ℕ) ≤ 2 ^ J₀ := Nat.le_self_pow (by omega) 2
    exact_mod_cast this
  have hbound : 2 * (rSeq α γ J₀ j : ℝ) + 2 ≤ (2 : ℝ) ^ (J₀ * j) := by
    calc 2 * (rSeq α γ J₀ j : ℝ) + 2
        ≤ 2 * ((J₀ : ℝ) * (α + γ) * j) + 2 := by linarith
      _ ≤ (2 * (J₀ : ℝ) * (α + γ) + 2) * j := by nlinarith
      _ ≤ (2 : ℝ) ^ J₀ * j := mul_le_mul_of_nonneg_right hJl (by positivity)
      _ ≤ ((2 : ℝ) ^ J₀) ^ j := pow_ge_mul h2pow j hj
      _ = (2 : ℝ) ^ (J₀ * j) := by rw [← pow_mul]
  exact_mod_cast hbound

/-! ## 3. Construção da função `combFun` e continuidade -/

/-- `j`-ésima tenda `φ_j` sobre `J_{r_j, 1}` de altura `2^{-a_j}`. -/
noncomputable def phi (α γ : ℝ) (J₀ j : ℕ) (x : ℝ) : ℝ :=
  tent (cL (rSeq α γ J₀ j) 1) (cR (rSeq α γ J₀ j) 1) ((2 : ℝ) ^ (-(aSeq α J₀ j : ℤ))) x

/-- Pente de tendas `f = ∑_{j ≥ 1} φ_j` do Teorema IV.5.9. -/
noncomputable def combFun (α γ : ℝ) (J₀ : ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, phi α γ J₀ (n + 1) x

lemma phi_nonneg (α γ : ℝ) (J₀ j : ℕ) (x : ℝ) : 0 ≤ phi α γ J₀ j x :=
  tent_nonneg (by positivity) x

lemma phi_le (α γ : ℝ) (J₀ j : ℕ) (x : ℝ) :
    phi α γ J₀ j x ≤ (2 : ℝ) ^ (-(aSeq α J₀ j : ℤ)) :=
  tent_le (by positivity) (cL_lt_cR _ _) x

lemma phi_eq_zero_of_not_mem {α γ : ℝ} {J₀ j : ℕ} {x : ℝ}
    (hx : x ∉ cellIcc (rSeq α γ J₀ j) 1) : phi α γ J₀ j x = 0 := by
  rw [cellIcc_eq, mem_Icc, not_and_or] at hx
  rcases hx with hx | hx
  · exact tent_eq_zero_of_le (cL_lt_cR _ _) (not_le.mp hx).le
  · exact tent_eq_zero_of_ge (cL_lt_cR _ _) (not_le.mp hx).le

lemma combFun_continuous {α γ : ℝ} (hα : 0 < α) {J₀ : ℕ} (hJ1 : 1 ≤ J₀) :
    Continuous (combFun α γ J₀) := by
  set q : ℝ := (2 : ℝ) ^ (-(J₀ : ℝ) * α)
  have hJpos : (0 : ℝ) < J₀ := by exact_mod_cast hJ1
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by nlinarith)
  refine continuous_tsum (fun n => tent_continuous _ _ _)
    ((summable_geometric_of_lt_one hq0.le hq1).comp_injective Nat.succ_injective)
    (fun n x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (phi_nonneg α γ J₀ (n + 1) x)]
  refine (phi_le α γ J₀ (n + 1) x).trans ?_
  have ha : (J₀ : ℝ) * α * ((n : ℝ) + 1) ≤ aSeq α J₀ (n + 1) := by
    simpa [aSeq] using Nat.le_ceil ((J₀ : ℝ) * α * ((n : ℝ) + 1))
  calc (2 : ℝ) ^ (-(aSeq α J₀ (n + 1) : ℤ))
      = (2 : ℝ) ^ (-(aSeq α J₀ (n + 1) : ℝ)) := by rw [← Real.rpow_intCast]; norm_cast
    _ ≤ (2 : ℝ) ^ (-((J₀ : ℝ) * α * ((n : ℝ) + 1))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = ((2 : ℝ) ^ (-(J₀ : ℝ) * α)) ^ (n + 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
        congr 1
        push_cast
        ring

lemma rSeq_cell_disjoint {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) {J₀ : ℕ}
    (hJ₀ : 3 < (J₀ : ℝ) * (α + γ)) {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (hne : i ≠ j)
    {x : ℝ} (hxi : x ∈ cellIcc (rSeq α γ J₀ i) 1) (hxj : x ∈ cellIcc (rSeq α γ J₀ j) 1) :
    False := by
  have order_disj : ∀ {u v : ℕ}, 1 ≤ u → u < v →
      x ∈ cellIcc (rSeq α γ J₀ u) 1 → x ∈ cellIcc (rSeq α γ J₀ v) 1 → False := by
    intro u v hu huv hxu hxv
    have hgap := rSeq_gap_of_lt hα hαγ hJ₀ hu huv
    rw [cellIcc_eq, mem_Icc] at hxu hxv
    have hR : cR (rSeq α γ J₀ v) 1 < cL (rSeq α γ J₀ u) 1 := by
      unfold cR cL
      push_cast
      have hpow : (2 : ℝ) ^ (rSeq α γ J₀ u + 2) ≤ (2 : ℝ) ^ (rSeq α γ J₀ v) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) hgap
      have h1 : (2 : ℝ) / (2 : ℝ) ^ (rSeq α γ J₀ v) ≤ 2 / (2 : ℝ) ^ (rSeq α γ J₀ u + 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
      have h2 : (2 : ℝ) / (2 : ℝ) ^ (rSeq α γ J₀ u + 2) = 1 / (2 * (2 : ℝ) ^ (rSeq α γ J₀ u)) := by
        rw [pow_add]; field_simp
      have h3 : (1 : ℝ) / (2 * (2 : ℝ) ^ (rSeq α γ J₀ u)) < 1 / (2 : ℝ) ^ (rSeq α γ J₀ u) := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        have : (0 : ℝ) < (2 : ℝ) ^ (rSeq α γ J₀ u) := by positivity
        linarith
      linarith
    linarith [hxu.1, hxv.2]
  rcases lt_or_gt_of_ne hne with h | h
  · exact order_disj hi h hxi hxj
  · exact order_disj hj h hxj hxi

lemma combFun_eq_phi {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) {J₀ : ℕ}
    (hJ₀ : 3 < (J₀ : ℝ) * (α + γ)) {j : ℕ} (hj : 1 ≤ j) {x : ℝ}
    (hx : x ∈ cellIcc (rSeq α γ J₀ j) 1) :
    combFun α γ J₀ x = phi α γ J₀ j x := by
  unfold combFun
  have hsingle : ∀ n : ℕ, n ≠ j - 1 → phi α γ J₀ (n + 1) x = 0 := by
    intro n hn
    apply phi_eq_zero_of_not_mem
    intro hmem
    exact rSeq_cell_disjoint hα hαγ hJ₀ (by omega) hj (by omega) hmem hx
  rw [tsum_eq_single (j - 1) hsingle, Nat.sub_add_cancel hj]

lemma combFun_nonneg (α γ : ℝ) (J₀ : ℕ) (x : ℝ) : 0 ≤ combFun α γ J₀ x :=
  tsum_nonneg fun n => phi_nonneg α γ J₀ (n + 1) x

lemma combFun_le_one {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) {J₀ : ℕ}
    (hJ₀ : 3 < (J₀ : ℝ) * (α + γ)) (x : ℝ) : combFun α γ J₀ x ≤ 1 := by
  by_cases hx : ∃ j : ℕ, 1 ≤ j ∧ x ∈ cellIcc (rSeq α γ J₀ j) 1
  · obtain ⟨j, hj, hxj⟩ := hx
    rw [combFun_eq_phi hα hαγ hJ₀ hj hxj]
    refine (phi_le α γ J₀ j x).trans ?_
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  · push_neg at hx
    have hzero : combFun α γ J₀ x = 0 := by
      unfold combFun
      have hf : ∀ n : ℕ, phi α γ J₀ (n + 1) x = 0 := fun n =>
        phi_eq_zero_of_not_mem (hx (n + 1) (by omega))
      simp only [hf, tsum_zero]
    linarith

lemma combFun_on_deep_leaf {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) {J₀ : ℕ}
    (hJ₀ : 3 < (J₀ : ℝ) * (α + γ)) {j : ℕ} (hj : 1 ≤ j) {x : ℝ}
    (hx : x ∈ cellIcc (rSeq α γ J₀ j) 0) :
    0 ≤ combFun α γ J₀ x ∧ combFun α γ J₀ x ≤ (2 : ℝ) ^ (-(aSeq α J₀ (j + 1) : ℤ)) := by
  refine ⟨combFun_nonneg α γ J₀ x, ?_⟩
  by_cases hmem : ∃ i : ℕ, 1 ≤ i ∧ x ∈ cellIcc (rSeq α γ J₀ i) 1
  · obtain ⟨i, hi, hxi⟩ := hmem
    rw [combFun_eq_phi hα hαγ hJ₀ hi hxi]
    by_cases hij : i ≤ j
    · have hri : rSeq α γ J₀ i ≤ rSeq α γ J₀ j := by
        rcases eq_or_lt_of_le hij with rfl | hlt
        · exact le_rfl
        · exact (rSeq_strictMonoOn hα hαγ hJ₀ hi hlt).le
      rw [cellIcc_eq, mem_Icc] at hx hxi
      have hpow : (2 : ℝ) ^ (rSeq α γ J₀ i) ≤ (2 : ℝ) ^ (rSeq α γ J₀ j) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num) hri
      have hle : cR (rSeq α γ J₀ j) 0 ≤ cL (rSeq α γ J₀ i) 1 := by
        unfold cR cL
        simp only [Int.cast_zero, zero_add, Int.cast_one]
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
      have hxe : x ≤ cL (rSeq α γ J₀ i) 1 := hx.2.trans hle
      have hphi0 : phi α γ J₀ i x = 0 := tent_eq_zero_of_le (cL_lt_cR _ _) hxe
      rw [hphi0]
      positivity
    · have hij' : j + 1 ≤ i := by omega
      refine (phi_le α γ J₀ i x).trans ?_
      have ha : aSeq α J₀ (j + 1) ≤ aSeq α J₀ i := aSeq_mono hα.le J₀ hij'
      rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
      exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.pow_le_pow_right (by norm_num) ha)
  · push_neg at hmem
    have hzero : combFun α γ J₀ x = 0 := by
      unfold combFun
      have hf : ∀ n : ℕ, phi α γ J₀ (n + 1) x = 0 := fun n =>
        phi_eq_zero_of_not_mem (hmem (n + 1) (by omega))
      simp only [hf, tsum_zero]
    rw [hzero]
    positivity

lemma combFun_eq_zero_on_flat {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) {J₀ : ℕ}
    (hJ₀ : 3 < (J₀ : ℝ) * (α + γ)) {j d : ℕ} (hj : 1 ≤ j) (_hd1 : 1 ≤ d)
    (hdj : d ≤ rSeq α γ J₀ j) (hnot : ∀ i : ℕ, 1 ≤ i → i ≤ j → rSeq α γ J₀ i ≠ d)
    {x : ℝ} (hx : x ∈ cellIcc d 1) :
    combFun α γ J₀ x = 0 := by
  unfold combFun
  have hterm : ∀ n : ℕ, phi α γ J₀ (n + 1) x = 0 := by
    intro n
    set i := n + 1
    have hne : rSeq α γ J₀ i ≠ d := by
      by_cases hij : i ≤ j
      · exact hnot i (by omega) hij
      · have hjlt : j < i := by omega
        have := rSeq_gap_of_lt hα hαγ hJ₀ hj hjlt
        omega
    rw [cellIcc_eq, mem_Icc] at hx
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `r_i < d`, logo `r_i + 1 ≤ d`, então `cR d 1 ≤ cL (r_i) 1`
      have hle : cR d 1 ≤ cL (rSeq α γ J₀ i) 1 := by
        have hpow : (2 : ℝ) ^ (rSeq α γ J₀ i + 1) ≤ (2 : ℝ) ^ d := by
          exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [show cR d 1 = 2 / (2 : ℝ) ^ d from by unfold cR; norm_num,
          show cL (rSeq α γ J₀ i) 1 = 1 / (2 : ℝ) ^ (rSeq α γ J₀ i) from by unfold cL; norm_num]
        calc (2 : ℝ) / (2 : ℝ) ^ d ≤ 2 / (2 : ℝ) ^ (rSeq α γ J₀ i + 1) :=
              div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
          _ = 1 / (2 : ℝ) ^ (rSeq α γ J₀ i) := by rw [pow_succ]; ring
      exact tent_eq_zero_of_le (cL_lt_cR _ _) (hx.2.trans hle)
    · -- `d < r_i`, logo `d + 1 ≤ r_i`, então `cR (r_i) 1 ≤ cL d 1`
      have hle : cR (rSeq α γ J₀ i) 1 ≤ cL d 1 := by
        have hpow : (2 : ℝ) ^ (d + 1) ≤ (2 : ℝ) ^ (rSeq α γ J₀ i) := by
          exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [show cR (rSeq α γ J₀ i) 1 = 2 / (2 : ℝ) ^ (rSeq α γ J₀ i) from by unfold cR; norm_num,
          show cL d 1 = 1 / (2 : ℝ) ^ d from by unfold cL; norm_num]
        calc (2 : ℝ) / (2 : ℝ) ^ (rSeq α γ J₀ i) ≤ 2 / (2 : ℝ) ^ (d + 1) :=
              div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
          _ = 1 / (2 : ℝ) ^ d := by rw [pow_succ]; ring
      exact tent_eq_zero_of_ge (cL_lt_cR _ _) (hle.trans hx.1)
  simp [hterm]

/-! ## 4. Construção do pente refinado em `LTree` e orçamentos -/

/-- Expoente da altura da tenda na célula `J_{d, 1}` para a montagem de ordem `j`:
`aᵢ` se `d = rᵢ` (`1 ≤ i ≤ j`), ou `a_{j+1} + 2` (correspondente a `δ_j`) caso contrário. -/
noncomputable def expAt (α γ : ℝ) (J₀ j d : ℕ) : ℕ :=
  letI := Classical.propDecidable
  if h : ∃ i ∈ Finset.Icc 1 j, rSeq α γ J₀ i = d then aSeq α J₀ (Classical.choose h)
  else aSeq α J₀ (j + 1) + 2

lemma expAt_eq_of_mem {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) {J₀ : ℕ}
    (hJ₀ : 3 < (J₀ : ℝ) * (α + γ)) {j i d : ℕ} (hi1 : 1 ≤ i) (hij : i ≤ j)
    (hd : rSeq α γ J₀ i = d) :
    expAt α γ J₀ j d = aSeq α J₀ i := by
  classical
  have hex : ∃ i' ∈ Finset.Icc 1 j, rSeq α γ J₀ i' = d := ⟨i, Finset.mem_Icc.mpr ⟨hi1, hij⟩, hd⟩
  have heq : expAt α γ J₀ j d = aSeq α J₀ (Classical.choose hex) := by
    unfold expAt
    rw [dif_pos hex]
  rw [heq]
  obtain ⟨hmem, hreq⟩ := Classical.choose_spec hex
  rw [Finset.mem_Icc] at hmem
  set i' := Classical.choose hex
  have hi'eq : i' = i := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (rSeq_strictMonoOn hα hαγ hJ₀ hmem.1 hlt).ne (hreq.trans hd.symm)
    · exact (rSeq_strictMonoOn hα hαγ hJ₀ hi1 hgt).ne (hd.trans hreq.symm)
  rw [hi'eq]

lemma expAt_eq_default (α γ : ℝ) (J₀ j d : ℕ)
    (hnot : ∀ i : ℕ, 1 ≤ i → i ≤ j → rSeq α γ J₀ i ≠ d) :
    expAt α γ J₀ j d = aSeq α J₀ (j + 1) + 2 := by
  classical
  have hnex : ¬ ∃ i ∈ Finset.Icc 1 j, rSeq α γ J₀ i = d := by
    rintro ⟨i, hi, hid⟩
    rw [Finset.mem_Icc] at hi
    exact hnot i hi.1 hi.2 hid
  unfold expAt
  rw [dif_neg hnex]

lemma expAt_bounds {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) {J₀ : ℕ}
    (hJ₀ : 3 < (J₀ : ℝ) * (α + γ)) (j d : ℕ) :
    1 ≤ expAt α γ J₀ j d ∧ expAt α γ J₀ j d ≤ aSeq α J₀ (j + 1) + 2 := by
  classical
  unfold expAt
  split_ifs with hex
  · obtain ⟨hmem, _⟩ := Classical.choose_spec hex
    rw [Finset.mem_Icc] at hmem
    exact ⟨one_le_aSeq hα hαγ hJ₀ hmem.1,
      (aSeq_mono hα.le J₀ (by omega : Classical.choose hex ≤ j + 1)).trans (by omega)⟩
  · exact ⟨by have := one_le_aSeq hα hαγ hJ₀ (by omega : 1 ≤ j + 1); omega, le_rfl⟩

/-- Subárvore do pente refinado (com inclinações não nulas em todas as folhas) enraizada em
`J_{k, 0}`, para `0 ≤ k ≤ r_j`. Em `k = 0` fornece a montagem `g_j` da biblioteca original `𝓛`. -/
noncomputable def combFrom (α γ : ℝ) (J₀ j k : ℕ) : LTree :=
  if _ : k < rSeq α γ J₀ j then
    let e := expAt α γ J₀ j (k + 1)
    let hq : (1 : ℚ) / 2 ^ e ≠ 0 := by positivity
    LTree.node (combFrom α γ J₀ j (k + 1)) (tentTree (k + 1) 1 ((1 : ℚ) / 2 ^ e) hq)
  else
    let e := aSeq α J₀ (j + 1) + 2
    let hq : (1 : ℚ) / 2 ^ e ≠ 0 := by positivity
    tentTree (rSeq α γ J₀ j) 0 ((1 : ℚ) / 2 ^ e) hq
termination_by rSeq α γ J₀ j - k

lemma combFrom_eq_node {α γ : ℝ} {J₀ j k : ℕ} (hk : k < rSeq α γ J₀ j) :
    combFrom α γ J₀ j k =
      LTree.node (combFrom α γ J₀ j (k + 1))
        (tentTree (k + 1) 1 ((1 : ℚ) / 2 ^ (expAt α γ J₀ j (k + 1))) (by positivity)) := by
  rw [combFrom, dif_pos hk]

lemma combFrom_eq_base {α γ : ℝ} {J₀ j : ℕ} :
    combFrom α γ J₀ j (rSeq α γ J₀ j) =
      tentTree (rSeq α γ J₀ j) 0 ((1 : ℚ) / 2 ^ (aSeq α J₀ (j + 1) + 2)) (by positivity) := by
  rw [combFrom, dif_neg (lt_irrefl _)]

lemma combFrom_spec (α γ : ℝ) (J₀ j : ℕ) :
    ∀ m k : ℕ, k ≤ rSeq α γ J₀ j → rSeq α γ J₀ j - k = m →
      LTree.WF k 0 (combFrom α γ J₀ j k) ∧
      (combFrom α γ J₀ j k).lval = 0 ∧
      (combFrom α γ J₀ j k).rval = 0 ∧
      (combFrom α γ J₀ j k).numLeaves = 2 * (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro k hk hsub
    obtain rfl : k = rSeq α γ J₀ j := by omega
    rw [combFrom_eq_base]
    exact ⟨tentTree_WF _ _ _ _, tentTree_lval _ _ _ _, tentTree_rval _ _ _ _,
      by simpa using tentTree_numLeaves _ _ _ _⟩
  | succ m ih =>
    intro k hk hsub
    have hklt : k < rSeq α γ J₀ j := by omega
    obtain ⟨hwf, hl, hr, hnum⟩ := ih (k + 1) (by omega) (by omega)
    rw [combFrom_eq_node hklt]
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine ⟨by simpa using hwf, tentTree_WF (k + 1) 1 _ _, ?_⟩
      rw [hr, tentTree_lval]
    · simp [LTree.lval, hl]
    · simp [LTree.rval, tentTree_rval]
    · rw [LTree.numLeaves_node, hnum, tentTree_numLeaves]
      omega

lemma combFrom_height {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) {J₀ : ℕ}
    (hJ₀ : 3 < (J₀ : ℝ) * (α + γ)) {j : ℕ} (hj : 1 ≤ j) :
    ∀ m k : ℕ, k ≤ rSeq α γ J₀ j → rSeq α γ J₀ j - k = m →
      ∀ a ∈ (combFrom α γ J₀ j k).leaves,
        a.height ≤ max (max 4 (rSeq α γ J₀ j + 2))
          (max (2 ^ (aSeq α J₀ (j + 1) + 3)) (2 ^ bSeq γ J₀ j)) := by
  set B := max (max 4 (rSeq α γ J₀ j + 2)) (max (2 ^ (aSeq α J₀ (j + 1) + 3)) (2 ^ bSeq γ J₀ j))
  have hr1 : 1 ≤ rSeq α γ J₀ j := one_le_rSeq hα hαγ hJ₀ hj
  have ha1 : 1 ≤ aSeq α J₀ (j + 1) := one_le_aSeq hα hαγ hJ₀ (by omega)
  have hbase_le : aSeq α J₀ (j + 1) + 2 ≤ rSeq α γ J₀ j + 1 →
      rSeq α γ J₀ j + 1 - (aSeq α J₀ (j + 1) + 2) ≤ bSeq γ J₀ j := by
    intro _
    have h1 : aSeq α J₀ j ≤ aSeq α J₀ (j + 1) := aSeq_mono hα.le J₀ (by omega)
    have ha0 : 1 ≤ aSeq α J₀ j := one_le_aSeq hα hαγ hJ₀ hj
    have hb0 : 1 ≤ bSeq γ J₀ j := one_le_bSeq hαγ hJ₀ hj
    unfold rSeq
    omega
  intro m
  induction m with
  | zero =>
    intro k hk hsub a ha
    obtain rfl : k = rSeq α γ J₀ j := by omega
    rw [combFrom_eq_base] at ha
    have htent := tentTree_pow2_height (rSeq α γ J₀ j) (aSeq α J₀ (j + 1) + 2)
      hr1 (Or.inl rfl) _ a ha
    refine htent.trans (max_le (max_le (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_trans (le_max_right _ _) (le_max_left _ _))) ?_)
    refine max_le (le_trans (le_max_left _ _) (le_max_right _ _)) ?_
    split_ifs with hif
    · refine le_trans ?_ (le_trans (le_max_right _ _) (le_max_right _ _))
      exact Nat.pow_le_pow_right (by norm_num) (hbase_le hif)
    · refine le_trans ?_ (le_trans (le_max_left _ _) (le_max_right _ _))
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
  | succ m ih =>
    intro k hk hsub a ha
    have hklt : k < rSeq α γ J₀ j := by omega
    rw [combFrom_eq_node hklt, LTree.leaves, List.mem_append] at ha
    rcases ha with ha | ha
    · exact ih (k + 1) (by omega) (by omega) a ha
    · set d := k + 1
      set e := expAt α γ J₀ j d
      have htent := tentTree_pow2_height d e (by omega) (Or.inr rfl) _ a ha
      refine htent.trans (max_le (max_le (le_trans (le_max_left _ _) (le_max_left _ _))
        (le_trans (Nat.add_le_add_right (by omega : d ≤ rSeq α γ J₀ j) 2)
          (le_trans (le_max_right _ _) (le_max_left _ _)))) ?_)
      have heb := expAt_bounds hα hαγ hJ₀ j d
      refine max_le (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega))
        (le_trans (le_max_left _ _) (le_max_right _ _))) ?_
      split_ifs with hif
      · refine le_trans ?_ (le_trans (le_max_right _ _) (le_max_right _ _))
        apply Nat.pow_le_pow_right (by norm_num)
        by_cases hex : ∃ i ∈ Finset.Icc 1 j, rSeq α γ J₀ i = d
        · obtain ⟨i, hi, hrid⟩ := hex
          rw [Finset.mem_Icc] at hi
          have heq : e = aSeq α J₀ i := expAt_eq_of_mem hα hαγ hJ₀ hi.1 hi.2 hrid
          have ha_i : 1 ≤ aSeq α J₀ i := one_le_aSeq hα hαγ hJ₀ hi.1
          have hb_i : 1 ≤ bSeq γ J₀ i := one_le_bSeq hαγ hJ₀ hi.1
          have hri_def : d + 1 - aSeq α J₀ i = bSeq γ J₀ i := by
            rw [← hrid]; unfold rSeq; omega
          have hb_le : bSeq γ J₀ i ≤ bSeq γ J₀ j := by
            apply Nat.floor_mono
            have hJpos := J0_pos_real hα hαγ hJ₀
            have hij' : (i : ℝ) ≤ j := by exact_mod_cast hi.2
            have hγ : 0 ≤ γ := by linarith
            gcongr
          rw [heq, hri_def]
          exact hb_le
        · push_neg at hex
          have heq : e = aSeq α J₀ (j + 1) + 2 := expAt_eq_default α γ J₀ j d (fun i hi1 hij => by
            exact hex i (Finset.mem_Icc.mpr ⟨hi1, hij⟩))
          rw [heq]
          have hd_le : d + 1 - (aSeq α J₀ (j + 1) + 2) ≤ rSeq α γ J₀ j + 1 - (aSeq α J₀ (j + 1) + 2)
            := by
            omega
          exact hd_le.trans (hbase_le (by omega))
      · refine le_trans ?_ (le_trans (le_max_left _ _) (le_max_right _ _))
        exact Nat.pow_le_pow_right (by norm_num) (by omega)

lemma combFrom_eval_err {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) {J₀ : ℕ}
    (hJ₀ : 3 < (J₀ : ℝ) * (α + γ)) {j : ℕ} (hj : 1 ≤ j) :
    ∀ m k : ℕ, k ≤ rSeq α γ J₀ j → rSeq α γ J₀ j - k = m →
      ∀ x ∈ cellIcc k 0,
        |combFun α γ J₀ x - (combFrom α γ J₀ j k).eval k 0 x| ≤
          (2 : ℝ) ^ (-(aSeq α J₀ (j + 1) : ℤ)) + (2 : ℝ) ^ (-((aSeq α J₀ (j + 1) + 2 : ℕ) : ℤ)) :=
            by
  set err := (2 : ℝ) ^ (-(aSeq α J₀ (j + 1) : ℤ)) + (2 : ℝ) ^ (-((aSeq α J₀ (j + 1) + 2 : ℕ) : ℤ))
  have herr_nonneg : 0 ≤ err := by positivity
  intro m
  induction m with
  | zero =>
    intro k hk hsub x hx
    obtain rfl : k = rSeq α γ J₀ j := by omega
    rw [combFrom_eq_base, tentTree_eval (rSeq α γ J₀ j) 0 _ _ hx]
    have hcomb := combFun_on_deep_leaf hα hαγ hJ₀ hj hx
    have htent0 : 0 ≤ tent (cL (rSeq α γ J₀ j) 0) (cR (rSeq α γ J₀ j) 0)
        (((1 : ℚ) / 2 ^ (aSeq α J₀ (j + 1) + 2) : ℚ) : ℝ) x :=
      tent_nonneg (by positivity) x
    have htent1 : tent (cL (rSeq α γ J₀ j) 0) (cR (rSeq α γ J₀ j) 0)
        (((1 : ℚ) / 2 ^ (aSeq α J₀ (j + 1) + 2) : ℚ) : ℝ) x ≤
        (2 : ℝ) ^ (-((aSeq α J₀ (j + 1) + 2 : ℕ) : ℤ)) := by
      refine (tent_le (by positivity) (cL_lt_cR _ _) x).trans (le_of_eq ?_)
      push_cast
      rw [one_div, zpow_neg]
      norm_cast
    rw [abs_le]
    constructor <;> linarith
  | succ m ih =>
    intro k hk hsub x hx
    have hklt : k < rSeq α γ J₀ j := by omega
    rw [combFrom_eq_node hklt]
    rw [cellIcc_eq, mem_Icc] at hx
    unfold LTree.eval
    split_ifs with hlt
    · have hx' : x ∈ cellIcc (k + 1) 0 := by
        rw [cellIcc_eq, mem_Icc]
        have hl : cL (k + 1) 0 = cL k 0 := by simpa using cL_child_left k 0
        have hr : cR (k + 1) 0 = cL (k + 1) 1 := by simpa using cR_child_left k 0
        exact ⟨hl ▸ hx.1, hr ▸ hlt.le⟩
      have hc0 : LTree.eval (k + 1) (2 * (0 : ℤ)) (combFrom α γ J₀ j (k + 1)) x =
          LTree.eval (k + 1) 0 (combFrom α γ J₀ j (k + 1)) x := by simp
      rw [hc0]
      exact ih (k + 1) (by omega) (by omega) x hx'
    · have hx' : x ∈ cellIcc (k + 1) 1 := by
        rw [cellIcc_eq, mem_Icc]
        have hr1 : cR (k + 1) 1 = cR k 0 := by simpa using cR_child_right k 0
        exact ⟨not_lt.mp hlt, hr1 ▸ hx.2⟩
      simp only [mul_zero, zero_add]
      rw [tentTree_eval (k + 1) 1 _ _ hx']
      by_cases hex : ∃ i ∈ Finset.Icc 1 j, rSeq α γ J₀ i = k + 1
      · obtain ⟨i, hi, hrik⟩ := hex
        rw [Finset.mem_Icc] at hi
        have heq := expAt_eq_of_mem hα hαγ hJ₀ hi.1 hi.2 hrik
        have hxr : x ∈ cellIcc (rSeq α γ J₀ i) 1 := by rwa [hrik]
        rw [combFun_eq_phi hα hαγ hJ₀ hi.1 hxr]
        have hcast : ((((1 : ℚ) / 2 ^ expAt α γ J₀ j (k + 1)) : ℚ) : ℝ) =
            (2 : ℝ) ^ (-(aSeq α J₀ i : ℤ)) := by
          rw [heq]
          push_cast
          rw [one_div, zpow_neg]
          norm_cast
        unfold phi
        rw [hrik, hcast, sub_self, abs_zero]
        exact herr_nonneg
      · have hnot : ∀ i : ℕ, 1 ≤ i → i ≤ j → rSeq α γ J₀ i ≠ k + 1 := by
          intro i hi1 hij hrik
          exact hex ⟨i, Finset.mem_Icc.mpr ⟨hi1, hij⟩, hrik⟩
        have heq := expAt_eq_default α γ J₀ j (k + 1) hnot
        have hcomb0 := combFun_eq_zero_on_flat hα hαγ hJ₀ hj (by omega) (by omega) hnot hx'
        rw [hcomb0, zero_sub, abs_neg]
        have htent0 : 0 ≤ tent (cL (k + 1) 1) (cR (k + 1) 1)
            (((1 : ℚ) / 2 ^ expAt α γ J₀ j (k + 1) : ℚ) : ℝ) x :=
          tent_nonneg (by positivity) x
        have htent1 : tent (cL (k + 1) 1) (cR (k + 1) 1)
            (((1 : ℚ) / 2 ^ expAt α γ J₀ j (k + 1) : ℚ) : ℝ) x ≤
            (2 : ℝ) ^ (-((aSeq α J₀ (j + 1) + 2 : ℕ) : ℤ)) := by
          refine (tent_le (by positivity) (cL_lt_cR _ _) x).trans (le_of_eq ?_)
          rw [heq]
          push_cast
          rw [one_div, zpow_neg]
          norm_cast
        rw [abs_of_nonneg htent0]
        exact htent1.trans (le_add_of_nonneg_left (by positivity))

/-! ## 5. Cotas da altura e taxa de aproximação para todo `N ≥ 1` -/

lemma real_le_two_mul_two_rpow {x : ℝ} (hx : 0 ≤ x) : x ≤ 2 * (2 : ℝ) ^ x := by
  have hlog : 1 / 2 < Real.log 2 := by
    have hexp : Real.exp 1 < (2 : ℝ) ^ 2 := by
      have := Real.exp_one_lt_d9
      linarith
    have hlog_lt : 1 < Real.log ((2 : ℝ) ^ 2) := by
      rw [← Real.exp_lt_exp, Real.exp_log (by positivity)]
      exact hexp
    rw [Real.log_pow] at hlog_lt
    push_cast at hlog_lt
    linarith
  have h1 : x * Real.log 2 + 1 ≤ Real.exp (x * Real.log 2) := Real.add_one_le_exp (x * Real.log 2)
  have h2 : Real.exp (x * Real.log 2) = (2 : ℝ) ^ x := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  have h3 : x / 2 ≤ x * Real.log 2 := by nlinarith
  linarith

lemma combFrom_maxHeight_le {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) {J₀ : ℕ}
    (hJ₀ : 3 < (J₀ : ℝ) * (α + γ)) {j : ℕ} (hj : 1 ≤ j) :
    ((combFrom α γ J₀ j 0).maxHeight : ℝ) ≤
      max 6 ((2 : ℝ) ^ ((J₀ : ℝ) * α + 4)) * ((2 : ℝ) ^ (J₀ * j)) ^ γ := by
  have hJpos := J0_pos_real hα hαγ hJ₀
  have hγ : 0 < γ := lt_of_lt_of_le hα hαγ
  have hNj1 : (1 : ℝ) ≤ (2 : ℝ) ^ (J₀ * j) := one_le_pow₀ (by norm_num)
  have hNj_pos : (0 : ℝ) < (2 : ℝ) ^ (J₀ * j) := by positivity
  have hNjγ_ge1 : (1 : ℝ) ≤ ((2 : ℝ) ^ (J₀ * j)) ^ γ := Real.one_le_rpow hNj1 hγ.le
  have hNjγ_eq : ((2 : ℝ) ^ (J₀ * j)) ^ γ = (2 : ℝ) ^ ((J₀ : ℝ) * γ * j) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  set M := max 6 ((2 : ℝ) ^ ((J₀ : ℝ) * α + 4))
  have hM6 : 6 ≤ M := le_max_left _ _
  have hMp : (2 : ℝ) ^ ((J₀ : ℝ) * α + 4) ≤ M := le_max_right _ _
  have hmax : (combFrom α γ J₀ j 0).maxHeight ≤
      max (max 4 (rSeq α γ J₀ j + 2)) (max (2 ^ (aSeq α J₀ (j + 1) + 3)) (2 ^ bSeq γ J₀ j)) :=
    LTree.maxHeight_le_iff.mpr (combFrom_height hα hαγ hJ₀ hj (rSeq α γ J₀ j) 0 (Nat.zero_le _)
      (Nat.sub_zero _))
  have hmaxR : ((combFrom α γ J₀ j 0).maxHeight : ℝ) ≤
      max (max 4 ((rSeq α γ J₀ j : ℝ) + 2))
        (max ((2 : ℝ) ^ (aSeq α J₀ (j + 1) + 3)) ((2 : ℝ) ^ bSeq γ J₀ j)) := by
    exact_mod_cast hmax
  refine hmaxR.trans (max_le (max_le ?_ ?_) (max_le ?_ ?_))
  · -- `4 ≤ M * N_j^γ`
    nlinarith
  · -- `r_j + 2 ≤ M * N_j^γ`
    have hr : (rSeq α γ J₀ j : ℝ) ≤ (J₀ : ℝ) * (α + γ) * j := by
      have ha1 := one_le_aSeq hα hαγ hJ₀ hj
      have hb1 := one_le_bSeq hαγ hJ₀ hj
      have hcast : (rSeq α γ J₀ j : ℝ) = (aSeq α J₀ j : ℝ) + bSeq γ J₀ j - 1 := by
        unfold rSeq
        have hge : 1 ≤ aSeq α J₀ j + bSeq γ J₀ j := by omega
        rw [Nat.cast_sub hge, Nat.cast_add, Nat.cast_one]
      have ha : (aSeq α J₀ j : ℝ) < (J₀ : ℝ) * α * j + 1 := by
        unfold aSeq; exact Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg hJpos.le hα.le)
          (Nat.cast_nonneg j))
      have hb : (bSeq γ J₀ j : ℝ) ≤ (J₀ : ℝ) * γ * j := by
        unfold bSeq; exact Nat.floor_le (mul_nonneg (mul_nonneg hJpos.le (by linarith))
          (Nat.cast_nonneg j))
      linarith
    have h2J : (J₀ : ℝ) * (α + γ) * j ≤ 2 * ((J₀ : ℝ) * γ * j) := by
      have : (J₀ : ℝ) * α * j ≤ (J₀ : ℝ) * γ * j := by gcongr
      linarith
    have hexp := real_le_two_mul_two_rpow (show 0 ≤ (J₀ : ℝ) * γ * j by positivity)
    rw [← hNjγ_eq] at hexp
    nlinarith
  · -- `2^(a_{j+1}+3) ≤ M * N_j^γ`
    have ha : (aSeq α J₀ (j + 1) : ℝ) < (J₀ : ℝ) * α * ((j : ℝ) + 1) + 1 := by
      unfold aSeq
      push_cast
      exact Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg hJpos.le hα.le) (add_nonneg (Nat.cast_nonneg
        j) zero_le_one))
    have hle : (aSeq α J₀ (j + 1) : ℝ) + 3 ≤ ((J₀ : ℝ) * α + 4) + (J₀ : ℝ) * γ * j := by
      have : (J₀ : ℝ) * α * j ≤ (J₀ : ℝ) * γ * j := by gcongr
      linarith
    calc (2 : ℝ) ^ (aSeq α J₀ (j + 1) + 3)
        = (2 : ℝ) ^ ((aSeq α J₀ (j + 1) : ℝ) + 3) := by
          rw [← Real.rpow_natCast]; push_cast; rfl
      _ ≤ (2 : ℝ) ^ (((J₀ : ℝ) * α + 4) + (J₀ : ℝ) * γ * j) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      _ = (2 : ℝ) ^ ((J₀ : ℝ) * α + 4) * (2 : ℝ) ^ ((J₀ : ℝ) * γ * j) :=
          Real.rpow_add (by norm_num) _ _
      _ ≤ M * ((2 : ℝ) ^ (J₀ * j)) ^ γ := by
          rw [← hNjγ_eq]
          exact mul_le_mul_of_nonneg_right hMp (by positivity)
  · -- `2^b_j ≤ M * N_j^γ`
    have hb : (bSeq γ J₀ j : ℝ) ≤ (J₀ : ℝ) * γ * j := by
      unfold bSeq; exact Nat.floor_le (mul_nonneg (mul_nonneg hJpos.le (by linarith))
        (Nat.cast_nonneg j))
    calc (2 : ℝ) ^ bSeq γ J₀ j
        = (2 : ℝ) ^ (bSeq γ J₀ j : ℝ) := by rw [← Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ ((J₀ : ℝ) * γ * j) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hb
      _ = 1 * ((2 : ℝ) ^ (J₀ * j)) ^ γ := by rw [one_mul, hNjγ_eq]
      _ ≤ M * ((2 : ℝ) ^ (J₀ * j)) ^ γ := by
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-! ## 6. Cotas inferiores de `ω₂` e não pertencimento a Besov -/

lemma omega2_combFun_lower {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) {J₀ : ℕ}
    (hJ₀ : 3 < (J₀ : ℝ) * (α + γ)) {j : ℕ} (hj : 1 ≤ j) :
    ENNReal.ofReal ((2 : ℝ) ^ (1 - (aSeq α J₀ j : ℝ))) ≤
      omega2 (combFun α γ J₀) ((2 : ℝ) ^ (rSeq α γ J₀ j + 1))⁻¹ := by
  set r := rSeq α γ J₀ j
  have hr1 : 1 ≤ r := one_le_rSeq hα hαγ hJ₀ hj
  set h : ℝ := ((2 : ℝ) ^ (r + 1))⁻¹
  set x : ℝ := cL r 1
  have hh0 : 0 < h := by positivity
  have hcellL : x ∈ cellIcc r 1 := by rw [cellIcc_eq, mem_Icc]; exact ⟨le_rfl, (cL_lt_cR r 1).le⟩
  have hmid_eq : x + h = (cL r 1 + cR r 1) / 2 := by
    simp only [x, h, cL, cR]
    push_cast
    rw [pow_succ]
    field_simp
    ring
  have hcellM : x + h ∈ cellIcc r 1 := by
    rw [cellIcc_eq, mem_Icc, hmid_eq]
    have hab := cL_lt_cR r 1
    constructor <;> linarith
  have hright_eq : x + 2 * h = cR r 1 := by
    simp only [x, h, cL, cR]
    push_cast
    rw [pow_succ]
    field_simp
  have hcellR : x + 2 * h ∈ cellIcc r 1 := by
    rw [cellIcc_eq, mem_Icc, hright_eq]
    exact ⟨(cL_lt_cR r 1).le, le_rfl⟩
  have hx0 : 0 ≤ x := by simp only [x, cL]; positivity
  have hx2h : x + 2 * h ≤ 1 := by
    rw [hright_eq]
    unfold cR
    norm_num
    have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
      have : 2 ≤ 2 ^ r := Nat.le_self_pow (by omega) 2
      exact_mod_cast this
    exact (div_le_one (by positivity)).mpr hpow
  have hfx : combFun α γ J₀ x = 0 := by
    rw [combFun_eq_phi hα hαγ hJ₀ hj hcellL]
    exact tent_eq_zero_of_le (cL_lt_cR r 1) le_rfl
  have hfm : combFun α γ J₀ (x + h) = (2 : ℝ) ^ (-(aSeq α J₀ j : ℤ)) := by
    rw [combFun_eq_phi hα hαγ hJ₀ hj hcellM, hmid_eq]
    exact tent_midpoint _ _ _
  have hfr : combFun α γ J₀ (x + 2 * h) = 0 := by
    rw [combFun_eq_phi hα hαγ hJ₀ hj hcellR, hright_eq]
    exact tent_eq_zero_of_ge (cL_lt_cR r 1) le_rfl
  have hdiff : |combFun α γ J₀ (x + 2 * h) - 2 * combFun α γ J₀ (x + h) + combFun α γ J₀ x| =
      (2 : ℝ) ^ (1 - (aSeq α J₀ j : ℝ)) := by
    rw [hfr, hfm, hfx]
    have hpos : 0 < (2 : ℝ) ^ (-(aSeq α J₀ j : ℤ)) := by positivity
    rw [zero_sub, add_zero, abs_neg, abs_of_pos (by positivity)]
    calc 2 * (2 : ℝ) ^ (-(aSeq α J₀ j : ℤ))
        = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(aSeq α J₀ j : ℝ)) := by
          rw [Real.rpow_one, ← Real.rpow_intCast]; norm_cast
      _ = (2 : ℝ) ^ (1 - (aSeq α J₀ j : ℝ)) := by
          rw [← Real.rpow_add (by norm_num)]; ring_nf
  rw [← hdiff]
  exact le_omega2 ⟨hh0, le_rfl⟩ ⟨hx0, hx2h⟩

lemma bterm_combFun_lower {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) {J₀ : ℕ}
    (hJ₀ : 3 < (J₀ : ℝ) * (α + γ)) (θ : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    ENNReal.ofReal ((2 : ℝ) ^ ((θ - α / (α + γ)) * (rSeq α γ J₀ j + 1 : ℕ) - 1)) ≤
      bterm θ (combFun α γ J₀) (rSeq α γ J₀ j + 1) := by
  have hJpos := J0_pos_real hα hαγ hJ₀
  set θs := α / (α + γ)
  have hθs0 : 0 < θs := div_pos hα (by linarith)
  have hθs1 : θs ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hlow := omega2_combFun_lower hα hαγ hJ₀ hj
  have hr_ge : (J₀ : ℝ) * (α + γ) * j - 1 < (rSeq α γ J₀ j + 1 : ℕ) := by
    have ha1 := one_le_aSeq hα hαγ hJ₀ hj
    have hb1 := one_le_bSeq hαγ hJ₀ hj
    have hcast : ((rSeq α γ J₀ j + 1 : ℕ) : ℝ) = (aSeq α J₀ j : ℝ) + bSeq γ J₀ j := by
      have hr_eq : rSeq α γ J₀ j + 1 = aSeq α J₀ j + bSeq γ J₀ j := by
        unfold rSeq
        omega
      rw [hr_eq]
      push_cast
      rfl
    have ha : (J₀ : ℝ) * α * j ≤ aSeq α J₀ j := by
      unfold aSeq; exact Nat.le_ceil _
    have hb : (J₀ : ℝ) * γ * j - 1 < bSeq γ J₀ j := by
      have := Nat.lt_floor_add_one ((J₀ : ℝ) * γ * j)
      unfold bSeq; linarith
    linarith
  have ha_lt : (aSeq α J₀ j : ℝ) < (J₀ : ℝ) * α * j + 1 := by
    unfold aSeq
    exact Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg hJpos.le hα.le) (Nat.cast_nonneg j))
  have hexp : (θ - θs) * (rSeq α γ J₀ j + 1 : ℕ) - 1 ≤
      θ * ((rSeq α γ J₀ j + 1 : ℕ) : ℝ) + (1 - (aSeq α J₀ j : ℝ)) := by
    have h1 : θs * ((rSeq α γ J₀ j + 1 : ℕ) : ℝ) ≥ θs * ((J₀ : ℝ) * (α + γ) * j - 1) :=
      mul_le_mul_of_nonneg_left hr_ge.le hθs0.le
    have h2 : θs * ((J₀ : ℝ) * (α + γ) * j - 1) = (J₀ : ℝ) * α * j - θs := by
      simp only [θs]
      field_simp [show α + γ ≠ 0 by linarith]
    linarith
  unfold bterm
  calc ENNReal.ofReal ((2 : ℝ) ^ ((θ - θs) * (rSeq α γ J₀ j + 1 : ℕ) - 1))
      ≤ ENNReal.ofReal ((2 : ℝ) ^ (θ * ((rSeq α γ J₀ j + 1 : ℕ) : ℝ) + (1 - (aSeq α J₀ j : ℝ)))) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
    _ = ENNReal.ofReal (((2 : ℝ) ^ (rSeq α γ J₀ j + 1)) ^ θ) *
          ENNReal.ofReal ((2 : ℝ) ^ (1 - (aSeq α J₀ j : ℝ))) := by
        rw [Real.rpow_add (by norm_num), ← Real.rpow_natCast (2 : ℝ) (rSeq α γ J₀ j + 1),
          ← Real.rpow_mul (by norm_num), mul_comm θ _, ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (((2 : ℝ) ^ (rSeq α γ J₀ j + 1)) ^ θ) *
          omega2 (combFun α γ J₀) ((2 : ℝ) ^ (rSeq α γ J₀ j + 1))⁻¹ :=
        mul_le_mul_right hlow _

lemma not_besovInf_combFun {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) {J₀ : ℕ}
    (hJ₀ : 3 < (J₀ : ℝ) * (α + γ)) {θ : ℝ} (hθ : α / (α + γ) < θ) :
    ¬ BesovInf θ (combFun α γ J₀) := by
  intro hB
  unfold BesovInf at hB
  have hsup : ⨆ r : ℕ, bterm θ (combFun α γ J₀) r < ⊤ :=
    lt_of_le_of_lt le_add_self hB
  set S := (⨆ r : ℕ, bterm θ (combFun α γ J₀) r).toReal
  have hgap : 0 < θ - α / (α + γ) := sub_pos.mpr hθ
  obtain ⟨j0, hj0⟩ := exists_nat_gt ((2 * (S + 2) + 1) / (θ - α / (α + γ)))
  set j := max 1 j0
  have hj1 : 1 ≤ j := le_max_left _ _
  have hjr : j ≤ rSeq α γ J₀ j + 1 := by
    have := rSeq_ge_two_mul_sub_one hα hαγ hJ₀ hj1
    omega
  have hj_real : 2 * (S + 2) + 1 < (θ - α / (α + γ)) * (j : ℝ) := by
    have h0 := (div_lt_iff₀ hgap).mp hj0
    have hjle : (j0 : ℝ) ≤ j := by exact_mod_cast le_max_right 1 j0
    nlinarith
  have hjr_real : (j : ℝ) ≤ (rSeq α γ J₀ j + 1 : ℕ) := by exact_mod_cast hjr
  have hexp : 2 * (S + 2) < (θ - α / (α + γ)) * (rSeq α γ J₀ j + 1 : ℕ) - 1 := by
    have hle1 : (θ - α / (α + γ)) * (j : ℝ) ≤ (θ - α / (α + γ)) * (rSeq α γ J₀ j + 1 : ℕ) :=
      mul_le_mul_of_nonneg_left hjr_real hgap.le
    linarith
  have hpow_gt : S + 1 < (2 : ℝ) ^ ((θ - α / (α + γ)) * (rSeq α γ J₀ j + 1 : ℕ) - 1) := by
    set u := (θ - α / (α + γ)) * (rSeq α γ J₀ j + 1 : ℕ) - 1
    have hu0 : 0 ≤ u := by
      have : 0 ≤ S := ENNReal.toReal_nonneg
      linarith
    have h2 : u ≤ 2 * (2 : ℝ) ^ u := real_le_two_mul_two_rpow hu0
    linarith
  have hlow := (bterm_combFun_lower hα hαγ hJ₀ θ hj1).trans
    (le_iSup (fun r => bterm θ (combFun α γ J₀) r) (rSeq α γ J₀ j + 1))
  have hS_eq : ENNReal.ofReal S = ⨆ r : ℕ, bterm θ (combFun α γ J₀) r :=
    ENNReal.ofReal_toReal hsup.ne
  have hle_ofReal : ENNReal.ofReal (S + 1) ≤ ENNReal.ofReal S := by
    rw [hS_eq]
    exact (ENNReal.ofReal_le_ofReal hpow_gt.le).trans hlow
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  have hle_real : S + 1 ≤ S := (ENNReal.ofReal_le_ofReal_iff hS0).mp hle_ofReal
  linarith

lemma not_besovQ_combFun {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) {J₀ : ℕ}
    (hJ₀ : 3 < (J₀ : ℝ) * (α + γ)) {p : ℝ} (hp : 0 < p) :
    ¬ BesovQ (α / (α + γ)) p (combFun α γ J₀) := by
  intro hB
  unfold BesovQ at hB
  set θs := α / (α + γ)
  have hpow_fin : (∑' r : ℕ, bterm θs (combFun α γ J₀) r ^ p) ^ (1 / p) < ⊤ :=
    lt_of_le_of_lt le_add_self hB
  have hsum_fin : ∑' r : ℕ, bterm θs (combFun α γ J₀) r ^ p ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.top_rpow_of_pos (by positivity)] at hpow_fin
    exact lt_irrefl ⊤ hpow_fin
  set c : ENNReal := ENNReal.ofReal (1 / 2) ^ p
  have hc_pos : 0 < c := ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (by norm_num))
    ENNReal.ofReal_ne_top
  have hc_ne_top : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top
  have hterm : ∀ n : ℕ, c ≤ bterm θs (combFun α γ J₀) (rSeq α γ J₀ (n + 1) + 1) ^ p := by
    intro n
    apply ENNReal.rpow_le_rpow _ hp.le
    have hlow := bterm_combFun_lower hα hαγ hJ₀ θs (by omega : 1 ≤ n + 1)
    have hpow : (1 / 2 : ℝ) = (2 : ℝ) ^ ((θs - α / (α + γ)) * (rSeq α γ J₀ (n + 1) + 1 : ℕ) - 1) :=
      by
      simp [θs]; norm_num
    simpa only [← hpow] using hlow
  let idx : ℕ → ℕ := fun n => rSeq α γ J₀ (n + 1) + 1
  have hidx_inj : Function.Injective idx := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := rSeq_strictMonoOn hα hαγ hJ₀ (by omega : 1 ≤ a + 1) (by omega : a + 1 < b + 1)
      simp only [idx] at hab
      omega
    · have := rSeq_strictMonoOn hα hαγ hJ₀ (by omega : 1 ≤ b + 1) (by omega : b + 1 < a + 1)
      simp only [idx] at hab
      omega
  have hmul_le : ∀ K : ℕ, (K : ENNReal) * c ≤ ∑' r : ℕ, bterm θs (combFun α γ J₀) r ^ p := by
    intro K
    calc (K : ENNReal) * c
        = ∑ _ ∈ Finset.range K, c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ n ∈ Finset.range K, bterm θs (combFun α γ J₀) (idx n) ^ p :=
          Finset.sum_le_sum fun n _ => hterm n
      _ = ∑ r ∈ (Finset.range K).image idx, bterm θs (combFun α γ J₀) r ^ p := by
          rw [Finset.sum_image (fun a _ b _ h => hidx_inj h)]
      _ ≤ ∑' r : ℕ, bterm θs (combFun α γ J₀) r ^ p := ENNReal.sum_le_tsum _
  set T := (∑' r : ℕ, bterm θs (combFun α γ J₀) r ^ p).toReal
  have hc_toReal_pos : 0 < c.toReal := ENNReal.toReal_pos hc_pos.ne' hc_ne_top
  obtain ⟨K, hK⟩ := exists_nat_gt (T / c.toReal)
  have hK1 : T < (K : ℝ) * c.toReal := (div_lt_iff₀ hc_toReal_pos).mp hK
  have hK2 : ((K : ENNReal) * c).toReal ≤ T := ENNReal.toReal_mono hsum_fin (hmul_le K)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hK2
  linarith

/-! ## 7. Teorema principal IV.5.9 -/

/-- **Teorema IV.5.9 (agudeza por um pente de tendas)** (`\label{map:artigo_3:5.9}`,
`\label{artigo_3:thm:critical-tent-comb}`):

Para todo `0 < α ≤ γ` com `θ* = α / (α + γ)`, existem `f ∈ C([0,1])` e uma constante `C > 0`
tais que, na **biblioteca original** sob a agenda `H(N) = ⌈C N^γ⌉`:
1. `e_N^{𝓛,H}(f) ≤ C N^{-α}` para todo `N ≥ 1`;
2. `f ∉ B^θ_{∞,∞}([0,1])` para todo `θ > θ*`;
3. `f ∉ B^{θ*}_{∞,r}([0,1])` para todo `0 < r < ∞`. -/
theorem critical_tent_comb {α γ : ℝ} (hα : 0 < α) (hαγ : α ≤ γ) :
    ∃ (f : ℝ → ℝ) (C : ℝ), 0 < C ∧ ContinuousOn f (Icc (0 : ℝ) 1) ∧
      (∀ N : ℕ, 1 ≤ N →
        pErr (fun n => ⌈C * (n : ℝ) ^ γ⌉₊) N f ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-α))) ∧
      (∀ θ : ℝ, α / (α + γ) < θ → ¬ BesovInf θ f) ∧
      (∀ r : ℝ, 0 < r → ¬ BesovQ (α / (α + γ)) r f) := by
  obtain ⟨J₀, hJ2, hJ₀, hJl⟩ := exists_J0 hα hαγ
  have hJ1 : 1 ≤ J₀ := by omega
  set f := combFun α γ J₀
  set C : ℝ := max 6 ((2 : ℝ) ^ ((J₀ : ℝ) * α + 4))
  have hC6 : 6 ≤ C := le_max_left _ _
  have hCpos : 0 < C := by linarith
  have hCp : (2 : ℝ) ^ ((J₀ : ℝ) * α + 4) ≤ C := le_max_right _ _
  set H : ℕ → ℕ := fun n => ⌈C * (n : ℝ) ^ γ⌉₊
  refine ⟨f, C, hCpos, (combFun_continuous hα hJ1).continuousOn, ?_,
    fun θ hθ => not_besovInf_combFun hα hαγ hJ₀ hθ,
    fun r hr => not_besovQ_combFun hα hαγ hJ₀ hr⟩
  intro N hN
  by_cases hN_small : N < 2 ^ J₀
  · -- Escala inicial `1 ≤ N < 2^{J₀}`: usa `0 ∈ Σ_N^{𝓛,H}`
    have h0_mem : (0 : ℝ → ℝ) ∈ Sigma H N := Or.inl rfl
    have hdist0 : distInf f 0 ≤ ENNReal.ofReal 1 := by
      refine iSup₂_le fun x _ => ENNReal.ofReal_le_ofReal ?_
      simp only [Pi.zero_apply, sub_zero]
      show |combFun α γ J₀ x| ≤ 1
      rw [abs_of_nonneg (combFun_nonneg α γ J₀ x)]
      exact combFun_le_one hα hαγ hJ₀ x
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hNa : (N : ℝ) ^ α ≤ (2 : ℝ) ^ ((J₀ : ℝ) * α) := by
      have hNlt : (N : ℝ) ≤ (2 : ℝ) ^ J₀ := by exact_mod_cast hN_small.le
      calc (N : ℝ) ^ α ≤ ((2 : ℝ) ^ J₀) ^ α := Real.rpow_le_rpow hN0.le hNlt hα.le
        _ = (2 : ℝ) ^ ((J₀ : ℝ) * α) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have h2le : (2 : ℝ) ^ ((J₀ : ℝ) * α) ≤ (2 : ℝ) ^ ((J₀ : ℝ) * α + 4) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h1le : 1 ≤ C * (N : ℝ) ^ (-α) := by
      have hNa_pos : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hN0 α
      rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, one_le_div hNa_pos]
      exact hNa.trans (h2le.trans hCp)
    calc pErr H N f ≤ distInf f 0 := iInf₂_le (0 : ℝ → ℝ) h0_mem
      _ ≤ ENNReal.ofReal 1 := hdist0
      _ ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-α)) := ENNReal.ofReal_le_ofReal h1le
  · -- Escala `N ≥ 2^{J₀}`: usa `g_j` com `j = Nat.log (2 ^ J₀) N ≥ 1`
    have hN_ge : 2 ^ J₀ ≤ N := Nat.le_of_not_lt hN_small
    have h2J_gt1 : 1 < 2 ^ J₀ := by
      have : 2 ^ 1 < 2 ^ J₀ := Nat.pow_lt_pow_right (by norm_num) (by omega)
      linarith
    set j := Nat.log (2 ^ J₀) N
    have hj1 : 1 ≤ j := Nat.le_log_of_pow_le h2J_gt1 (by simpa using hN_ge)
    have hpow_le : (2 ^ J₀) ^ j ≤ N := Nat.pow_log_le_self (2 ^ J₀) (by omega)
    have hlt_pow : N < (2 ^ J₀) ^ (j + 1) := Nat.lt_pow_succ_log_self h2J_gt1 N
    rw [← pow_mul] at hpow_le hlt_pow
    set T := combFrom α γ J₀ j 0
    have hspec := combFrom_spec α γ J₀ j (rSeq α γ J₀ j) 0 (Nat.zero_le _) (Nat.sub_zero _)
    have hwf : LTree.WF 0 0 T := hspec.1
    have hleaves : T.numLeaves ≤ N := by
      rw [hspec.2.2.2, show 2 * (rSeq α γ J₀ j + 1) = 2 * rSeq α γ J₀ j + 2 by ring]
      exact (two_rSeq_add_two_le hα hαγ hJ₀ hJl hj1).trans hpow_le
    have hheight : T.maxHeight ≤ H N := by
      have hmax := combFrom_maxHeight_le hα hαγ hJ₀ hj1
      have hNj_le : ((2 : ℝ) ^ (J₀ * j)) ^ γ ≤ (N : ℝ) ^ γ := by
        have h1 : (2 : ℝ) ^ (J₀ * j) ≤ N := by exact_mod_cast hpow_le
        exact Real.rpow_le_rpow (by positivity) h1 (by linarith)
      have hMR : (T.maxHeight : ℝ) ≤ C * (N : ℝ) ^ γ :=
        hmax.trans (mul_le_mul_of_nonneg_left hNj_le hCpos.le)
      exact_mod_cast hMR.trans (Nat.le_ceil (C * (N : ℝ) ^ γ))
    have hadm : AdmNH N (H N) T := ⟨hwf, hleaves, hheight⟩
    have hmem : T.eval 0 0 ∈ Sigma H N := Or.inr ⟨T, hadm, rfl⟩
    have herr_pt : ∀ x ∈ Icc (0 : ℝ) 1,
        |f x - T.eval 0 0 x| ≤
          (2 : ℝ) ^ (-(aSeq α J₀ (j + 1) : ℤ)) + (2 : ℝ) ^ (-((aSeq α J₀ (j + 1) + 2 : ℕ) : ℤ)) :=
            by
      intro x hx
      have hx0 : x ∈ cellIcc 0 0 := by simpa [cellIcc] using hx
      exact combFrom_eval_err hα hαγ hJ₀ hj1 (rSeq α γ J₀ j) 0 (Nat.zero_le _) (Nat.sub_zero _) x
        hx0
    have herr_bound :
        (2 : ℝ) ^ (-(aSeq α J₀ (j + 1) : ℤ)) + (2 : ℝ) ^ (-((aSeq α J₀ (j + 1) + 2 : ℕ) : ℤ)) ≤
          C * (N : ℝ) ^ (-α) := by
      have ha_ge : (J₀ : ℝ) * α * ((j : ℝ) + 1) ≤ aSeq α J₀ (j + 1) := by
        simpa [aSeq] using Nat.le_ceil ((J₀ : ℝ) * α * ((j : ℝ) + 1))
      have hpow1 : (2 : ℝ) ^ (-(aSeq α J₀ (j + 1) : ℤ)) ≤ (N : ℝ) ^ (-α) := by
        have hN_pos : (0 : ℝ) < N := by exact_mod_cast hN
        have hN_le : (N : ℝ) ≤ (2 : ℝ) ^ (J₀ * (j + 1)) := by exact_mod_cast hlt_pow.le
        calc (2 : ℝ) ^ (-(aSeq α J₀ (j + 1) : ℤ))
            = (2 : ℝ) ^ (-(aSeq α J₀ (j + 1) : ℝ)) := by rw [← Real.rpow_intCast]; norm_cast
          _ ≤ (2 : ℝ) ^ (-((J₀ : ℝ) * α * ((j : ℝ) + 1))) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = ((2 : ℝ) ^ (J₀ * (j + 1))) ^ (-α) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
              congr 1; push_cast; ring
          _ ≤ (N : ℝ) ^ (-α) := Real.rpow_le_rpow_of_nonpos hN_pos hN_le (by linarith)
      have hpow2 : (2 : ℝ) ^ (-((aSeq α J₀ (j + 1) + 2 : ℕ) : ℤ)) ≤ (2 : ℝ) ^ (-(aSeq α J₀ (j + 1) :
        ℤ)) := by
        rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
        exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by
          omega))
      have hN0 : 0 ≤ (N : ℝ) ^ (-α) := by positivity
      have hCN : 2 * (N : ℝ) ^ (-α) ≤ C * (N : ℝ) ^ (-α) :=
        mul_le_mul_of_nonneg_right (by linarith) hN0
      linarith
    calc pErr H N f ≤ distInf f (T.eval 0 0) := iInf₂_le (T.eval 0 0) hmem
      _ ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-α)) :=
          iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal ((herr_pt x hx).trans herr_bound)

end Pendencias.PenteGemini

#print axioms Pendencias.PenteGemini.tent_continuous
#print axioms Pendencias.PenteGemini.tentTree_WF
#print axioms Pendencias.PenteGemini.combFun_continuous
#print axioms Pendencias.PenteGemini.combFrom_spec
#print axioms Pendencias.PenteGemini.omega2_combFun_lower
#print axioms Pendencias.PenteGemini.not_besovInf_combFun
#print axioms Pendencias.PenteGemini.not_besovQ_combFun
#print axioms Pendencias.PenteGemini.critical_tent_comb
