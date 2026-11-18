import Mathlib

/-!
# III.12.5 — as funções `g` e `g⁺` do texto

`gC u = 2^{⌈u⌉ - u}` (contínua à esquerda, `gC n = 1` nos inteiros) e
`gP u = 2^{⌊u⌋ + 1 - u}` (contínua à direita, `gP n = 2`), com `1 ≤ gC ≤ gP ≤ 2`.
-/

namespace Pendencias

open Set Filter Topology

noncomputable def gC (u : ℝ) : ℝ := (2 : ℝ) ^ ((⌈u⌉ : ℝ) - u)
noncomputable def gP (u : ℝ) : ℝ := (2 : ℝ) ^ ((⌊u⌋ : ℝ) + 1 - u)

lemma gC_ge_one (u : ℝ) : 1 ≤ gC u :=
  Real.one_le_rpow (by norm_num) (by linarith [Int.le_ceil u])

lemma gC_lt_two (u : ℝ) : gC u < 2 := by
  have : (⌈u⌉ : ℝ) - u < 1 := by linarith [Int.ceil_lt_add_one u]
  calc gC u < (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) this
    _ = 2 := Real.rpow_one 2

lemma gP_le_two (u : ℝ) : gP u ≤ 2 := by
  have : (⌊u⌋ : ℝ) + 1 - u ≤ 1 := by linarith [Int.floor_le u]
  calc gP u ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) this
    _ = 2 := Real.rpow_one 2

lemma gC_le_gP (u : ℝ) : gC u ≤ gP u := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have : (⌈u⌉ : ℝ) ≤ ⌊u⌋ + 1 := by exact_mod_cast Int.ceil_le_floor_add_one u
  linarith

lemma gP_ge_one (u : ℝ) : 1 ≤ gP u := (gC_ge_one u).trans (gC_le_gP u)

lemma gC_nonneg (u : ℝ) : 0 ≤ gC u := by linarith [gC_ge_one u]
lemma gP_nonneg (u : ℝ) : 0 ≤ gP u := by linarith [gP_ge_one u]

lemma gC_add_int (u : ℝ) (z : ℤ) : gC (u + z) = gC u := by
  unfold gC
  rw [Int.ceil_add_intCast]
  congr 1
  push_cast; ring

lemma gP_add_int (u : ℝ) (z : ℤ) : gP (u + z) = gP u := by
  unfold gP
  rw [Int.floor_add_intCast]
  congr 1
  push_cast; ring

lemma gC_add_one (u : ℝ) : gC (u + 1) = gC u := by
  simpa using gC_add_int u 1

lemma gP_add_one (u : ℝ) : gP (u + 1) = gP u := by
  simpa using gP_add_int u 1

/-- fora dos inteiros, `gC = gP` -/
lemma gC_eq_gP_of_not_int {u : ℝ} (h : ∀ z : ℤ, u ≠ z) : gC u = gP u := by
  unfold gC gP
  have : (⌈u⌉ : ℝ) = ⌊u⌋ + 1 := by
    have h1 : (⌊u⌋ : ℝ) ≠ u := fun e => h ⌊u⌋ e.symm
    have : ⌈u⌉ = ⌊u⌋ + 1 := by
      rw [Int.ceil_eq_iff]
      constructor
      · push_cast; exact lt_of_le_of_ne (Int.floor_le u) h1 |>.trans_eq' (by ring) |> fun h => by linarith
      · push_cast; linarith [Int.lt_floor_add_one u]
    exact_mod_cast this
  rw [this]

lemma gC_int (z : ℤ) : gC z = 1 := by
  unfold gC; simp

lemma gP_int (z : ℤ) : gP z = 2 := by
  unfold gP; simp

open Classical in
/-- `gP - gC` vale `1` nos inteiros e `0` fora deles -/
lemma gP_sub_gC (u : ℝ) : gP u - gC u = if ∃ z : ℤ, u = z then 1 else 0 := by
  split_ifs with h
  · obtain ⟨z, rfl⟩ := h
    rw [gP_int, gC_int]; norm_num
  · push_neg at h
    rw [gC_eq_gP_of_not_int h]; ring

/-! ## Semicontinuidade e limites laterais -/

lemma cont_aux (n : ℝ) : Continuous (fun v : ℝ => (2 : ℝ) ^ (n - v)) :=
  Continuous.rpow continuous_const (continuous_const.sub continuous_id) (fun _ => Or.inl (by norm_num))

/-- no intervalo `(n, n+1)`, `gC v = 2^{n+1-v}` -/
lemma gC_eq_of_mem_Ioo (n : ℤ) {v : ℝ} (hv : v ∈ Ioo (n : ℝ) (n + 1)) :
    gC v = (2 : ℝ) ^ ((n : ℝ) + 1 - v) := by
  unfold gC
  have : ⌈v⌉ = n + 1 := by
    rw [Int.ceil_eq_iff]; push_cast; exact ⟨by linarith [hv.1], hv.2.le⟩
  rw [this]; push_cast; ring_nf

lemma gP_eq_of_mem_Ioo (n : ℤ) {v : ℝ} (hv : v ∈ Ioo (n : ℝ) (n + 1)) :
    gP v = (2 : ℝ) ^ ((n : ℝ) + 1 - v) := by
  unfold gP
  have : ⌊v⌋ = n := by
    rw [Int.floor_eq_iff]; exact ⟨hv.1.le, hv.2⟩
  rw [this]

lemma gC_lsc : LowerSemicontinuous gC := by
  intro u y hy
  by_cases h : ∃ z : ℤ, u = z
  · obtain ⟨z, rfl⟩ := h
    rw [gC_int] at hy
    exact Eventually.of_forall fun v => lt_of_lt_of_le hy (gC_ge_one v)
  · push_neg at h
    have h1 : (⌊u⌋ : ℝ) < u := lt_of_le_of_ne (Int.floor_le u) (fun e => h _ e.symm)
    have h2 : u < (⌊u⌋ : ℝ) + 1 := Int.lt_floor_add_one u
    have hmem : Ioo (⌊u⌋ : ℝ) (⌊u⌋ + 1) ∈ 𝓝 u := Ioo_mem_nhds h1 h2
    have hu : gC u = (2 : ℝ) ^ ((⌊u⌋ : ℝ) + 1 - u) := gC_eq_of_mem_Ioo _ ⟨h1, h2⟩
    have hc : ContinuousAt (fun v : ℝ => (2 : ℝ) ^ ((⌊u⌋ : ℝ) + 1 - v)) u := (cont_aux _).continuousAt
    have hev : ∀ᶠ v in 𝓝 u, y < (2 : ℝ) ^ ((⌊u⌋ : ℝ) + 1 - v) :=
      hc.eventually (lt_mem_nhds (by
        have h3 : y < (2 : ℝ) ^ ((⌊u⌋ : ℝ) + 1 - u) := by rw [← hu]; exact hy
        exact h3))
    filter_upwards [hev, hmem] with v hv hvm
    rw [gC_eq_of_mem_Ioo _ hvm]; exact hv

lemma gP_usc : UpperSemicontinuous gP := by
  intro u y hy
  by_cases h : ∃ z : ℤ, u = z
  · obtain ⟨z, rfl⟩ := h
    rw [gP_int] at hy
    exact Eventually.of_forall fun v => lt_of_le_of_lt (gP_le_two v) hy
  · push_neg at h
    have h1 : (⌊u⌋ : ℝ) < u := lt_of_le_of_ne (Int.floor_le u) (fun e => h _ e.symm)
    have h2 : u < (⌊u⌋ : ℝ) + 1 := Int.lt_floor_add_one u
    have hmem : Ioo (⌊u⌋ : ℝ) (⌊u⌋ + 1) ∈ 𝓝 u := Ioo_mem_nhds h1 h2
    have hu : gP u = (2 : ℝ) ^ ((⌊u⌋ : ℝ) + 1 - u) := gP_eq_of_mem_Ioo _ ⟨h1, h2⟩
    have hc : ContinuousAt (fun v : ℝ => (2 : ℝ) ^ ((⌊u⌋ : ℝ) + 1 - v)) u := (cont_aux _).continuousAt
    have hev : ∀ᶠ v in 𝓝 u, (2 : ℝ) ^ ((⌊u⌋ : ℝ) + 1 - v) < y :=
      hc.eventually (gt_mem_nhds (by
        have h3 : (2 : ℝ) ^ ((⌊u⌋ : ℝ) + 1 - u) < y := by rw [← hu]; exact hy
        exact h3))
    filter_upwards [hev, hmem] with v hv hvm
    rw [gP_eq_of_mem_Ioo _ hvm]; exact hv

/-- `gC` é contínua à esquerda -/
lemma tendsto_gC_left (u : ℝ) : Tendsto gC (𝓝[≤] u) (𝓝 (gC u)) := by
  set n := ⌈u⌉
  have hlt : (n : ℝ) - 1 < u := by linarith [Int.ceil_lt_add_one u]
  have hle : u ≤ n := Int.le_ceil u
  have hcont : Tendsto (fun v : ℝ => (2 : ℝ) ^ ((n : ℝ) - v)) (𝓝[≤] u) (𝓝 (gC u)) := by
    have := (cont_aux (n : ℝ)).tendsto u
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  refine hcont.congr' ?_
  filter_upwards [Ioc_mem_nhdsLE hlt] with v hv
  unfold gC
  have : ⌈v⌉ = n := by
    rw [Int.ceil_eq_iff]; exact ⟨hv.1, hv.2.trans hle⟩
  rw [this]

/-- à direita, `gC` tende a `gP` -/
lemma tendsto_gC_right (u : ℝ) : Tendsto gC (𝓝[>] u) (𝓝 (gP u)) := by
  have hlt : u < (⌊u⌋ : ℝ) + 1 := Int.lt_floor_add_one u
  have hcont : Tendsto (fun v : ℝ => (2 : ℝ) ^ (((⌊u⌋ : ℝ) + 1) - v)) (𝓝[>] u) (𝓝 (gP u)) :=
    tendsto_nhdsWithin_of_tendsto_nhds ((cont_aux ((⌊u⌋ : ℝ) + 1)).tendsto u)
  refine hcont.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT hlt] with v hv
  unfold gC
  have : ⌈v⌉ = ⌊u⌋ + 1 := by
    rw [Int.ceil_eq_iff]
    push_cast
    exact ⟨by linarith [Int.floor_le u, hv.1], hv.2⟩
  rw [this]; push_cast; rfl

/-- `gP` é contínua à direita -/
lemma tendsto_gP_right (u : ℝ) : Tendsto gP (𝓝[>] u) (𝓝 (gP u)) := by
  have hlt : u < (⌊u⌋ : ℝ) + 1 := Int.lt_floor_add_one u
  have hcont : Tendsto (fun v : ℝ => (2 : ℝ) ^ (((⌊u⌋ : ℝ) + 1) - v)) (𝓝[>] u) (𝓝 (gP u)) :=
    tendsto_nhdsWithin_of_tendsto_nhds ((cont_aux ((⌊u⌋ : ℝ) + 1)).tendsto u)
  refine hcont.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hlt] with v hv
  unfold gP
  have : ⌊v⌋ = ⌊u⌋ := by
    rw [Int.floor_eq_iff]; exact ⟨by linarith [Int.floor_le u, hv.1], hv.2⟩
  rw [this]

/-- à esquerda, `gP` tende a `gC` -/
lemma tendsto_gP_left (u : ℝ) : Tendsto gP (𝓝[<] u) (𝓝 (gC u)) := by
  set n := ⌈u⌉
  have hlt : (n : ℝ) - 1 < u := by linarith [Int.ceil_lt_add_one u]
  have hle : u ≤ n := Int.le_ceil u
  have hcont : Tendsto (fun v : ℝ => (2 : ℝ) ^ ((n : ℝ) - v)) (𝓝[<] u) (𝓝 (gC u)) :=
    tendsto_nhdsWithin_of_tendsto_nhds ((cont_aux (n : ℝ)).tendsto u)
  refine hcont.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hlt] with v hv
  unfold gP
  have : ⌊v⌋ = n - 1 := by
    rw [Int.floor_eq_iff]; push_cast; exact ⟨hv.1.le, by linarith [hv.2]⟩
  rw [this]; push_cast; ring_nf

end Pendencias
