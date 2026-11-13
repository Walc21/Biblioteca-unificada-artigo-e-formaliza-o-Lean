module
public import RequestProject.Sec7.Interp
public import RequestProject.Sec7.Formats
@[expose] public section

/-!
# Theorem 7.16: simultaneous control of error, leaves, height and bits

For `f ∈ 𝓕_{R,M}` and `n = 2^r ≥ 2`, the nodal values are `v_j = b_j/(2n²)`, where `b_j ≡ j (mod 2)`
is the integer nearest to `2n² f(j/n)` (ties towards the smaller one), i.e. `v_j` is the point of
the alternating grid `G_j = n^{-2}(ℤ + (j mod 2)/2)` nearest to `f(t_j)`.  The assembly `g_n` is
their dyadic interpolant.
-/

open Set Finset

namespace Dyadic.Lib

/-- The constant `C_H = max{4(R+1), 2(C₀+1)}` (eq. (71)). -/
noncomputable def CH (R M : ℝ) : ℝ := max (4 * (R + 1)) (2 * (C0 R M + 1))

/-- The alternating grid `G_j^{(n)} = Δ(ℤ + (j mod 2)/2)`, `Δ = n^{-2}`, `n = 2^r` (eq. (76)). -/
def altGrid (r j : ℕ) : Set ℝ :=
  {w | ∃ z : ℤ, w = 1 / ((2 : ℝ) ^ r) ^ 2 * (z + ((j % 2 : ℕ) : ℝ) / 2)}

/-- The numerator `b_j` of eq. (77). -/
noncomputable def bNum (f : ℝ → ℝ) (r j : ℕ) : ℤ :=
  gridNum (2 * ((2 : ℝ) ^ r) ^ 2 * f (j / 2 ^ r)) (j % 2)

/-- The nodal value `v_j = b_j / (2n²)`. -/
noncomputable def vNode (f : ℝ → ℝ) (r j : ℕ) : ℚ := bNum f r j / (2 * ((2 : ℚ) ^ r) ^ 2)

lemma bNum_mod (f : ℝ → ℝ) (r j : ℕ) : bNum f r j ≡ (j % 2 : ℕ) [ZMOD 2] := gridNum_mod _ _

lemma vNode_ne (f : ℝ → ℝ) (r : ℕ) (j : ℕ) : vNode f r (j + 1) ≠ vNode f r j := by
  intro h
  have h' : bNum f r (j + 1) = bNum f r j := by
    unfold vNode at h
    have hpos : (2 * ((2 : ℚ) ^ r) ^ 2) ≠ 0 := by positivity
    rw [div_left_inj' hpos] at h
    exact_mod_cast h
  have h1 := bNum_mod f r (j + 1)
  have h2 := bNum_mod f r j
  rw [h'] at h1
  have := h1.symm.trans h2
  rw [Int.ModEq] at this
  push_cast at this
  omega

/-- The leaves of `g_n` (`j < n`). -/
noncomputable def leafAtom (f : ℝ → ℝ) (r : ℕ) : ℕ → Atom := interpAtom r (vNode f r) (vNode_ne f r)

/-- The assembly `g_n` of Theorem 7.16 (`n = 2^r`). -/
noncomputable def gN (f : ℝ → ℝ) (r : ℕ) : ℝ → ℝ := chainFun (leafAtom f r) (2 ^ r)

/-- Its set of leaves. -/
noncomputable def leavesN (f : ℝ → ℝ) (r : ℕ) : Finset Atom :=
  (Finset.range (2 ^ r)).image (leafAtom f r)

section

variable {R M : ℝ} {f : ℝ → ℝ}

lemma FRM.R_nonneg (hf : f ∈ FRM R M) : 0 ≤ R :=
  (abs_nonneg _).trans (hf.2.1 0 (left_mem_Icc.2 zero_le_one))

lemma FRM.M_nonneg (hf : f ∈ FRM R M) : 0 ≤ M :=
  (abs_nonneg _).trans (hf.2.2 0 (left_mem_Icc.2 zero_le_one))

lemma C0_nonneg (hf : f ∈ FRM R M) : 0 ≤ C0 R M := by
  unfold C0; linarith [FRM.R_nonneg hf, FRM.M_nonneg hf]

lemma node_mem {r j : ℕ} (hj : j ≤ 2 ^ r) : (j : ℝ) / 2 ^ r ∈ Icc (0 : ℝ) 1 :=
  ⟨by positivity, by rw [div_le_one (by positivity)]; exact_mod_cast hj⟩

lemma vNode_cast (r j : ℕ) : ((vNode f r j : ℚ) : ℝ) = bNum f r j / (2 * ((2 : ℝ) ^ r) ^ 2) := by
  simp [vNode]

/-- `|v_j - f(t_j)| ≤ 1/(2n²)`. -/
lemma vNode_sub_le (r j : ℕ) :
    |((vNode f r j : ℚ) : ℝ) - f (j / 2 ^ r)| ≤ 1 / (2 * ((2 : ℝ) ^ r) ^ 2) := by
  rw [vNode_cast]
  have h := gridNum_sub_le (2 * ((2 : ℝ) ^ r) ^ 2 * f (j / 2 ^ r)) (j % 2)
  have hpos : (0 : ℝ) < 2 * ((2 : ℝ) ^ r) ^ 2 := by positivity
  have e : (bNum f r j : ℝ) / (2 * ((2 : ℝ) ^ r) ^ 2) - f (j / 2 ^ r) =
      ((gridNum (2 * ((2 : ℝ) ^ r) ^ 2 * f (j / 2 ^ r)) (j % 2) : ℝ) -
        2 * ((2 : ℝ) ^ r) ^ 2 * f (j / 2 ^ r)) / (2 * ((2 : ℝ) ^ r) ^ 2) := by
    unfold bNum; field_simp
  rw [e, abs_div, abs_of_pos hpos]
  exact div_le_div_of_nonneg_right h hpos.le

/-- `|b_j| ≤ 2Rn² + 1` (eq. (78)). -/
lemma bNum_abs_le (hf : f ∈ FRM R M) {r j : ℕ} (hj : j ≤ 2 ^ r) :
    |(bNum f r j : ℝ)| ≤ 2 * R * ((2 : ℝ) ^ r) ^ 2 + 1 := by
  have h := gridNum_sub_le (2 * ((2 : ℝ) ^ r) ^ 2 * f (j / 2 ^ r)) (j % 2)
  have hR := hf.2.1 _ (node_mem hj)
  have hn : (0 : ℝ) ≤ 2 * ((2 : ℝ) ^ r) ^ 2 := by positivity
  have : |2 * ((2 : ℝ) ^ r) ^ 2 * f (j / 2 ^ r)| ≤ 2 * ((2 : ℝ) ^ r) ^ 2 * R := by
    rw [abs_mul, abs_of_nonneg hn]; exact mul_le_mul_of_nonneg_left hR hn
  unfold bNum
  have := abs_sub_abs_le_abs_sub (gridNum (2 * ((2 : ℝ) ^ r) ^ 2 * f (j / 2 ^ r)) (j % 2) : ℝ)
    (2 * ((2 : ℝ) ^ r) ^ 2 * f (j / 2 ^ r))
  linarith

/-- `|b_{j+1} - b_j| ≤ 2C₀n + 2` (eq. (80)). -/
lemma bNum_diff_le (hf : f ∈ FRM R M) {r j : ℕ} (hj : j + 1 ≤ 2 ^ r) :
    |(bNum f r (j + 1) : ℝ) - bNum f r j| ≤ 2 * C0 R M * 2 ^ r + 2 := by
  have h1 := gridNum_sub_le (2 * ((2 : ℝ) ^ r) ^ 2 * f ((j + 1 : ℕ) / 2 ^ r)) ((j + 1) % 2)
  have h2 := gridNum_sub_le (2 * ((2 : ℝ) ^ r) ^ 2 * f (j / 2 ^ r)) (j % 2)
  have hL := FRM.lipschitz hf (node_mem (r := r) (j := j) (by omega)) (node_mem hj)
  have hd : ((j + 1 : ℕ) : ℝ) / 2 ^ r - j / 2 ^ r = 1 / 2 ^ r := by push_cast; field_simp; ring
  rw [hd, abs_of_pos (show (0 : ℝ) < 1 / 2 ^ r by positivity)] at hL
  have hn : (0 : ℝ) < 2 ^ r := by positivity
  have key : |2 * ((2 : ℝ) ^ r) ^ 2 * f ((j + 1 : ℕ) / 2 ^ r) -
      2 * ((2 : ℝ) ^ r) ^ 2 * f (j / 2 ^ r)| ≤ 2 * C0 R M * 2 ^ r := by
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity)]
    calc 2 * ((2 : ℝ) ^ r) ^ 2 * |f ((j + 1 : ℕ) / 2 ^ r) - f (j / 2 ^ r)|
        ≤ 2 * ((2 : ℝ) ^ r) ^ 2 * (C0 R M * (1 / 2 ^ r)) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ = 2 * C0 R M * 2 ^ r := by field_simp
  unfold bNum
  rw [abs_le] at h1 h2 key ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, key.1, key.2]

lemma natCast_height_le (a : Atom) {X : ℝ} (h2 : 2 ≤ X) (hk : (a.k : ℝ) + 1 ≤ X)
    (hm : (a.m.natAbs : ℝ) + 1 ≤ X) (hy : (ratHeight a.y0 : ℝ) ≤ X) (hs : (ratHeight a.s : ℝ) ≤ X) :
    (a.height : ℝ) ≤ X := by
  unfold Atom.height
  push_cast [Nat.cast_max]
  exact max_le (max_le h2 hk) (max_le hm (max_le hy hs))

lemma ratHeight_intDiv_le_real (n : ℤ) (d : ℕ) (hd : 0 < d) :
    (ratHeight ((n : ℚ) / (d : ℚ)) : ℝ) ≤ max (|(n : ℝ)|) d := by
  have := ratHeight_intDiv_le n d hd
  have h' : ((max n.natAbs d : ℕ) : ℝ) = max (|(n : ℝ)|) d := by
    push_cast [Nat.cast_max]; rw [Nat.cast_natAbs, Int.cast_abs]
  rw [← h']; exact_mod_cast this

lemma leafAtom_y0 (r j : ℕ) : (leafAtom f r j).y0 =
    ((bNum f r j + bNum f r (j + 1) : ℤ) : ℚ) / ((4 * (2 ^ r) ^ 2 : ℕ) : ℚ) := by
  simp only [leafAtom, interpAtom, vNode]; push_cast; field_simp; ring

lemma leafAtom_s (r j : ℕ) : (leafAtom f r j).s =
    ((bNum f r (j + 1) - bNum f r j : ℤ) : ℚ) / ((2 * 2 ^ r : ℕ) : ℚ) := by
  simp only [leafAtom, interpAtom, vNode]; push_cast; field_simp

/-- eq. (81): `ht(y_{0,j}) ≤ 4(R+1)n²`. -/
lemma leafAtom_y0_height (hf : f ∈ FRM R M) {r j : ℕ} (hj : j < 2 ^ r) :
    (ratHeight (leafAtom f r j).y0 : ℝ) ≤ 4 * (R + 1) * ((2 : ℝ) ^ r) ^ 2 := by
  rw [leafAtom_y0]
  refine (ratHeight_intDiv_le_real _ _ (by positivity)).trans (max_le ?_ ?_)
  · have h1 := bNum_abs_le hf (r := r) (j := j) hj.le
    have h2 := bNum_abs_le hf (r := r) (j := j + 1) hj
    have hn : (1 : ℝ) ≤ ((2 : ℝ) ^ r) ^ 2 := one_le_pow₀ (one_le_pow₀ (by norm_num))
    push_cast
    calc |(bNum f r j : ℝ) + bNum f r (j + 1)| ≤ |(bNum f r j : ℝ)| + |(bNum f r (j + 1) : ℝ)| :=
          abs_add_le _ _
      _ ≤ 4 * (R + 1) * ((2 : ℝ) ^ r) ^ 2 := by nlinarith
  · push_cast
    have := FRM.R_nonneg hf
    have : (0 : ℝ) ≤ ((2 : ℝ) ^ r) ^ 2 := by positivity
    nlinarith

/-- eq. (81): `ht(s_j) ≤ 2(C₀+1)n`. -/
lemma leafAtom_s_height (hf : f ∈ FRM R M) {r j : ℕ} (hj : j < 2 ^ r) :
    (ratHeight (leafAtom f r j).s : ℝ) ≤ 2 * (C0 R M + 1) * 2 ^ r := by
  rw [leafAtom_s]
  refine (ratHeight_intDiv_le_real _ _ (by positivity)).trans (max_le ?_ ?_)
  · have h := bNum_diff_le hf (r := r) (j := j) hj
    have hn : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
    push_cast
    nlinarith
  · push_cast
    have := C0_nonneg hf
    have : (0 : ℝ) ≤ 2 ^ r := by positivity
    nlinarith

lemma CH_ge (R M : ℝ) : 4 * (R + 1) ≤ CH R M ∧ 2 * (C0 R M + 1) ≤ CH R M :=
  ⟨le_max_left _ _, le_max_right _ _⟩

/-- eq. (73): every leaf of `g_n` has height `≤ C_H n²`. -/
lemma leafAtom_height (hf : f ∈ FRM R M) {r j : ℕ} (hj : j < 2 ^ r) :
    ((leafAtom f r j).height : ℝ) ≤ CH R M * ((2 : ℝ) ^ r) ^ 2 := by
  have hR := FRM.R_nonneg hf
  have hC := C0_nonneg hf
  obtain ⟨h1, h2⟩ := CH_ge R M
  have hn1 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have hnn : (2 : ℝ) ^ r ≤ ((2 : ℝ) ^ r) ^ 2 := by nlinarith
  have hr : (r : ℝ) + 1 ≤ 2 ^ r := by exact_mod_cast Nat.lt_two_pow_self (n := r)
  have hjr : (j : ℝ) + 1 ≤ 2 ^ r := by exact_mod_cast hj
  have hCH : 4 ≤ CH R M := by linarith
  apply natCast_height_le
  · nlinarith
  · simp only [leafAtom, interpAtom]; nlinarith
  · simp only [leafAtom, interpAtom, Int.natAbs_natCast]; nlinarith
  · exact (leafAtom_y0_height hf hj).trans (by nlinarith)
  · exact (leafAtom_s_height hf hj).trans (by nlinarith)

lemma leavesN_height (hf : f ∈ FRM R M) (r : ℕ) :
    ∀ a ∈ leavesN f r, (a.height : ℝ) ≤ CH R M * ((2 : ℝ) ^ r) ^ 2 := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ha
  exact leafAtom_height hf (Finset.mem_range.1 hj)

/-- eq. (72): `‖f - g_n‖ ≤ (M+4)/(8n²)`. -/
lemma gN_error (hf : f ∈ FRM R M) (r : ℕ) :
    ∀ x ∈ Icc (0 : ℝ) 1, |f x - gN f r x| ≤ (M + 4) / (8 * ((2 : ℝ) ^ r) ^ 2) := by
  intro x hx
  have h := interp_error (r := r) (v := vNode f r) (hv := vNode_ne f r) (FRM.M_nonneg hf)
    (fun p q hp hq => FRM.c2bound hf hp hq) (fun j _ => vNode_sub_le r j) x hx
  have e : M / (8 * ((2 : ℝ) ^ r) ^ 2) + 1 / (2 * ((2 : ℝ) ^ r) ^ 2) =
      (M + 4) / (8 * ((2 : ℝ) ^ r) ^ 2) := by field_simp; ring
  rw [← e]; exact h

/-- The nodal value `v_j` is the point of `G_j` nearest to `f(t_j)`, ties broken towards the
smaller point. -/
lemma vNode_nearest (r j : ℕ) :
    ((vNode f r j : ℚ) : ℝ) ∈ altGrid r j ∧
    ∀ w ∈ altGrid r j, |((vNode f r j : ℚ) : ℝ) - f (j / 2 ^ r)| ≤ |w - f (j / 2 ^ r)| ∧
      (|((vNode f r j : ℚ) : ℝ) - f (j / 2 ^ r)| = |w - f (j / 2 ^ r)| →
        ((vNode f r j : ℚ) : ℝ) ≤ w) := by
  set y := 2 * ((2 : ℝ) ^ r) ^ 2 * f (j / 2 ^ r)
  have hpos : (0 : ℝ) < 2 * ((2 : ℝ) ^ r) ^ 2 := by positivity
  have hscale : ∀ b : ℤ, |(b : ℝ) / (2 * ((2 : ℝ) ^ r) ^ 2) - f (j / 2 ^ r)| =
      |(b : ℝ) - y| / (2 * ((2 : ℝ) ^ r) ^ 2) := by
    intro b
    rw [← abs_of_pos hpos, ← abs_div, abs_of_pos hpos]
    congr 1; simp only [y]; field_simp
  have hgrid : ∀ w ∈ altGrid r j, ∃ b : ℤ, b ≡ (j % 2 : ℕ) [ZMOD 2] ∧
      w = (b : ℝ) / (2 * ((2 : ℝ) ^ r) ^ 2) := by
    rintro w ⟨z, rfl⟩
    refine ⟨2 * z + (j % 2 : ℕ), Int.modEq_iff_dvd.2 ⟨-z, by ring⟩, ?_⟩
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]; field_simp
  refine ⟨?_, fun w hw => ?_⟩
  · obtain ⟨z, hz⟩ : ∃ z : ℤ, bNum f r j = 2 * z + (j % 2 : ℕ) := by
      obtain ⟨c, hc⟩ := Int.ModEq.dvd (bNum_mod f r j).symm
      exact ⟨c, by linarith⟩
    refine ⟨z, ?_⟩
    rw [vNode_cast, hz]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]; field_simp
  · obtain ⟨b, hb, rfl⟩ := hgrid w hw
    obtain ⟨o1, o2⟩ := gridNum_optimal y (j % 2) b hb
    rw [vNode_cast, hscale, hscale]
    refine ⟨div_le_div_of_nonneg_right o1 hpos.le, fun heq => ?_⟩
    have := o2 ((div_left_inj' hpos.ne').1 heq)
    exact div_le_div_of_nonneg_right (by exact_mod_cast this) hpos.le

lemma gN_mem_AsmNH (hf : f ∈ FRM R M) {r N H : ℕ} (hN : 2 ^ r ≤ N)
    (hH : CH R M * ((2 : ℝ) ^ r) ^ 2 ≤ H) : gN f r ∈ AsmNH (Icc 0 1) N H := by
  obtain ⟨hrep, hcard, hasm⟩ := interp_isAssemblyRep (r := r) (v := vNode f r) (hv := vNode_ne f r)
  refine ⟨hasm.1, leavesN f r, hrep, ?_, fun a ha => ?_⟩
  · unfold leavesN leafAtom; rw [hcard]; exact hN
  · have := (leavesN_height hf r a ha).trans hH
    exact_mod_cast this

lemma jointError_le_of_mem {K : Set ℝ} {N H : ℕ} {f g : ℝ → ℝ} (hg : g ∈ AsmNH K N H) {e : ℝ}
    (he : 0 ≤ e) (hfg : ∀ x ∈ K, |f x - g x| ≤ e) : jointError K N H f ≤ ENNReal.ofReal e :=
  (biInf_le (fun g => supDist K f g) hg).trans ((supDist_le_iff he).2 hfg)

/-- eq. (75): `E_{N, ⌈C_H N²⌉}(f) < (M+4)/(2N²)` for every `N ≥ 2`. -/
lemma jointError_lt (hf : f ∈ FRM R M) {N : ℕ} (hN : 2 ≤ N) :
    jointError (Icc 0 1) N ⌈CH R M * (N : ℝ) ^ 2⌉₊ f <
      ENNReal.ofReal ((M + 4) / (2 * (N : ℝ) ^ 2)) := by
  set r := Nat.log 2 N
  have h1 : 2 ^ r ≤ N := Nat.pow_log_le_self 2 (by omega)
  have h2 : N < 2 ^ (r + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hM := FRM.M_nonneg hf
  have hCH : 0 ≤ CH R M := by linarith [(CH_ge R M).1, FRM.R_nonneg hf]
  have hn1 : ((2 : ℝ) ^ r) ≤ N := by exact_mod_cast h1
  have hn2 : (N : ℝ) < 2 * 2 ^ r := by
    have : ((N : ℕ) : ℝ) < ((2 ^ (r + 1) : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this; rw [pow_succ] at this; linarith
  have hg : gN f r ∈ AsmNH (Icc 0 1) N ⌈CH R M * (N : ℝ) ^ 2⌉₊ := by
    apply gN_mem_AsmNH hf h1
    refine le_trans ?_ (Nat.le_ceil _)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hn1 2) hCH
  refine lt_of_le_of_lt (jointError_le_of_mem hg (by positivity) (gN_error hf r)) ?_
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  have hpos : (0 : ℝ) < 2 ^ r := by positivity
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have : (N : ℝ) ^ 2 < 4 * ((2 : ℝ) ^ r) ^ 2 := by nlinarith
  nlinarith

end

end Dyadic.Lib

namespace Dyadic.Lib

/-! ### Bit lengths (eq. (74)) -/

/-- Length of `C_ReLU,rat` when all its parameters have height `≤ P`. -/
lemma streamRat_length_le_heights (a : ℕ → Atom) {N P : ℕ}
    (h0 : ratHeight (a 0).intercept ≤ P) (hs : ratHeight (a 0).s ≤ P)
    (hj : ∀ p ∈ jumps a N, ratHeight p.1 ≤ P ∧ ratHeight p.2 ≤ P) :
    (streamRat a N).length ≤ (2 * Nat.log 2 N + 1) + 2 * (2 * (eliasGamma (2 * P + 1)).length) +
      (N - 1) * (2 * (2 * (eliasGamma (2 * P + 1)).length)) := by
  unfold streamRat
  simp only [List.length_append, length_eliasGamma]
  have e1 := length_codeRat_le h0
  have e2 := length_codeRat_le hs
  have e3 := length_flatten_le (jumps a N) codePairRat (2 * (2 * (eliasGamma (2 * P + 1)).length))
    (fun p hp => by
      obtain ⟨h1, h2⟩ := hj p hp
      simp only [codePairRat, List.length_append]
      have := length_codeRat_le h1
      have := length_codeRat_le h2
      omega)
  rw [length_jumps] at e3
  simp only [length_eliasGamma] at e1 e2 e3 ⊢
  omega

variable {R M : ℝ} {f : ℝ → ℝ}

lemma logb_two_pow_succ (r : ℕ) : Real.logb 2 (2 * (2 : ℝ) ^ r) = r + 1 := by
  rw [← pow_succ', Real.logb_pow]; simp

lemma CH_pos (hf : f ∈ FRM R M) : 4 ≤ CH R M := by
  linarith [(CH_ge R M).1, FRM.R_nonneg hf]

/-- Bits of the atomic and structural streams of `g_n`. -/
lemma gN_bits_atom_str (hf : f ∈ FRM R M) {r : ℕ} :
    ((streamAtom (leafAtom f r) (2 ^ r)).length : ℝ) ≤
        200 * (Real.logb 2 (CH R M) + 2) * 2 ^ r * (r + 1) ∧
    ((streamStr (leafAtom f r) (2 ^ r)).length : ℝ) ≤
        200 * (Real.logb 2 (CH R M) + 2) * 2 ^ r * (r + 1) := by
  have hCH := CH_pos hf
  have hn1 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  set X := CH R M * ((2 : ℝ) ^ r) ^ 2
  have hX : 4 ≤ X := by
    have : (1 : ℝ) ≤ ((2 : ℝ) ^ r) ^ 2 := one_le_pow₀ hn1
    nlinarith
  set H0 := ⌊X⌋₊
  have hH0 : 2 ≤ H0 := Nat.le_floor (by push_cast; linarith)
  have hht : ∀ j < 2 ^ r, (leafAtom f r j).height ≤ H0 :=
    fun j hj => Nat.le_floor (leafAtom_height hf hj)
  obtain ⟨b1, b2, -⟩ := formats_length_bounds (leafAtom f r) Nat.one_le_two_pow hH0 hht
  have hlog : Real.logb 2 H0 ≤ Real.logb 2 (CH R M) + 2 * r := by
    have h1 : (H0 : ℝ) ≤ X := Nat.floor_le (by linarith)
    have h2 : (0 : ℝ) < H0 := by exact_mod_cast (show 0 < H0 by omega)
    calc Real.logb 2 H0 ≤ Real.logb 2 X := Real.logb_le_logb_of_le (by norm_num) h2 h1
      _ = Real.logb 2 (CH R M) + 2 * r := by
          simp only [X]
          rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow]
          simp
  have hlc : 0 ≤ Real.logb 2 (CH R M) := Real.logb_nonneg (by norm_num) (by linarith)
  have hr : (0 : ℝ) ≤ r := by positivity
  have key : 200 * ((2 ^ r : ℕ) : ℝ) * Real.logb 2 H0 ≤
      200 * (Real.logb 2 (CH R M) + 2) * 2 ^ r * (r + 1) := by
    push_cast
    have : Real.logb 2 (CH R M) + 2 * r ≤ (Real.logb 2 (CH R M) + 2) * (r + 1) := by nlinarith
    have hpos : (0 : ℝ) ≤ 200 * 2 ^ r := by positivity
    calc 200 * (2 : ℝ) ^ r * Real.logb 2 H0 ≤ 200 * 2 ^ r * (Real.logb 2 (CH R M) + 2 * r) :=
          mul_le_mul_of_nonneg_left hlog hpos
      _ ≤ 200 * 2 ^ r * ((Real.logb 2 (CH R M) + 2) * (r + 1)) :=
          mul_le_mul_of_nonneg_left this hpos
      _ = _ := by ring
  exact ⟨b1.trans key, b2.trans key⟩

lemma leafAtom_intercept (r : ℕ) : (leafAtom f r 0).intercept = vNode f r 0 := by
  have h := interpAtom_line (r := r) (v := vNode f r) (hv := vNode_ne f r) 0 0
  rw [Atom.line_eq] at h
  simp at h
  exact_mod_cast h

set_option maxHeartbeats 1000000 in
/-- Bits of the expanded ReLU stream of `g_n`. -/
lemma gN_bits_rat (hf : f ∈ FRM R M) {r : ℕ} :
    ((streamRat (leafAtom f r) (2 ^ r)).length : ℝ) ≤
        (8 * Real.logb 2 (6 * CH R M ^ 2) + 40) * 2 ^ r * (r + 1) := by
  have hCH := CH_pos hf
  have hR := FRM.R_nonneg hf
  have hC := C0_nonneg hf
  obtain ⟨c1, c2⟩ := CH_ge R M
  have hn1 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  set X := CH R M * ((2 : ℝ) ^ r) ^ 2
  have hX1 : 1 ≤ X := by
    have : (1 : ℝ) ≤ ((2 : ℝ) ^ r) ^ 2 := one_le_pow₀ hn1
    nlinarith
  set P := ⌊2 * X ^ 2⌋₊
  have hXP : X ≤ 2 * X ^ 2 := by nlinarith
  have hP1 : 1 ≤ P := Nat.le_floor (by push_cast; nlinarith)
  -- all parameters have height `≤ P`
  have hsX : ∀ j < 2 ^ r, (ratHeight (leafAtom f r j).s : ℝ) ≤ X := fun j hj =>
    (leafAtom_s_height hf hj).trans (by
      have h1 : (2 : ℝ) ^ r ≤ ((2 : ℝ) ^ r) ^ 2 := by nlinarith
      exact mul_le_mul c2 h1 (by positivity) (by linarith))
  have h0 : ratHeight (leafAtom f r 0).intercept ≤ P := by
    apply Nat.le_floor
    rw [leafAtom_intercept]
    have e : vNode f r 0 = ((bNum f r 0 : ℤ) : ℚ) / ((2 * (2 ^ r) ^ 2 : ℕ) : ℚ) := by
      simp [vNode]
    rw [e]
    refine (ratHeight_intDiv_le_real _ _ (by positivity)).trans (max_le ?_ ?_)
    · have := bNum_abs_le hf (r := r) (j := 0) (Nat.zero_le _)
      have : (1 : ℝ) ≤ ((2 : ℝ) ^ r) ^ 2 := one_le_pow₀ hn1
      nlinarith
    · push_cast; nlinarith
  have hs : ratHeight (leafAtom f r 0).s ≤ P :=
    Nat.le_floor ((hsX 0 (by positivity)).trans hXP)
  have hj : ∀ p ∈ jumps (leafAtom f r) (2 ^ r), ratHeight p.1 ≤ P ∧ ratHeight p.2 ≤ P := by
    intro p hp
    simp only [jumps, List.mem_map, List.mem_range'] at hp
    obtain ⟨j, ⟨i, hi, hij⟩, rfl⟩ := hp
    have hjn : j < 2 ^ r := by omega
    constructor
    · apply Nat.le_floor
      have := ratHeight_dyadic_le (j : ℤ) r
      have h' : ((leafAtom f r j).left) = ((j : ℤ) : ℚ) / 2 ^ r := by
        simp [leafAtom, interpAtom, Atom.left]
      rw [h']
      have h4 : max (j : ℤ).natAbs (2 ^ r) = 2 ^ r := max_eq_right (by simp; omega)
      have h2 : (ratHeight (((j : ℤ) : ℚ) / 2 ^ r) : ℝ) ≤ 2 ^ r := by
        exact_mod_cast (this.trans h4.le)
      have : (2 : ℝ) ^ r ≤ X := by
        have : (2 : ℝ) ^ r ≤ ((2 : ℝ) ^ r) ^ 2 := by nlinarith
        nlinarith
      linarith
    · apply Nat.le_floor
      have e := ratHeight_sub_le (leafAtom f r j).s (leafAtom f r (j - 1)).s
      have e' : (ratHeight ((leafAtom f r j).s - (leafAtom f r (j - 1)).s) : ℝ) ≤
          2 * ratHeight (leafAtom f r j).s * ratHeight (leafAtom f r (j - 1)).s := by
        exact_mod_cast e
      have a1 := hsX j hjn
      have a2 := hsX (j - 1) (by omega)
      have : (2 : ℝ) * ratHeight (leafAtom f r j).s * ratHeight (leafAtom f r (j - 1)).s ≤
          2 * X * X := by
        have := mul_le_mul a1 a2 (by positivity) (by linarith)
        nlinarith
      push_cast; nlinarith
  have hlen := streamRat_length_le_heights (leafAtom f r) h0 hs hj
  -- convert to reals
  set G := (eliasGamma (2 * P + 1)).length
  have hG : (G : ℝ) ≤ 2 * (Real.logb 2 (6 * CH R M ^ 2) + 4 * r) + 1 := by
    refine (length_eliasGamma_le _).trans ?_
    have hP3 : ((2 * P + 1 : ℕ) : ℝ) ≤ 6 * CH R M ^ 2 * (2 ^ r) ^ 4 := by
      have : (P : ℝ) ≤ 2 * X ^ 2 := Nat.floor_le (by positivity)
      have : (1 : ℝ) ≤ P := by exact_mod_cast hP1
      push_cast
      have : 2 * X ^ 2 = 2 * CH R M ^ 2 * ((2 : ℝ) ^ r) ^ 4 := by simp only [X]; ring
      nlinarith
    have : Real.logb 2 ((2 * P + 1 : ℕ) : ℝ) ≤ Real.logb 2 (6 * CH R M ^ 2 * (2 ^ r) ^ 4) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) hP3
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow] at this
    simp at this
    push_cast at this ⊢
    linarith
  have hlr : (Nat.log 2 (2 ^ r) : ℝ) = r := by rw [Nat.log_pow (by norm_num)]
  have hlen' : ((streamRat (leafAtom f r) (2 ^ r)).length : ℝ) ≤ (2 * r + 1) + 4 * G +
      ((2 ^ r - 1 : ℕ) : ℝ) * (4 * G) := by
    have := hlen
    have h' : ((streamRat (leafAtom f r) (2 ^ r)).length : ℝ) ≤
        ((2 * Nat.log 2 (2 ^ r) + 1 + 2 * (2 * G) + (2 ^ r - 1) * (2 * (2 * G)) : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast [Nat.cast_sub Nat.one_le_two_pow] at h' ⊢
    rw [hlr] at h'
    linarith
  have hL6 : 0 ≤ Real.logb 2 (6 * CH R M ^ 2) := Real.logb_nonneg (by norm_num) (by nlinarith)
  have hr : (0 : ℝ) ≤ r := by positivity
  have hG' : (G : ℝ) ≤ (2 * Real.logb 2 (6 * CH R M ^ 2) + 9) * (r + 1) := by nlinarith
  have e1 : (2 : ℝ) ^ r * (4 * G) ≤ 2 ^ r * (4 * ((2 * Real.logb 2 (6 * CH R M ^ 2) + 9) * (r + 1))) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e2 : (2 : ℝ) * r + 1 ≤ 4 * 2 ^ r * (r + 1) := by nlinarith
  have e3 : 4 * (G : ℝ) + ((2 : ℝ) ^ r - 1) * (4 * G) = 2 ^ r * (4 * G) := by ring
  have e4 : ((2 ^ r - 1 : ℕ) : ℝ) = 2 ^ r - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  rw [e4] at hlen'
  linarith

/-- **Theorem 7.16** (simultaneous control of error, leaves, height and bits).  Let `R, M` be
fixed and `C_H = max{4(R+1), 2(C₀+1)}`.  For every dyadic power `n = 2^r ≥ 2` and every
`f ∈ 𝓕_{R,M}`, the assembly `g_n` (dyadic interpolant of the nodal values `v_j ∈ G_j^{(n)}`
nearest to `f(j/n)`, ties broken towards the smaller grid point) has exactly `n` leaves and
satisfies (72) `‖f - g_n‖ ≤ (M+4)/(8n²)` and (73) `ht_max(g_n) ≤ C_H n²`; in the three formats
of Theorem 7.12 its length is `O_{R,M}(n log(2n))` (74); and for every `N ≥ 2`,
`E_{N,⌈C_H N²⌉}(f) < (M+4)/(2N²)` (75). -/
theorem simultaneous_control (R M : ℝ) :
    (∀ f ∈ FRM R M, ∀ r : ℕ, 1 ≤ r →
      IsAssemblyRep (Icc 0 1) (gN f r) (leavesN f r) ∧ (leavesN f r).card = 2 ^ r ∧
      gN f r ∈ Asm (Icc 0 1) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, |f x - gN f r x| ≤ (M + 4) / (8 * ((2 : ℝ) ^ r) ^ 2)) ∧
      (∀ a ∈ leavesN f r, (a.height : ℝ) ≤ CH R M * ((2 : ℝ) ^ r) ^ 2) ∧
      (∀ j : ℕ, ((vNode f r j : ℚ) : ℝ) ∈ altGrid r j ∧
        ∀ w ∈ altGrid r j, |((vNode f r j : ℚ) : ℝ) - f (j / 2 ^ r)| ≤ |w - f (j / 2 ^ r)| ∧
          (|((vNode f r j : ℚ) : ℝ) - f (j / 2 ^ r)| = |w - f (j / 2 ^ r)| →
            ((vNode f r j : ℚ) : ℝ) ≤ w))) ∧
    (∃ C : ℝ, ∀ f ∈ FRM R M, ∀ r : ℕ, 1 ≤ r →
      ((streamAtom (leafAtom f r) (2 ^ r)).length : ℝ) ≤
        C * 2 ^ r * Real.logb 2 (2 * 2 ^ r) ∧
      ((streamStr (leafAtom f r) (2 ^ r)).length : ℝ) ≤
        C * 2 ^ r * Real.logb 2 (2 * 2 ^ r) ∧
      ((streamRat (leafAtom f r) (2 ^ r)).length : ℝ) ≤
        C * 2 ^ r * Real.logb 2 (2 * 2 ^ r)) ∧
    (∀ f ∈ FRM R M, ∀ N : ℕ, 2 ≤ N →
      jointError (Icc 0 1) N ⌈CH R M * (N : ℝ) ^ 2⌉₊ f <
        ENNReal.ofReal ((M + 4) / (2 * (N : ℝ) ^ 2))) := by
  refine ⟨fun f hf r _ => ?_, ?_, fun f hf N hN => jointError_lt hf hN⟩
  · obtain ⟨hrep, hcard, hasm⟩ :=
      interp_isAssemblyRep (r := r) (v := vNode f r) (hv := vNode_ne f r)
    exact ⟨hrep, hcard, hasm, gN_error hf r, leavesN_height hf r, fun j => vNode_nearest r j⟩
  · set C := 200 * (|Real.logb 2 (CH R M)| + 2) + (8 * |Real.logb 2 (6 * CH R M ^ 2)| + 40)
    refine ⟨C, fun f hf r _ => ?_⟩
    obtain ⟨b1, b2⟩ := gN_bits_atom_str hf (r := r)
    have b3 := gN_bits_rat hf (r := r)
    rw [logb_two_pow_succ]
    have hr : (0 : ℝ) ≤ (2 : ℝ) ^ r * (r + 1) := by positivity
    have a1 := le_abs_self (Real.logb 2 (CH R M))
    have a2 := le_abs_self (Real.logb 2 (6 * CH R M ^ 2))
    have a3 := abs_nonneg (Real.logb 2 (CH R M))
    have a4 := abs_nonneg (Real.logb 2 (6 * CH R M ^ 2))
    have k1 : 200 * (Real.logb 2 (CH R M) + 2) ≤ C := by simp only [C]; linarith
    have k2 : 8 * Real.logb 2 (6 * CH R M ^ 2) + 40 ≤ C := by simp only [C]; linarith
    have m1 : 200 * (Real.logb 2 (CH R M) + 2) * 2 ^ r * (r + 1) ≤ C * 2 ^ r * (r + 1) := by
      calc _ = 200 * (Real.logb 2 (CH R M) + 2) * (2 ^ r * (r + 1)) := by ring
        _ ≤ C * (2 ^ r * (r + 1)) := mul_le_mul_of_nonneg_right k1 hr
        _ = _ := by ring
    have m2 : (8 * Real.logb 2 (6 * CH R M ^ 2) + 40) * 2 ^ r * (r + 1) ≤ C * 2 ^ r * (r + 1) := by
      calc _ = (8 * Real.logb 2 (6 * CH R M ^ 2) + 40) * (2 ^ r * (r + 1)) := by ring
        _ ≤ C * (2 ^ r * (r + 1)) := mul_le_mul_of_nonneg_right k2 hr
        _ = _ := by ring
    exact ⟨b1.trans m1, b2.trans m1, b3.trans m2⟩

end Dyadic.Lib
