module
public import RequestProject.Basic

/-!
# Seção 4: enumerações fixadas por fórmulas

Formalização da Seção 4 (`sec:enumeration`): pareamento triangular,
enumeração dos inteiros, ordens e postos dos racionais, e os
codificadores concretos de átomos.
-/

@[expose] public section

open scoped Classical

noncomputable section

namespace Montagens

/-! ## Pareamento e descompactação -/

/-- Números triangulares: `T(0) = 0`, `T(n+1) = T(n) + n + 1`. -/
def T : ℕ → ℕ
  | 0 => 0
  | n + 1 => T n + n + 1

/-- Pareamento `π(u, v) = T(u+v) + v`. -/
def pair (u v : ℕ) : ℕ := T (u + v) + v

theorem zero_mem_diagSet (n : ℕ) :
    0 ∈ (Finset.range (n + 1)).filter (fun j => T j ≤ n) := by
  simp [T]

/-- `w(n) = max {j ≤ n : T(j) ≤ n}`. -/
def wdiag (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun j => T j ≤ n)).max' ⟨0, zero_mem_diagSet n⟩

/-- `v(n) = n - T(w(n))` (subtração natural). -/
def vdiag (n : ℕ) : ℕ := n - T (wdiag n)

/-- `u(n) = w(n) - v(n)` (subtração natural). -/
def udiag (n : ℕ) : ℕ := wdiag n - vdiag n

/-- `π⁻¹(n) = (u(n), v(n))`. -/
def unpair (n : ℕ) : ℕ × ℕ := (udiag n, vdiag n)

/-- `pack(k, μ, r, t) = π(π(k, μ), π(r, t))`. -/
def pack (x : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  pair (pair x.1 x.2.1) (pair x.2.2.1 x.2.2.2)

/-- `unpack(n) = (k, μ, r, t)` com `(u,v) = π⁻¹(n)`, `(k,μ) = π⁻¹(u)`,
`(r,t) = π⁻¹(v)`. -/
def unpack (n : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  ((unpair (unpair n).1).1, (unpair (unpair n).1).2,
   (unpair (unpair n).2).1, (unpair (unpair n).2).2)

theorem T_two_mul (n : ℕ) : 2 * T n = n * (n + 1) := by
  induction n with
  | zero => simp [T]
  | succ n ih => simp only [T]; nlinarith

theorem T_strictMono : StrictMono T :=
  strictMono_nat_of_lt_succ (fun n => by simp only [T]; omega)

theorem le_T (n : ℕ) : n ≤ T n := by
  induction n with
  | zero => simp [T]
  | succ n ih => simp only [T]; omega

theorem wdiag_spec (n : ℕ) : T (wdiag n) ≤ n ∧ n < T (wdiag n + 1) := by
  have hmem := Finset.max'_mem ((Finset.range (n + 1)).filter (fun j => T j ≤ n))
    ⟨0, zero_mem_diagSet n⟩
  rw [← wdiag, Finset.mem_filter] at hmem
  refine ⟨hmem.2, ?_⟩
  by_contra hc
  push_neg at hc
  have h1 : wdiag n + 1 ∈ (Finset.range (n + 1)).filter (fun j => T j ≤ n) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := le_T (wdiag n + 1); omega, hc⟩
  have := Finset.le_max' _ _ h1
  rw [← wdiag] at this
  omega

theorem wdiag_eq_of {n w : ℕ} (h1 : T w ≤ n) (h2 : n < T (w + 1)) : wdiag n = w := by
  obtain ⟨h3, h4⟩ := wdiag_spec n
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := T_strictMono.monotone (show wdiag n + 1 ≤ w by omega); omega
  · have := T_strictMono.monotone (show w + 1 ≤ wdiag n by omega); omega

/-- Lema `lem:pair` (inversas do pareamento). -/
theorem pair_props :
    (∀ n, T (wdiag n) ≤ n ∧ n < T (wdiag n + 1) ∧ vdiag n ≤ wdiag n) ∧
    (∀ u v, unpair (pair u v) = (u, v)) ∧
    (∀ n, pair (unpair n).1 (unpair n).2 = n) ∧
    (∀ x, unpack (pack x) = x) ∧
    (∀ n, pack (unpack n) = n) ∧
    (∀ n, wdiag n = (Nat.sqrt (8 * n + 1) - 1) / 2) := by
  have h1 : ∀ n, T (wdiag n) ≤ n ∧ n < T (wdiag n + 1) ∧ vdiag n ≤ wdiag n := by
    intro n
    obtain ⟨a, b⟩ := wdiag_spec n
    refine ⟨a, b, ?_⟩
    simp only [T] at b; unfold vdiag; omega
  have h2 : ∀ u v, unpair (pair u v) = (u, v) := by
    intro u v
    have hw : wdiag (pair u v) = u + v := by
      apply wdiag_eq_of <;> simp only [pair, T] <;> omega
    have hv : vdiag (pair u v) = v := by rw [vdiag, hw]; simp only [pair]; omega
    simp only [unpair, udiag, hw, hv, Prod.mk.injEq, and_true]; omega
  have h3 : ∀ n, pair (unpair n).1 (unpair n).2 = n := by
    intro n
    obtain ⟨a, b, c⟩ := h1 n
    simp only [unpair, pair, udiag]
    rw [show wdiag n - vdiag n + vdiag n = wdiag n by omega]
    unfold vdiag; omega
  refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
  · rintro ⟨k, μ, r, t⟩
    simp [unpack, pack, h2]
  · intro n
    simp only [pack, unpack]
    rw [h3, h3, h3]
  · intro n
    obtain ⟨a, b, -⟩ := h1 n
    set w := wdiag n
    have hT := T_two_mul w
    have hT1 := T_two_mul (w + 1)
    have hs1 : 2 * w + 1 ≤ Nat.sqrt (8 * n + 1) := by
      rw [Nat.le_sqrt]; nlinarith
    have hs2 : Nat.sqrt (8 * n + 1) < 2 * w + 3 := by
      rw [Nat.sqrt_lt]; nlinarith
    omega

/-! ## Enumeração dos inteiros -/

/-- `Z : ℕ → ℤ`, definida por casos de paridade. -/
def Zenc (n : ℕ) : ℤ := if n % 2 = 0 then ((n / 2 : ℕ) : ℤ) else -(((n / 2 : ℕ) : ℤ) + 1)

/-- `Z⁻¹ : ℤ → ℕ`: `2m` se `m ≥ 0`, `-2m-1` se `m < 0`. -/
def Zinv (m : ℤ) : ℕ := if 0 ≤ m then (2 * m).toNat else (-2 * m - 1).toNat

theorem Zenc_even (j : ℕ) : Zenc (2 * j) = j := by
  simp [Zenc]

theorem Zenc_odd (j : ℕ) : Zenc (2 * j + 1) = -((j : ℤ) + 1) := by
  simp only [Zenc]; rw [if_neg (by omega)]; congr 3; omega

theorem Zinv_nonneg {m : ℤ} (h : 0 ≤ m) : (Zinv m : ℤ) = 2 * m := by
  simp only [Zinv, if_pos h]; omega

theorem Zinv_neg {m : ℤ} (h : m < 0) : (Zinv m : ℤ) = -2 * m - 1 := by
  simp only [Zinv, if_neg (not_le.2 h)]; omega

theorem Zenc_Zinv (m : ℤ) : Zenc (Zinv m) = m := by
  rcases le_or_gt 0 m with h | h
  · have h1 := Zinv_nonneg h
    unfold Zenc; rw [if_pos (by omega)]; omega
  · have h1 := Zinv_neg h
    unfold Zenc; rw [if_neg (by omega)]; omega

theorem Zinv_Zenc (n : ℕ) : Zinv (Zenc n) = n := by
  unfold Zenc
  split_ifs with h
  · have := Zinv_nonneg (m := ((n/2 : ℕ) : ℤ)) (by positivity); omega
  · have := Zinv_neg (m := -(((n/2 : ℕ) : ℤ) + 1)) (by omega); omega

/-! ## Ordens e postos dos racionais (Definição `def:rank`) -/

/-- `𝒬_H = {p/q : |p| ≤ H, 1 ≤ q ≤ H}` como conjunto finito de racionais. -/
def QH (H : ℕ) : Finset ℚ :=
  ((Finset.Icc (-(H : ℤ)) H) ×ˢ (Finset.Icc 1 H)).image
    (fun pq : ℤ × ℕ => (pq.1 : ℚ) / (pq.2 : ℚ))

/-- `𝒬_H` é exatamente `{r : ℚ | ht(r) ≤ H}`. -/
theorem mem_QH (H : ℕ) (r : ℚ) : r ∈ QH H ↔ ht r ≤ H := by
  unfold QH ht
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨p, q⟩, hpq, rfl⟩
    simp only [Finset.mem_product, Finset.mem_Icc] at hpq
    obtain ⟨⟨hp1, hp2⟩, hq1, hq2⟩ := hpq
    have hq0 : (q : ℤ) ≠ 0 := by omega
    have e : (p : ℚ) / (q : ℚ) = Rat.divInt p q := by rw [Rat.divInt_eq_div]; simp
    simp only [e]
    have hd := Int.le_of_dvd (by omega) (Rat.den_dvd p q)
    have hn := Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd p hq0)
    rcases eq_or_ne p 0 with h0 | h0
    · subst h0; simp; omega
    · have := hn h0
      apply max_le <;> omega
  · intro h
    refine ⟨(r.num, r.den), ?_, Rat.num_div_den r⟩
    simp only [Finset.mem_product, Finset.mem_Icc]
    have h1 := le_of_max_le_left h
    have h2 := le_of_max_le_right h
    have := r.den_pos
    omega

/-- As três fases de endereçamento `i ∈ {2, 3, c}`. -/
inductive Phase
  | two
  | three
  | con
  deriving DecidableEq

/-- A tripla `(ht(r), q(r), p(r))` na ordem lexicográfica. -/
def key2 (r : ℚ) : Lex (ℕ × Lex (ℕ × ℤ)) := toLex (ht r, toLex (r.den, r.num))

/-- A ordem `≺₂`: ordem lexicográfica da tripla `(ht(r), q(r), p(r))`. -/
def prec2 (r s : ℚ) : Prop := key2 r < key2 s

/-- A ordem `≺₃` é a mesma ordem `≺₂`. -/
def prec3 (r s : ℚ) : Prop := prec2 r s

/-- A chave natural `κ(r) = 4 ht(r)^3 + q(r)(2 ht(r) + 1) + (p(r) + ht(r))_ℕ`. -/
def kappa (r : ℚ) : ℕ :=
  4 * ht r ^ 3 + r.den * (2 * ht r + 1) + (r.num + (ht r : ℤ)).toNat

/-- A ordem consolidada `r ≺_c s :⟺ κ(r) < κ(s)`. -/
def precC (r s : ℚ) : Prop := kappa r < kappa s

/-- A ordem `≺_i` da fase `i`. -/
def prec : Phase → ℚ → ℚ → Prop
  | .two => prec2
  | .three => prec3
  | .con => precC

/-- `Pred_i(r) = {v ∈ 𝒬_{ht(r)} : v ≺_i r}`. -/
def Pred (i : Phase) (r : ℚ) : Finset ℚ := (QH (ht r)).filter (fun v => prec i v r)

/-- `rank_i(r) = |Pred_i(r)|`. -/
def rank (i : Phase) (r : ℚ) : ℕ := (Pred i r).card

/-- `Pred*_i(r) = {v : ℚ^× : v.1 ∈ 𝒬_{ht(r.1)}, v.1 ≺_i r.1}`. -/
def PredStar (i : Phase) (r : Qstar) : Finset Qstar :=
  ((QH (ht r.1)).subtype (fun v => v ≠ 0)).filter (fun v => prec i v.1 r.1)

/-- `rank*_i(r) = |Pred*_i(r)|`. -/
def rankStar (i : Phase) (r : Qstar) : ℕ := (PredStar i r).card

theorem key2_injective : Function.Injective key2 := by
  intro r s h
  simp only [key2, toLex_inj, Prod.mk.injEq] at h
  exact Rat.ext h.2.2 h.2.1

theorem num_bounds (r : ℚ) : -(ht r : ℤ) ≤ r.num ∧ r.num ≤ ht r := by
  have := (ht_props r).2.1
  omega

theorem kappa_lt_of_key2_lt {r s : ℚ} (h : key2 r < key2 s) : kappa r < kappa s := by
  unfold key2 at h
  rw [Prod.Lex.toLex_lt_toLex] at h
  have hr := ht_props r
  have hs := ht_props s
  have nr := num_bounds r
  have ns := num_bounds s
  unfold kappa
  have er : ((r.num + (ht r : ℤ)).toNat : ℤ) = r.num + ht r := Int.toNat_of_nonneg (by omega)
  have es : ((s.num + (ht s : ℤ)).toNat : ℤ) = s.num + ht s := Int.toNat_of_nonneg (by omega)
  have br : (r.num + (ht r : ℤ)).toNat ≤ 2 * ht r := by omega
  rcases h with h | ⟨h1, h⟩
  · simp only at h
    have h3 : (ht r + 1) ^ 3 ≤ ht s ^ 3 := Nat.pow_le_pow_left h 3
    have : r.den * (2 * ht r + 1) ≤ ht r * (2 * ht r + 1) := Nat.mul_le_mul_right _ hr.2.2
    nlinarith
  · simp only at h1 h
    rw [Prod.Lex.toLex_lt_toLex] at h
    rw [h1]
    rcases h with h | ⟨h2, h⟩
    · simp only at h
      have : (r.den + 1) * (2 * ht s + 1) ≤ s.den * (2 * ht s + 1) := Nat.mul_le_mul_right _ h
      rw [h1] at br
      nlinarith
    · simp only at h2 h
      rw [h2]
      have : (r.num + (ht s : ℤ)).toNat < (s.num + (ht s : ℤ)).toNat := by
        rw [h1] at er; omega
      omega

/-- A ordem `≺_c` (pela chave `κ`) é precisamente a ordem lexicográfica `≺₂`. -/
theorem precC_iff (r s : ℚ) : precC r s ↔ prec2 r s := by
  unfold precC prec2
  constructor
  · intro h
    by_contra hc
    rcases lt_or_eq_of_le (not_lt.1 hc) with h' | h'
    · exact lt_asymm h (kappa_lt_of_key2_lt h')
    · rw [key2_injective h'] at h; exact lt_irrefl _ h
  · exact kappa_lt_of_key2_lt

/-- Lema `lem:rank`, primeira parte: as três ordens coincidem. -/
theorem prec_coincide (i : Phase) (r s : ℚ) : prec i r s ↔ prec2 r s := by
  cases i
  · rfl
  · rfl
  · exact precC_iff r s

theorem ht_le_of_key2_lt {v r : ℚ} (h : key2 v < key2 r) : ht v ≤ ht r := by
  unfold key2 at h
  rw [Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

theorem mem_Pred_iff (i : Phase) (r v : ℚ) : v ∈ Pred i r ↔ key2 v < key2 r := by
  unfold Pred
  rw [Finset.mem_filter, mem_QH, prec_coincide]
  exact ⟨fun h => h.2, fun h => ⟨ht_le_of_key2_lt h, h⟩⟩

theorem mem_PredStar_iff (i : Phase) (r v : Qstar) :
    v ∈ PredStar i r ↔ key2 v.1 < key2 r.1 := by
  unfold PredStar
  rw [Finset.mem_filter, Finset.mem_subtype, mem_QH, prec_coincide]
  exact ⟨fun h => h.2, fun h => ⟨ht_le_of_key2_lt h, h⟩⟩

instance : Infinite Qstar :=
  Infinite.of_injective (fun n : ℕ => (⟨(n : ℚ) + 1, by positivity⟩ : Qstar))
    (fun a b h => by simpa using h)

/-- Em uma ordem linear infinita (dada por uma chave injetiva) com conjuntos
finitos de predecessores, o posto por cardinalidade é bijetivo. -/
theorem rank_bij_generic {X : Type*} [Infinite X] {B : Type*} [LinearOrder B] (f : X → B)
    (hf : Function.Injective f) (P : X → Finset X) (hP : ∀ r v, v ∈ P r ↔ f v < f r) :
    Function.Bijective (fun r => (P r).card) := by
  have hmono : ∀ a b, f a < f b → (P a).card < (P b).card := by
    intro a b hab
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨a, (hP b a).2 hab, fun h => lt_irrefl _ ((hP a a).1 h)⟩
    · intro v hv; exact (hP b v).2 (lt_trans ((hP a v).1 hv) hab)
  have hinj : Function.Injective (fun r => (P r).card) := by
    intro a b h
    by_contra hne
    rcases lt_or_gt_of_ne (hf.ne hne) with h1 | h1
    · exact absurd h (ne_of_lt (hmono _ _ h1))
    · exact absurd h (ne_of_gt (hmono _ _ h1))
  refine ⟨hinj, ?_⟩
  have hstep : ∀ b n, (P b).card = n + 1 → ∃ a, (P a).card = n := by
    intro b n hb
    have hne : (P b).Nonempty := by rw [← Finset.card_pos]; omega
    obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image (P b) f hne
    refine ⟨a, ?_⟩
    have : P a = (P b).erase a := by
      ext v
      rw [Finset.mem_erase, hP, hP]
      constructor
      · intro hv; exact ⟨fun h => by subst h; exact lt_irrefl _ hv, lt_trans hv ((hP b a).1 ha)⟩
      · rintro ⟨hva, hv⟩
        exact lt_of_le_of_ne (hmax v ((hP b v).2 hv)) (fun h => hva (hf h))
    rw [this, Finset.card_erase_of_mem ha, hb]; rfl
  have hdown : ∀ m k b, (P b).card = m + k → ∃ a, (P a).card = m := by
    intro m k
    induction k with
    | zero => intro b hb; exact ⟨b, hb⟩
    | succ k ih =>
      intro b hb
      obtain ⟨a, ha⟩ := hstep b (m + k) (by omega)
      exact ih a ha
  intro m
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := (Set.infinite_range_of_injective hinj).exists_gt m
  exact hdown m ((P b).card - m) b (by simp only at hb; omega)

/-- Lema `lem:rank`: os conjuntos de predecessores contêm todos os
predecessores na ordem respectiva. -/
theorem mem_Pred_of_prec (i : Phase) {r v : ℚ} (h : prec i v r) : v ∈ Pred i r := by
  exact (mem_Pred_iff i r v).2 ((prec_coincide i v r).1 h)

theorem mem_PredStar_of_prec (i : Phase) {r v : Qstar} (h : prec i v.1 r.1) :
    v ∈ PredStar i r := by
  exact (mem_PredStar_iff i r v).2 ((prec_coincide i v.1 r.1).1 h)

/-- Lema `lem:rank`: cada `rank_i` é bijetiva. -/
theorem rank_bijective (i : Phase) : Function.Bijective (rank i) := by
  exact rank_bij_generic key2 key2_injective (Pred i) (fun r v => mem_Pred_iff i r v)

/-- Lema `lem:rank`: cada `rank*_i` é bijetiva. -/
theorem rankStar_bijective (i : Phase) : Function.Bijective (rankStar i) := by
  exact rank_bij_generic (fun v : Qstar => key2 v.1)
    (fun a b h => Subtype.ext (key2_injective h)) (PredStar i) (fun r v => mem_PredStar_iff i r v)

/-- A enumeração inversa `Q_i : ℕ → ℚ`, com `rank_i(Q_i(n)) = n`. -/
def Qenum (i : Phase) (n : ℕ) : ℚ := Function.surjInv (rank_bijective i).2 n

/-- A enumeração inversa `Q*_i : ℕ → ℚ^×`, com `rank*_i(Q*_i(n)) = n`. -/
def QstarEnum (i : Phase) (n : ℕ) : Qstar := Function.surjInv (rankStar_bijective i).2 n

theorem rank_Qenum (i : Phase) (n : ℕ) : rank i (Qenum i n) = n :=
  Function.surjInv_eq _ n

theorem rankStar_QstarEnum (i : Phase) (n : ℕ) : rankStar i (QstarEnum i n) = n :=
  Function.surjInv_eq _ n

theorem Qenum_rank (i : Phase) (r : ℚ) : Qenum i (rank i r) = r :=
  (rank_bijective i).1 (rank_Qenum i _)

theorem QstarEnum_rankStar (i : Phase) (s : Qstar) : QstarEnum i (rankStar i s) = s :=
  (rankStar_bijective i).1 (rankStar_QstarEnum i _)

/-! ## Codificadores concretos de átomos (Definição `def:codec`) -/

/-- `enc_i(a) = pack(a.k, Z⁻¹(a.m), rank_i(a.y), rank*_i(⟨a.s, h_s⟩))`. -/
def enc (i : Phase) (a : Atom) : ℕ :=
  pack (a.k, Zinv a.m, rank i a.y, rankStar i ⟨a.s, a.hs⟩)

/-- `dec_i(n) = (k, Z(μ), Q_i(r), (Q*_i(t)).1, (Q*_i(t)).2)` com
`(k, μ, r, t) = unpack(n)`. -/
def dec (i : Phase) (n : ℕ) : Atom :=
  ⟨(unpack n).1, Zenc (unpack n).2.1, Qenum i (unpack n).2.2.1,
    (QstarEnum i (unpack n).2.2.2).1, (QstarEnum i (unpack n).2.2.2).2⟩

/-- `C_i(n) = C(dec_i(n))`. -/
def Ci (i : Phase) (n : ℕ) : Cell := (dec i n).C
/-- `U_i(n) = u(dec_i(n))`. -/
def Ui (i : Phase) (n : ℕ) : ℚ := (dec i n).u
/-- `B_i(n) = b(dec_i(n))`. -/
def Bi (i : Phase) (n : ℕ) : ℚ := (dec i n).b
/-- `λ_i(n, x) = ↑U_i(n) + ↑B_i(n) x`. -/
def lam (i : Phase) (n : ℕ) (x : ℝ) : ℝ := (Ui i n : ℝ) + (Bi i n : ℝ) * x

/-- Reendereçamento `τ_{i→j} = enc_j ∘ dec_i`. -/
def tau (i j : Phase) (n : ℕ) : ℕ := enc j (dec i n)

theorem dec_k (i : Phase) (n : ℕ) : (dec i n).k = (unpack n).1 := rfl
theorem dec_m (i : Phase) (n : ℕ) : (dec i n).m = Zenc (unpack n).2.1 := rfl
theorem dec_y (i : Phase) (n : ℕ) : (dec i n).y = Qenum i (unpack n).2.2.1 := rfl
theorem dec_s (i : Phase) (n : ℕ) : (dec i n).s = (QstarEnum i (unpack n).2.2.2).1 := rfl
theorem enc_eq (i : Phase) (a : Atom) :
    enc i a = pack (a.k, Zinv a.m, rank i a.y, rankStar i ⟨a.s, a.hs⟩) := rfl

/-- Lema `lem:codec` (contrato completo de endereçamento), primeira parte. -/
theorem codec (i : Phase) :
    (∀ a, dec i (enc i a) = a) ∧ (∀ n, enc i (dec i n) = n) ∧
    (∀ n x, lam i n x = (dec i n).line x) := by
  refine ⟨fun a => ?_, fun n => ?_, fun n x => ?_⟩
  · have h := pair_props.2.2.2.1 (a.k, Zinv a.m, rank i a.y, rankStar i ⟨a.s, a.hs⟩)
    apply Atom.ext
    · rw [dec_k, enc_eq, h]
    · rw [dec_m, enc_eq, h]; exact Zenc_Zinv a.m
    · rw [dec_y, enc_eq, h]; exact Qenum_rank i a.y
    · rw [dec_s, enc_eq, h]; simp only [QstarEnum_rankStar]
  · rw [enc_eq]
    have : (⟨(dec i n).s, (dec i n).hs⟩ : Qstar) = QstarEnum i (unpack n).2.2.2 :=
      Subtype.ext (dec_s i n)
    rw [this, dec_k, dec_m, dec_y, Zinv_Zenc, rank_Qenum, rankStar_QstarEnum]
    exact pair_props.2.2.2.2.1 n
  · unfold lam Ui Bi
    rw [(line_forms (dec i n)).1 x]

/-- Lema `lem:codec`, propriedades do reendereçamento. -/
theorem tau_props (i j : Phase) (n : ℕ) (x : ℝ) :
    dec j (tau i j n) = dec i n ∧ Ci j (tau i j n) = Ci i n ∧
    lam j (tau i j n) x = lam i n x := by
  have h : dec j (tau i j n) = dec i n := (codec j).1 _
  refine ⟨h, ?_, ?_⟩
  · simp only [Ci, h]
  · rw [(codec j).2.2, (codec i).2.2, h]

end Montagens

end
