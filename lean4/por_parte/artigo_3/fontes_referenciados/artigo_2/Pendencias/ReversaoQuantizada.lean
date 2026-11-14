import Pendencias.ReversaoOriginal
import Pendencias.AlturaInversa
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# IV.5.5 — reversão aproximada quantizada (`map:artigo_3:5.5`)

Teorema final: `Pendencias.Marcada.QuantIV55.quantized_approximate_reverse`.
Para uma forma ReLU reduzida real `R` com `|c|,|q|,|a_j| ≤ W` (`W ≥ 1`) e `0 < ε ≤ 1`, existe
uma montagem `U` da biblioteca original (`LTree.WF 0 0 U`) com erro uniforme `≤ ε` em `[0,1]`,
`|Λ(U)| ≤ 1 + M D_ε` e altura atômica máxima `≤ C (M+1)³ (W+1)³ ε⁻²`, com `C = 320`.
Usa a cota corrigida de IV.5.4 apenas no espírito (altura canônica com denominador comum, sem
`W^(M+3)`), provada aqui em `Hcan_leQ`; não depende da cota impressa antiga.

Estratégia (a do TeX): arredondar `c,q,a_j` a múltiplos de `1/Q`, `Q = ⌈4(M+2)/ε⌉`; as quebras
`τ_j` a `j/2^D` com `1 ≤ j ≤ 2^D-1`; somar `t/Q`, `1 ≤ t ≤ M+2`, à inclinação global para anular
nenhuma inclinação local (princípio das gavetas: no máximo `M+1` valores proibidos); aplicar a
montagem canônica de IV.5.2 (`canonTree_representation_bounds`) e transportá-la para `LTree`.
-/

/-!
# IV.5.5 — parte 1: altura canônica com denominador comum

Variante da cota de `AlturaInversa` quando todos os coeficientes são múltiplos de `1/Q`:
`H_can(R) ≤ Q · 2^(D+1) · (M+2) · B`, com `B` majorando os módulos dos coeficientes.
Não há potência `W^(M+3)`: o denominador comum não cresce com `M`.
-/

namespace Pendencias.Marcada

open Artigo

namespace QuantIV55

open AlturaInversa

lemma inteiro_listsum (n : ℕ) (g : ℚ × ℚ → ℚ) :
    ∀ l : List (ℚ × ℚ), (∀ p ∈ l, Inteiro n (p.1 * g p)) →
      Inteiro n ((l.map fun p => p.1 * g p).sum)
  | [], _ => ⟨0, by simp⟩
  | p :: l, h => by
      simp only [List.map_cons, List.sum_cons]
      exact (h p (by simp)).add (inteiro_listsum n g l fun p' hp' => h p' (List.mem_cons_of_mem _ hp'))

/-- hipóteses: coeficientes em `(1/Q)ℤ`, módulos `≤ B`, quebras diádicas em `(0,1)`, profundidade `≤ D`. -/
structure HipQ (R : RedReLU) (Q B D : ℕ) : Prop where
  hQ : 0 < Q
  hB : 1 ≤ B
  ic : Inteiro Q R.c
  iq : Inteiro Q R.q
  ia : ∀ p ∈ R.data, Inteiro Q p.1
  bc : |R.c| ≤ B
  bq : |R.q| ≤ B
  ba : ∀ p ∈ R.data, |p.1| ≤ B
  hτ : ∀ p ∈ R.data, IsDyadic p.2 ∧ 0 < p.2 ∧ p.2 < 1
  hD : R.depth ≤ D

lemma HipQ.log_le {R : RedReLU} {Q B D : ℕ} (h : HipQ R Q B D) (p : ℚ × ℚ) (hp : p ∈ R.data) :
    Nat.log 2 p.2.den ≤ D := by
  have hmem : p.2 ∈ R.breaks := by
    unfold RedReLU.breaks
    rw [List.mem_toFinset]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  exact le_trans (Finset.le_sup (f := fun τ : ℚ => Nat.log 2 τ.den) hmem) h.hD

lemma ht_slope_leQ (R : RedReLU) {Q B D : ℕ} (h : HipQ R Q B D) (x : ℚ) :
    ht (R.slopeAt x) ≤ Q * ((R.data.length + 1) * B) := by
  rw [slopeAt_eq]
  have hS : Inteiro Q ((R.data.map fun p => p.1 * (if p.2 ≤ x then (1 : ℚ) else 0)).sum) :=
    inteiro_listsum Q (fun p => if p.2 ≤ x then (1 : ℚ) else 0) R.data fun p hp =>
      ((h.ia p hp).mul (inteiro_ite _)).mono ⟨1, by ring⟩
  have hI : Inteiro Q (R.q + (R.data.map fun p => p.1 * (if p.2 ≤ x then (1 : ℚ) else 0)).sum) :=
    h.iq.add hS
  have hsum := abs_sum_le (B : ℚ) (fun p => if p.2 ≤ x then (1 : ℚ) else 0) R.data
    (fun p hp => (h.ba p hp)) (fun p _ => by by_cases hp : p.2 ≤ x <;> simp [hp])
    (by positivity)
  have hB : |R.q + (R.data.map fun p => p.1 * (if p.2 ≤ x then (1 : ℚ) else 0)).sum|
      ≤ (((R.data.length + 1) * B : ℕ) : ℚ) := by
    refine (abs_add_le _ _).trans ?_
    push_cast
    nlinarith [h.bq]
  have key := ht_le_of_inteiro h.hQ hI hB
  have hmax : max ((R.data.length + 1) * B) 1 = (R.data.length + 1) * B :=
    max_eq_left (Nat.one_le_iff_ne_zero.mpr (by have := h.hB; positivity))
  rwa [hmax] at key

lemma ht_evalQ_leQ (R : RedReLU) {Q B D : ℕ} (h : HipQ R Q B D) (x : ℚ)
    (hxI : Inteiro (2 ^ (D + 1)) x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ht (R.evalQ x) ≤ Q * 2 ^ (D + 1) * ((R.data.length + 2) * B) := by
  have hg : ∀ p ∈ R.data, Inteiro (2 ^ (D + 1)) (max 0 (x - p.2)) := by
    intro p hp
    obtain ⟨hdy, _, _⟩ := h.hτ p hp
    have hs : Inteiro (2 ^ (D + 1)) (x - p.2) := hxI.sub (inteiro_dyadic _ D hdy (h.log_le p hp))
    rcases max_choice (0 : ℚ) (x - p.2) with e | e
    · rw [e]; exact inteiro_zero _
    · rw [e]; exact hs
  have hS : Inteiro (Q * 2 ^ (D + 1)) ((R.data.map fun p => p.1 * max 0 (x - p.2)).sum) :=
    inteiro_listsum _ (fun p => max 0 (x - p.2)) R.data fun p hp => (h.ia p hp).mul (hg p hp)
  have hqx : Inteiro (Q * 2 ^ (D + 1)) (R.q * x) := h.iq.mul hxI
  have hI : Inteiro (Q * 2 ^ (D + 1)) (R.evalQ x) := by
    unfold RedReLU.evalQ
    exact ((h.ic.mono ⟨2 ^ (D + 1), rfl⟩).add hqx).add hS
  have hsum := abs_sum_le (B : ℚ) (fun p => max 0 (x - p.2)) R.data
    (fun p hp => h.ba p hp)
    (fun p hp => by
      obtain ⟨_, hτ0, _⟩ := h.hτ p hp
      exact abs_le.mpr ⟨le_trans (by norm_num) (le_max_left _ _),
        max_le (by norm_num) (by linarith)⟩)
    (by positivity)
  have hqx' : |R.q * x| ≤ B := by
    rw [abs_mul, abs_of_nonneg hx0]
    calc |R.q| * x ≤ B * 1 := mul_le_mul h.bq hx1 hx0 (by positivity)
      _ = B := mul_one _
  have hB : |R.evalQ x| ≤ (((R.data.length + 2) * B : ℕ) : ℚ) := by
    unfold RedReLU.evalQ
    refine (abs_add_le _ _).trans ?_
    have h1 := abs_add_le R.c (R.q * x)
    push_cast
    nlinarith [h.bc]
  have hN : 0 < Q * 2 ^ (D + 1) := Nat.mul_pos h.hQ (by positivity)
  have key := ht_le_of_inteiro hN hI hB
  have hmax : max ((R.data.length + 2) * B) 1 = (R.data.length + 2) * B :=
    max_eq_left (Nat.one_le_iff_ne_zero.mpr (by have := h.hB; positivity))
  rwa [hmax] at key

lemma hShape_leaf_leQ (R : RedReLU) {Q B D : ℕ} (h : HipQ R Q B D) (k : ℕ) (m : ℤ) (hk : k ≤ D)
    (hm0 : 0 ≤ m) (hm : m < 2 ^ k) :
    R.hShape .leaf k m ≤ Q * 2 ^ (D + 1) * ((R.data.length + 2) * B) := by
  have hQ := h.hQ
  have hB := h.hB
  set M := R.data.length with hM
  have hE : D + 1 < 2 ^ (D + 1) := Nat.lt_two_pow_self
  have hBd : 2 ^ (D + 1) ≤ Q * 2 ^ (D + 1) * ((M + 2) * B) :=
    calc 2 ^ (D + 1) = 1 * 2 ^ (D + 1) * 1 := by ring
      _ ≤ Q * 2 ^ (D + 1) * ((M + 2) * B) :=
        Nat.mul_le_mul (Nat.mul_le_mul hQ le_rfl) (by nlinarith)
  have habs : m.natAbs < 2 ^ k := by
    have h1 : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg hm0
    have h2 : ((m.natAbs : ℕ) : ℤ) < ((2 ^ k : ℕ) : ℤ) := by
      rw [h1]; push_cast; exact hm
    exact_mod_cast h2
  have h2k : 2 ^ k ≤ 2 ^ (D + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hxI : Inteiro (2 ^ (D + 1)) (((m : ℚ) + 1 / 2) / 2 ^ k) := inteiro_center k D hk m
  have hm0' : (0 : ℚ) ≤ m := by exact_mod_cast hm0
  have hm1 : (m : ℚ) + 1 ≤ 2 ^ k := by exact_mod_cast (show m + 1 ≤ 2 ^ k by omega)
  have hx0 : (0 : ℚ) ≤ ((m : ℚ) + 1 / 2) / 2 ^ k := by positivity
  have hx1 : ((m : ℚ) + 1 / 2) / 2 ^ k ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hval := ht_evalQ_leQ R h _ hxI hx0 hx1
  have hslope := ht_slope_leQ R h ((m : ℚ) / 2 ^ k)
  rw [← hM] at hval hslope
  have hslope' : ht (R.slopeAt ((m : ℚ) / 2 ^ k)) ≤ Q * 2 ^ (D + 1) * ((M + 2) * B) := by
    refine hslope.trans ?_
    calc Q * ((M + 1) * B) ≤ Q * (1 * ((M + 2) * B)) := by
          rw [one_mul]; exact
          Nat.mul_le_mul le_rfl (Nat.mul_le_mul (by omega : M + 1 ≤ M + 2) le_rfl)
      _ ≤ Q * 2 ^ (D + 1) * ((M + 2) * B) := by
          rw [mul_assoc]
          exact Nat.mul_le_mul le_rfl (Nat.mul_le_mul (Nat.one_le_two_pow) le_rfl)
  simp only [RedReLU.hShape]
  refine max_le (max_le (max_le (max_le ?_ ?_) ?_) hval) hslope'
  · omega
  · omega
  · omega

lemma hShape_canon_leQ (R : RedReLU) {Q B D : ℕ} (h : HipQ R Q B D) :
    ∀ (d k : ℕ) (m : ℤ), 0 ≤ m → m < 2 ^ k → k + d ≤ D →
      R.hShape (canonShape R.breaks d k m) k m ≤
        Q * 2 ^ (D + 1) * ((R.data.length + 2) * B) := by
  intro d
  induction d with
  | zero =>
      intro k m hm0 hm hkd
      simp only [canonShape]
      exact hShape_leaf_leQ R h k m (by omega) hm0 hm
  | succ d ih =>
      intro k m hm0 hm hkd
      unfold canonShape
      split_ifs with hex
      · simp only [RedReLU.hShape]
        have hm' : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
        refine max_le (ih (k + 1) (2 * m) (by omega) (by omega) (by omega))
          (ih (k + 1) (2 * m + 1) (by omega) (by omega) (by omega))
      · exact hShape_leaf_leQ R h k m (by omega) hm0 hm

/-- **Altura canônica com denominador comum**: `H_can(R) ≤ Q 2^(D+1) (M+2) B`. -/
theorem Hcan_leQ (R : RedReLU) {Q B D : ℕ} (h : HipQ R Q B D) :
    R.Hcan ≤ Q * 2 ^ (D + 1) * ((R.data.length + 2) * B) := by
  unfold RedReLU.Hcan
  exact hShape_canon_leQ R h R.depth 0 0 le_rfl (by norm_num) (by simpa using h.hD)

end QuantIV55

end Pendencias.Marcada

/-!
# IV.5.5 — parte 2: quantização dos parâmetros e erro

Dados reais `(c, q, a_j, τ_j)` são arredondados: `c, q, a_j` para múltiplos de `1/Q` e `τ_j`
para `j/2^D` com `1 ≤ j ≤ 2^D - 1` (nunca em `0` ou `1`, evitando absorver nós no domínio).
-/

namespace Pendencias.Marcada

open Artigo

namespace QuantIV55

open AlturaInversa

/-- Arredondamento de `x` ao múltiplo mais próximo de `1/Q`. -/
noncomputable def rq (Q : ℕ) (x : ℝ) : ℚ := (round (x * Q) : ℚ) / Q

lemma rq_err {Q : ℕ} (hQ : 0 < Q) (x : ℝ) : |x - (rq Q x : ℝ)| ≤ 1 / (2 * Q) := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h := abs_sub_round (x * Q)
  have : x - (rq Q x : ℝ) = (x * Q - round (x * Q)) / Q := by
    unfold rq; push_cast; field_simp
  rw [this, abs_div, abs_of_pos hQ', div_le_div_iff₀ hQ' (by positivity)]
  nlinarith

lemma rq_inteiro {Q : ℕ} (hQ : 0 < Q) (x : ℝ) : Inteiro Q (rq Q x) := by
  refine ⟨round (x * Q), ?_⟩
  unfold rq
  have : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  field_simp

lemma rq_abs_le {Q : ℕ} (hQ : 0 < Q) (x W : ℝ) (h : |x| ≤ W) : |(rq Q x : ℝ)| ≤ W + 1 / (2 * Q) := by
  have := rq_err hQ x
  calc |(rq Q x : ℝ)| = |x - (x - (rq Q x : ℝ))| := by ring_nf
    _ ≤ |x| + |x - (rq Q x : ℝ)| := abs_sub _ _
    _ ≤ _ := by linarith

/-- quebra quantizada: `j / 2^D` com `j = max 1 ⌊t 2^D⌋`. -/
noncomputable def jt (D : ℕ) (t : ℝ) : ℤ := max 1 ⌊t * 2 ^ D⌋

noncomputable def tq (D : ℕ) (t : ℝ) : ℚ := (jt D t : ℚ) / 2 ^ D

lemma jt_bounds {D : ℕ} (hD : 1 ≤ D) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    1 ≤ jt D t ∧ jt D t ≤ 2 ^ D - 1 ∧ |t - (tq D t : ℝ)| ≤ 1 / 2 ^ D := by
  have h2 : (2 : ℤ) ≤ 2 ^ D := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ D := pow_le_pow_right₀ (by norm_num) hD
  have hp : (0 : ℝ) < 2 ^ D := by positivity
  have hu0 : 0 < t * 2 ^ D := by positivity
  have hu1 : t * 2 ^ D < 2 ^ D := by nlinarith
  have hfl : ⌊t * 2 ^ D⌋ < 2 ^ D := by
    rw [Int.floor_lt]; push_cast; exact hu1
  refine ⟨le_max_left _ _, max_le (by omega) (by omega), ?_⟩
  have hflo := Int.floor_le (t * 2 ^ D)
  have hfhi := Int.lt_floor_add_one (t * 2 ^ D)
  have key : |t * 2 ^ D - (jt D t : ℝ)| ≤ 1 := by
    unfold jt
    by_cases hc : 1 ≤ ⌊t * 2 ^ D⌋
    · rw [max_eq_right hc, abs_le]; constructor <;> linarith
    · have hc' : ⌊t * 2 ^ D⌋ ≤ 0 := by omega
      have hc'' : (⌊t * 2 ^ D⌋ : ℝ) ≤ 0 := by exact_mod_cast hc'
      rw [max_eq_left (by omega)]
      push_cast
      rw [abs_le]; constructor <;> linarith
  have : (t : ℝ) - (tq D t : ℝ) = (t * 2 ^ D - (jt D t : ℝ)) / 2 ^ D := by
    unfold tq; push_cast; field_simp
  rw [this, abs_div, abs_of_pos hp]
  exact div_le_div_of_nonneg_right key hp.le

lemma tq_pos_lt_one {D : ℕ} (hD : 1 ≤ D) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    0 < tq D t ∧ tq D t < 1 := by
  obtain ⟨a, b, _⟩ := jt_bounds hD h0 h1
  have hp : (0 : ℚ) < 2 ^ D := by positivity
  unfold tq
  constructor
  · apply div_pos _ hp
    exact_mod_cast (by omega : (0 : ℤ) < jt D t)
  · rw [div_lt_one hp]
    have : ((jt D t : ℤ) : ℚ) ≤ ((2 ^ D - 1 : ℤ) : ℚ) := by exact_mod_cast b
    push_cast at this
    linarith

lemma den_dvd_of_inteiro {n : ℕ} {q : ℚ} (h : Inteiro n q) : q.den ∣ n := by
  obtain ⟨z, hz⟩ := h
  have h1 : (q.num : ℚ) * n = z * q.den := by
    have := Rat.mul_den_eq_num q
    calc (q.num : ℚ) * n = (q * q.den) * n := by rw [this]
      _ = (q * n) * q.den := by ring
      _ = z * q.den := by rw [hz]
  have h2 : q.num * (n : ℤ) = z * q.den := by exact_mod_cast h1
  have h3 : (q.den : ℤ) ∣ q.num * n := ⟨z, by rw [h2]; ring⟩
  have h4 : q.den ∣ q.num.natAbs * n := by
    have := Int.natAbs_dvd_natAbs.mpr h3
    simpa [Int.natAbs_mul] using this
  exact (Nat.Coprime.dvd_of_dvd_mul_left q.reduced.symm h4)

lemma tq_dyadic (D : ℕ) (t : ℝ) : IsDyadic (tq D t) ∧ Nat.log 2 (tq D t).den ≤ D := by
  have hI : Inteiro (2 ^ D) (tq D t) := ⟨jt D t, by unfold tq; push_cast; field_simp⟩
  obtain ⟨d, hd, hden⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (den_dvd_of_inteiro hI)
  refine ⟨⟨d, hden⟩, ?_⟩
  rw [hden, Nat.log_pow (by norm_num)]
  exact hd

end QuantIV55

end Pendencias.Marcada

/-!
# IV.5.5 — parte 3: a forma quantizada `R_t`, erro uniforme e inclinações não nulas
-/

namespace Pendencias.Marcada

open Artigo Set

namespace QuantIV55

open AlturaInversa

/-- Forma racional quantizada: `c' + (q' + t/Q) x + ∑ a'_j ρ(x - τ'_j)`, com `c', q', a'_j ∈ (1/Q)ℤ`
e `τ'_j = j/2^D ∈ (0,1)`; `t/Q` é a perturbação global de inclinação do TeX. -/
noncomputable def Rq {M : ℕ} (R : RealReLU M) (Q D t : ℕ) : RedReLU :=
  ⟨rq Q R.c, rq Q R.q + (t : ℚ) / Q,
    List.ofFn fun i => (rq Q (R.a i), tq D (R.τ i))⟩

lemma Rq_eval {M : ℕ} (R : RealReLU M) (Q D t : ℕ) (x : ℝ) :
    (Rq R Q D t).eval x = (rq Q R.c : ℝ) + ((rq Q R.q : ℝ) + (t : ℝ) / Q) * x +
      ∑ i, (rq Q (R.a i) : ℝ) * max 0 (x - (tq D (R.τ i) : ℝ)) := by
  simp only [RedReLU.eval, Rq, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  push_cast
  rfl

lemma Rq_data_length {M : ℕ} (R : RealReLU M) (Q D t : ℕ) : (Rq R Q D t).data.length = M := by
  simp [Rq]

/-- Erro uniforme em `[0,1]` da forma quantizada. -/
lemma Rq_err {M : ℕ} (R : RealReLU M) {Q D t : ℕ} (hQ : 0 < Q) (W : ℝ)
    (hτ : ∀ i, 0 < R.τ i ∧ R.τ i < 1) (haW : ∀ i, |R.a i| ≤ W) (hD : 1 ≤ D)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    |R.eval x - (Rq R Q D t).eval x| ≤
      1 / (2 * Q) + 1 / (2 * Q) + M * (1 / (2 * Q) + (W + 1) / 2 ^ D) + (t : ℝ) / Q := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hp : (0 : ℝ) < 2 ^ D := by positivity
  rw [Rq_eval]
  unfold RealReLU.eval
  set c' : ℝ := (rq Q R.c : ℝ)
  set q' : ℝ := (rq Q R.q : ℝ)
  have hterm : ∀ i : Fin M, |R.a i * max 0 (x - R.τ i) -
      (rq Q (R.a i) : ℝ) * max 0 (x - (tq D (R.τ i) : ℝ))| ≤ 1 / (2 * Q) + (W + 1) / 2 ^ D := by
    intro i
    obtain ⟨_, _, hj⟩ := jt_bounds hD (hτ i).1 (hτ i).2
    have hr0 : 0 ≤ max 0 (x - R.τ i) := le_max_left _ _
    have hr1 : max 0 (x - R.τ i) ≤ 1 := max_le (by norm_num) (by linarith [hx.2, (hτ i).1])
    have hlip : |max 0 (x - R.τ i) - max 0 (x - (tq D (R.τ i) : ℝ))| ≤ 1 / 2 ^ D := by
      rw [max_comm 0 (x - R.τ i), max_comm 0 (x - (tq D (R.τ i) : ℝ))]
      refine (abs_max_sub_max_le_abs _ _ _).trans ?_
      calc |x - R.τ i - (x - (tq D (R.τ i) : ℝ))| = |R.τ i - (tq D (R.τ i) : ℝ)| := by
            rw [← abs_neg]; ring_nf
        _ ≤ _ := hj
    have ha1 := rq_err hQ (R.a i)
    have ha2 := rq_abs_le hQ (R.a i) W (haW i)
    have hQh : 1 / (2 * (Q : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have e : R.a i * max 0 (x - R.τ i) - (rq Q (R.a i) : ℝ) * max 0 (x - (tq D (R.τ i) : ℝ)) =
        (R.a i - (rq Q (R.a i) : ℝ)) * max 0 (x - R.τ i) +
          (rq Q (R.a i) : ℝ) * (max 0 (x - R.τ i) - max 0 (x - (tq D (R.τ i) : ℝ))) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have t1 : |R.a i - (rq Q (R.a i) : ℝ)| * |max 0 (x - R.τ i)| ≤ 1 / (2 * Q) := by
      rw [abs_of_nonneg hr0]
      calc _ ≤ 1 / (2 * (Q : ℝ)) * 1 := mul_le_mul ha1 hr1 hr0 (by positivity)
        _ = _ := mul_one _
    have t2 : |(rq Q (R.a i) : ℝ)| * |max 0 (x - R.τ i) - max 0 (x - (tq D (R.τ i) : ℝ))| ≤
        (W + 1) / 2 ^ D := by
      calc _ ≤ (W + 1) * (1 / 2 ^ D) :=
            mul_le_mul (by linarith) hlip (abs_nonneg _) (by linarith [abs_nonneg (R.a i), haW i])
        _ = _ := by ring
    linarith
  have hsum : |∑ i : Fin M, (R.a i * max 0 (x - R.τ i) -
      (rq Q (R.a i) : ℝ) * max 0 (x - (tq D (R.τ i) : ℝ)))| ≤
      M * (1 / (2 * Q) + (W + 1) / 2 ^ D) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_rfl
  have hc := rq_err hQ R.c
  have hq := rq_err hQ R.q
  have hηx : |(t : ℝ) / Q * x| ≤ (t : ℝ) / Q := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t : ℝ) / Q), abs_of_nonneg hx.1]
    calc (t : ℝ) / Q * x ≤ (t : ℝ) / Q * 1 := by
          exact mul_le_mul_of_nonneg_left hx.2 (by positivity)
      _ = _ := mul_one _
  have hqx : |(R.q - q') * x| ≤ 1 / (2 * Q) := by
    rw [abs_mul, abs_of_nonneg hx.1]
    calc |R.q - q'| * x ≤ 1 / (2 * (Q : ℝ)) * 1 := mul_le_mul hq hx.2 hx.1 (by positivity)
      _ = _ := mul_one _
  have e : R.c + R.q * x + ∑ i, R.a i * max 0 (x - R.τ i) -
      (c' + (q' + (t : ℝ) / Q) * x + ∑ i, (rq Q (R.a i) : ℝ) * max 0 (x - (tq D (R.τ i) : ℝ))) =
      (R.c - c') + (R.q - q') * x - (t : ℝ) / Q * x +
        ∑ i : Fin M, (R.a i * max 0 (x - R.τ i) -
          (rq Q (R.a i) : ℝ) * max 0 (x - (tq D (R.τ i) : ℝ))) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [e]
  calc _ ≤ |(R.c - c') + (R.q - q') * x - (t : ℝ) / Q * x| + |∑ i : Fin M, _| := abs_add_le _ _
    _ ≤ (|(R.c - c') + (R.q - q') * x| + |(t : ℝ) / Q * x|) + _ := by
        gcongr; exact abs_sub _ _
    _ ≤ ((|R.c - c'| + |(R.q - q') * x|) + |(t : ℝ) / Q * x|) + _ := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

end QuantIV55

end Pendencias.Marcada

/-!
# IV.5.5 — parte 4: inclinações não nulas, hipóteses de altura e construção em `LTree`
-/

namespace Pendencias.Marcada

open Artigo Set

namespace QuantIV55

open AlturaInversa

lemma slopeAt_Rq {M : ℕ} (R : RealReLU M) (Q D t : ℕ) (ℓ : ℚ) :
    (Rq R Q D t).slopeAt ℓ = (Rq R Q D 0).slopeAt ℓ + (t : ℚ) / Q := by
  simp only [RedReLU.slopeAt, Rq]
  push_cast; ring

/-- as inclinações locais de uma forma assumem no máximo `1 + card (breaks)` valores distintos -/
lemma slopeAt_mem (P : RedReLU) (ℓ : ℚ) :
    P.slopeAt ℓ ∈ insert P.q (P.breaks.image P.slopeAt) := by
  classical
  have hbr : ∀ p ∈ P.data, p.2 ∈ P.breaks := fun p hp => by
    unfold RedReLU.breaks; rw [List.mem_toFinset]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
  by_cases hex : ∃ τ ∈ P.breaks, τ ≤ ℓ
  · apply Finset.mem_insert_of_mem
    let S := P.breaks.filter (· ≤ ℓ)
    have hS : S.Nonempty := by
      obtain ⟨τ, h1, h2⟩ := hex
      exact ⟨τ, Finset.mem_filter.mpr ⟨h1, h2⟩⟩
    have hmax := (Finset.mem_filter.mp (S.max'_mem hS)).2
    have hf : P.data.filter (fun p => decide (p.2 ≤ S.max' hS)) =
        P.data.filter (fun p => decide (p.2 ≤ ℓ)) := by
      apply List.filter_congr
      intro p hp
      simp only [decide_eq_decide]
      constructor
      · intro h; exact h.trans hmax
      · intro h; exact S.le_max' _ (Finset.mem_filter.mpr ⟨hbr p hp, h⟩)
    refine Finset.mem_image.mpr ⟨S.max' hS, (Finset.mem_filter.mp (S.max'_mem hS)).1, ?_⟩
    unfold RedReLU.slopeAt
    rw [hf]
  · have : P.slopeAt ℓ = P.q := by
      unfold RedReLU.slopeAt
      have : P.data.filter (fun p => decide (p.2 ≤ ℓ)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro p hp
        simpa using fun h => hex ⟨p.2, hbr p hp, h⟩
      rw [this]; simp
    rw [this]; exact Finset.mem_insert_self _ _

lemma exists_nonflat {M : ℕ} (R : RealReLU M) {Q : ℕ} (hQ : 0 < Q) (D : ℕ) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ M + 2 ∧ ∀ ℓ : ℚ, (Rq R Q D t).slopeAt ℓ ≠ 0 := by
  classical
  set P := Rq R Q D 0 with hP
  set S := insert P.q (P.breaks.image P.slopeAt) with hS
  have hcard : S.card ≤ M + 1 := by
    refine (Finset.card_insert_le _ _).trans ?_
    have h1 : (P.breaks.image P.slopeAt).card ≤ P.breaks.card := Finset.card_image_le
    have h2 : P.breaks.card ≤ M := by
      unfold RedReLU.breaks
      refine (List.toFinset_card_le _).trans ?_
      rw [List.length_map]
      exact (Rq_data_length R Q D 0).le
    omega
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  by_contra hcon
  push_neg at hcon
  -- para cada t ∈ [1, M+2], existe ℓ com inclinação nula, logo `-(t/Q) ∈ S`
  have hmem : ∀ t ∈ Finset.Icc 1 (M + 2), (-((t : ℚ) / Q)) ∈ S := by
    intro t ht
    obtain ⟨ℓ, hℓ⟩ := hcon t (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2
    rw [slopeAt_Rq] at hℓ
    have : P.slopeAt ℓ = -((t : ℚ) / Q) := by linarith
    rw [← this]
    exact slopeAt_mem P ℓ
  have hinj : Set.InjOn (fun t : ℕ => -((t : ℚ) / Q)) (Finset.Icc 1 (M + 2) : Set ℕ) := by
    intro a _ b _ hab
    simp only [neg_inj, div_left_inj' hQ'] at hab
    exact_mod_cast hab
  have := Finset.card_le_card_of_injOn (s := Finset.Icc 1 (M + 2)) (t := S)
    (fun t : ℕ => -((t : ℚ) / Q))
    (fun t ht => Finset.mem_coe.mpr (hmem t (Finset.mem_coe.mp ht))) hinj
  simp at this
  omega


lemma rat_abs_le_of_real {x : ℚ} {B : ℕ} (h : |(x : ℝ)| ≤ B) : |x| ≤ B := by
  exact_mod_cast h

lemma Rq_hip {M : ℕ} (R : RealReLU M) {Q D t B : ℕ} (hQ : 0 < Q) (W : ℝ) (hD : 1 ≤ D)
    (hB1 : 1 ≤ B) (hτ : ∀ i, 0 < R.τ i ∧ R.τ i < 1) (hcW : |R.c| ≤ W) (hqW : |R.q| ≤ W)
    (haW : ∀ i, |R.a i| ≤ W) (hWB : W + 1 ≤ B) (hQM : 4 * (M + 2) ≤ Q) (ht : t ≤ M + 2) :
    HipQ (Rq R Q D t) Q B D := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQM' : (4 * ((M : ℝ) + 2)) ≤ Q := by exact_mod_cast hQM
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have h8 : 1 / (2 * (Q : ℝ)) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have htQ : (t : ℝ) / Q ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hQ' (by norm_num)]
    have : (t : ℝ) ≤ M + 2 := by exact_mod_cast ht
    nlinarith
  have htQ0 : (0 : ℝ) ≤ (t : ℝ) / Q := by positivity
  have hmem : ∀ p ∈ (Rq R Q D t).data, ∃ i : Fin M,
      p = (rq Q (R.a i), tq D (R.τ i)) := by
    intro p hp
    simp only [Rq, List.mem_ofFn] at hp
    obtain ⟨i, rfl⟩ := hp
    exact ⟨i, rfl⟩
  refine ⟨hQ, hB1, rq_inteiro hQ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (rq_inteiro hQ _).add ⟨t, by push_cast; field_simp⟩
  · intro p hp
    obtain ⟨i, rfl⟩ := hmem p hp
    exact rq_inteiro hQ _
  · apply rat_abs_le_of_real
    have := rq_abs_le hQ R.c W hcW
    simp only [Rq]
    linarith
  · apply rat_abs_le_of_real
    have := rq_abs_le hQ R.q W hqW
    simp only [Rq]
    push_cast
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg htQ0]
    linarith
  · intro p hp
    obtain ⟨i, rfl⟩ := hmem p hp
    apply rat_abs_le_of_real
    have := rq_abs_le hQ (R.a i) W (haW i)
    linarith
  · intro p hp
    obtain ⟨i, rfl⟩ := hmem p hp
    exact ⟨(tq_dyadic D _).1, (tq_pos_lt_one hD (hτ i).1 (hτ i).2).1,
      (tq_pos_lt_one hD (hτ i).1 (hτ i).2).2⟩
  · unfold RedReLU.depth
    apply Finset.sup_le
    intro τ hτb
    unfold RedReLU.breaks at hτb
    rw [List.mem_toFinset, List.mem_map] at hτb
    obtain ⟨p, hp, rfl⟩ := hτb
    obtain ⟨i, rfl⟩ := hmem p hp
    exact (tq_dyadic D _).2

/-- Construção em `LTree`: o núcleo combinatório de IV.5.5, com os parâmetros numéricos
`Q`, `D`, `B` ainda abstratos. -/
theorem construct {M : ℕ} (R : RealReLU M) {Q D B : ℕ} (hQ : 0 < Q) (W ε : ℝ) (hD : 1 ≤ D)
    (hB1 : 1 ≤ B) (hτ : ∀ i, 0 < R.τ i ∧ R.τ i < 1) (hcW : |R.c| ≤ W) (hqW : |R.q| ≤ W)
    (haW : ∀ i, |R.a i| ≤ W) (hWB : W + 1 ≤ B) (hQM : 4 * (M + 2) ≤ Q)
    (herr : 1 / (2 * (Q : ℝ)) + 1 / (2 * Q) + M * (1 / (2 * Q) + (W + 1) / 2 ^ D) +
      ((M : ℝ) + 2) / Q ≤ ε) :
    ∃ U : LTree, LTree.WF 0 0 U ∧ (∀ x ∈ Icc (0 : ℝ) 1, |R.eval x - U.eval 0 0 x| ≤ ε) ∧
      U.numLeaves ≤ 1 + M * D ∧ U.maxHeight ≤ Q * 2 ^ (D + 1) * ((M + 2) * B) := by
  classical
  obtain ⟨t, ht1, ht2, hflat⟩ := exists_nonflat R hQ D
  set P := Rq R Q D t with hP
  have hip : HipQ P Q B D := Rq_hip R hQ W hD hB1 hτ hcW hqW haW hWB hQM ht2
  have hbr : ∀ τ ∈ P.breaks, ∃ p ∈ P.data, p.2 = τ := fun τ hτb => by
    unfold RedReLU.breaks at hτb
    rw [List.mem_toFinset, List.mem_map] at hτb
    exact hτb
  have hdy : ∀ τ ∈ P.breaks, IsDyadic τ := fun τ hτb => by
    obtain ⟨p, hp, rfl⟩ := hbr τ hτb; exact (hip.hτ p hp).1
  have hi : ∀ τ ∈ P.breaks, (0 : ℝ) < τ ∧ (τ : ℝ) < 1 := fun τ hτb => by
    obtain ⟨p, hp, rfl⟩ := hbr τ hτb
    obtain ⟨_, h0, h1⟩ := hip.hτ p hp
    exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩
  obtain ⟨hw, he, _, hhi⟩ := P.canonTree_representation_bounds hdy hi
  have hlen : P.data.length = M := Rq_data_length R Q D t
  have hcard : P.breaks.card ≤ M := by
    unfold RedReLU.breaks
    refine (List.toFinset_card_le _).trans ?_
    rw [List.length_map]; exact hlen.le
  have hsumD : (∑ τ ∈ P.breaks, Nat.log 2 τ.den) ≤ M * D := by
    calc (∑ τ ∈ P.breaks, Nat.log 2 τ.den) ≤ ∑ _τ ∈ P.breaks, D := by
          apply Finset.sum_le_sum
          intro τ hτb
          obtain ⟨p, hp, rfl⟩ := hbr τ hτb
          exact hip.log_le p hp
      _ = P.breaks.card * D := by simp
      _ ≤ M * D := Nat.mul_le_mul_right _ hcard
  set T := P.canonTree (canonShape P.breaks P.depth 0 0) 0 0 with hT
  have hslopes : ∀ k m, (P.atomAt k m).s ≠ 0 := fun k m => hflat _
  have hleaves : ∀ (Dd : DShape) (k : ℕ) (m : ℤ), ∀ a ∈ (P.canonTree Dd k m).leaves, a.s ≠ 0 := by
    intro Dd
    induction Dd with
    | leaf => intro k m a ha; simp only [RedReLU.canonTree, MTree.leaves,
        List.mem_singleton] at ha; subst a; exact hslopes k m
    | node l r ihl ihr =>
        intro k m a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact ihl _ _ a ha
        · exact ihr _ _ a ha
  obtain ⟨U, hU⟩ := MTree.exists_original T (hleaves _ 0 0)
  have hUe : ∀ x, U.eval 0 0 x = MTree.eval 0 0 T x := fun x => by
    rw [← hU, toM_eval]
  have hUl : U.numLeaves = T.numLeaves := by
    rw [← hU]; simp [LTree.numLeaves, MTree.numLeaves, toM_leaves]
  refine ⟨U, (toM_WF_iff U 0 0).mp (hU ▸ hw), ?_, ?_, ?_⟩
  · intro x hx
    rw [hUe, he hx]
    have := Rq_err R (t := t) hQ W hτ haW hD x hx
    refine this.trans ?_
    have htQ : (t : ℝ) / Q ≤ ((M : ℝ) + 2) / Q := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast ht2
    linarith
  · rw [hUl]; omega
  · have hHc : T.maxHeight ≤ Q * 2 ^ (D + 1) * ((M + 2) * B) := by
      have := Hcan_leQ P hip
      rw [hlen] at this
      rw [hT, ← RedReLU.Hcan_eq_maxHeight]  -- placeholder
      exact this
    refine LTree.maxHeight_le_iff.mpr fun a ha => ?_
    have hmem : a.toM ∈ U.toM.leaves := by rw [toM_leaves]; exact List.mem_map_of_mem ha
    rw [hU] at hmem
    have := MTree.maxHeight_le_iff.mp hHc a.toM hmem
    rwa [Atom.toM_height] at this

end QuantIV55

end Pendencias.Marcada

/-!
# IV.5.5 — parte 5: parâmetros numéricos e enunciado final
-/

namespace Pendencias.Marcada

open Artigo Set

namespace QuantIV55

lemma height_arith (X Y e Qr P2 Br : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (he0 : 0 < e)
    (hP0 : 0 ≤ P2) (hB0 : 0 ≤ Br)
    (hQ : Qr ≤ 5 * (X + 1) / e) (hP : P2 ≤ 4 * X * Y / e) (hB : Br ≤ 2 * Y) :
    Qr * (2 * P2) * ((X + 1) * Br) ≤ 320 * X ^ 3 * Y ^ 3 / e ^ 2 := by
  have hX0 : 0 < X := by linarith
  calc Qr * (2 * P2) * ((X + 1) * Br)
      ≤ (5 * (X + 1) / e) * (2 * (4 * X * Y / e)) * ((X + 1) * (2 * Y)) := by gcongr
    _ = 80 * (X + 1) ^ 2 * X * Y ^ 2 / e ^ 2 := by field_simp; ring
    _ ≤ 320 * X ^ 3 * Y ^ 3 / e ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have h1 : (X + 1) ^ 2 ≤ 4 * X ^ 2 := by nlinarith
        have h2 : Y ^ 2 ≤ Y ^ 3 := by nlinarith [sq_nonneg Y]
        calc 80 * (X + 1) ^ 2 * X * Y ^ 2 ≤ 80 * (4 * X ^ 2) * X * Y ^ 3 := by gcongr
          _ = 320 * X ^ 3 * Y ^ 3 := by ring

/-- **IV.5.5 (reversão aproximada quantizada)**. Existe uma constante universal `C` (aqui `320`)
tal que, para toda forma ReLU reduzida `R` de parâmetros reais com `|c|,|q|,|a_j| ≤ W`, `W ≥ 1`, e
todo `0 < ε ≤ 1`, há uma montagem `U` da biblioteca original (`LTree.WF 0 0 U`, átomos de
inclinação não nula) com erro uniforme `≤ ε` em `[0,1]`, `|Λ(U)| ≤ 1 + M D_ε` e altura atômica
máxima `≤ C (M+1)³ (W+1)³ ε⁻²`. A hipótese de forma reduzida é a do TeX; nenhuma hipótese sobre
`σ_i ≠ 0` é feita (regiões planas permitidas). -/
theorem quantized_approximate_reverse :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) (R : RealReLU M), R.Reduced → ∀ (W ε : ℝ), 1 ≤ W →
      |R.c| ≤ W → |R.q| ≤ W → (∀ i, |R.a i| ≤ W) → 0 < ε → ε ≤ 1 →
      ∃ U : LTree, LTree.WF 0 0 U ∧ (∀ x ∈ Icc (0 : ℝ) 1, |R.eval x - U.eval 0 0 x| ≤ ε) ∧
        (U.numLeaves : ℝ) ≤
          1 + M * (⌈Real.logb 2 (C * (M + 1) * (W + 1) / ε)⌉₊ : ℝ) ∧
        (U.maxHeight : ℝ) ≤ C * (M + 1) ^ 3 * (W + 1) ^ 3 / ε ^ 2 := by
  refine ⟨320, by norm_num, ?_⟩
  intro M R hR W ε hW hcW hqW haW hε0 hε1
  have hτ : ∀ i, 0 < R.τ i ∧ R.τ i < 1 := hR.2.1
  have hM0 : (0 : ℝ) ≤ M := by positivity
  set X : ℝ := (M : ℝ) + 1 with hXdef
  set Y : ℝ := W + 1 with hYdef
  have hX : 1 ≤ X := by linarith
  have hY : 2 ≤ Y := by linarith
  -- parâmetros
  set Q : ℕ := ⌈4 * ((M : ℝ) + 2) / ε⌉₊ with hQdef
  set y : ℝ := 2 * X * Y / ε with hy
  have hy4 : 4 ≤ y := by
    rw [hy, le_div_iff₀ hε0]; nlinarith
  have hy0 : 0 < y := by linarith
  set D : ℕ := ⌈Real.logb 2 y⌉₊ with hDdef
  set B : ℕ := ⌈W⌉₊ + 1 with hBdef
  -- Q
  have hQge : 4 * ((M : ℝ) + 2) / ε ≤ Q := Nat.le_ceil _
  have hQlt : (Q : ℝ) < 4 * ((M : ℝ) + 2) / ε + 1 := Nat.ceil_lt_add_one (by positivity)
  have hQM : 4 * (M + 2) ≤ Q := by
    have : (4 * ((M : ℝ) + 2)) ≤ Q := by
      refine le_trans ?_ hQge
      rw [le_div_iff₀ hε0]; nlinarith
    exact_mod_cast this
  have hQpos : 0 < Q := by omega
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQpos
  -- D
  have hlog4 : 2 ≤ Real.logb 2 y := by
    have : Real.logb 2 4 ≤ Real.logb 2 y :=
      Real.logb_le_logb_of_le (by norm_num) (by norm_num) hy4
    have h4 : Real.logb 2 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow]
      simp [Real.logb_self_eq_one]
    linarith
  have hD1 : 1 ≤ D := by
    rw [hDdef]; exact Nat.one_le_iff_ne_zero.mpr (by
      intro h; rw [Nat.ceil_eq_zero] at h; linarith)
  have hDge : y ≤ 2 ^ D := by
    have h1 : Real.logb 2 y ≤ D := Nat.le_ceil _
    calc y = (2 : ℝ) ^ (Real.logb 2 y) := (Real.rpow_logb (by norm_num) (by norm_num) hy0).symm
      _ ≤ (2 : ℝ) ^ (D : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = 2 ^ D := Real.rpow_natCast _ _
  have hDlt : (2 : ℝ) ^ D ≤ 2 * y := by
    have h1 : (D : ℝ) < Real.logb 2 y + 1 := Nat.ceil_lt_add_one (by linarith)
    calc (2 : ℝ) ^ D = (2 : ℝ) ^ (D : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ (Real.logb 2 y + 1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1.le
      _ = 2 * y := by
        rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hy0]
        simp [mul_comm]
  -- B
  have hB1 : 1 ≤ B := by omega
  have hWB : W + 1 ≤ B := by
    have := Nat.le_ceil W
    rw [hBdef]; push_cast; linarith
  have hBle : (B : ℝ) ≤ 2 * Y := by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ W)
    rw [hBdef]; push_cast; linarith
  -- erro
  have hp2 : (0 : ℝ) < 2 ^ D := by positivity
  have herr : 1 / (2 * (Q : ℝ)) + 1 / (2 * Q) + M * (1 / (2 * Q) + (W + 1) / 2 ^ D) +
      ((M : ℝ) + 2) / Q ≤ ε := by
    have h1 : ((M : ℝ) + 2) / Q ≤ ε / 4 := by
      rw [div_le_iff₀ hQ']
      have := hQge
      rw [div_le_iff₀ hε0] at this
      nlinarith
    have h3 : (W + 1) / 2 ^ D ≤ ε / (2 * (M + 1)) := by
      rw [div_le_div_iff₀ hp2 (by positivity)]
      have := hDge
      rw [hy, div_le_iff₀ hε0] at this
      nlinarith
    have h4 : (M : ℝ) * (ε / (2 * (M + 1))) ≤ ε / 2 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h6 : (M : ℝ) * ((W + 1) / 2 ^ D) ≤ ε / 2 :=
      (mul_le_mul_of_nonneg_left h3 hM0).trans h4
    have e : 1 / (2 * (Q : ℝ)) + 1 / (2 * Q) + M * (1 / (2 * Q) + (W + 1) / 2 ^ D) +
        ((M : ℝ) + 2) / Q = 3 / 2 * (((M : ℝ) + 2) / Q) + M * ((W + 1) / 2 ^ D) := by
      field_simp; ring
    rw [e]; linarith
  obtain ⟨U, hw, he, hn, hh⟩ := construct R (D := D) (B := B) hQpos W ε hD1 hB1 hτ hcW hqW haW hWB
    hQM herr
  refine ⟨U, hw, he, ?_, ?_⟩
  · have hDD : D ≤ ⌈Real.logb 2 (320 * X * Y / ε)⌉₊ := by
      apply Nat.ceil_mono
      apply Real.logb_le_logb_of_le (by norm_num) hy0
      rw [hy]
      apply div_le_div_of_nonneg_right _ hε0.le
      nlinarith
    have h1 : (U.numLeaves : ℝ) ≤ ((1 + M * D : ℕ) : ℝ) := by exact_mod_cast hn
    refine h1.trans ?_
    push_cast
    have : (D : ℝ) ≤ (⌈Real.logb 2 (320 * X * Y / ε)⌉₊ : ℝ) := by exact_mod_cast hDD
    nlinarith
  · have h1 : (U.maxHeight : ℝ) ≤ ((Q * 2 ^ (D + 1) * ((M + 2) * B) : ℕ) : ℝ) := by
      exact_mod_cast hh
    refine h1.trans ?_
    push_cast
    have hQle : (Q : ℝ) ≤ 5 * (X + 1) / ε := by
      have : 1 ≤ (X + 1) / ε := by
        rw [le_div_iff₀ hε0]; linarith
      have e2 : 5 * (X + 1) / ε = 4 * ((M : ℝ) + 2) / ε + (X + 1) / ε := by
        rw [hXdef]; field_simp; ring
      rw [e2]
      linarith
    have hPle : (2 : ℝ) ^ D ≤ 4 * X * Y / ε := by
      have : 2 * y = 4 * X * Y / ε := by rw [hy]; field_simp; ring
      linarith
    have key := height_arith X Y ε (Q : ℝ) ((2 : ℝ) ^ D) (B : ℝ) hX (by linarith) hε0
      hp2.le (by positivity) hQle hPle hBle
    have e3 : (Q : ℝ) * 2 ^ (D + 1) * (((M : ℝ) + 2) * B) =
        (Q : ℝ) * (2 * (2 : ℝ) ^ D) * ((X + 1) * B) := by
      rw [hXdef]; ring
    rw [e3]
    exact key

end QuantIV55

end Pendencias.Marcada

