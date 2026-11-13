import Pendencias.Marcada
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# IV.5.4 (parte inversa) — cota corrigida para a altura canônica

A cota impressa
`log₂ H_can(R) ≤ C [M log(2W) + D + log(M+1)]`
é falsa: para `R(x) = x` (`M = 0`, `D = 0`, `W = 1`) tem-se `H_can = 2`, enquanto o lado
direito é `0`. Pior: nenhuma constante aditiva a conserta, pois `R(x) = W·x` tem `M = 0`,
`D = 0` e `H_can ≥ W` (a altura da inclinação), logo `log₂ H_can` não é limitado em termos de
`M`, `D` somente.

A forma correta, demonstrada aqui, troca `M` por `M + 1` no primeiro termo (há `M + 1`
inclinações locais, cada uma soma de até `M + 1` racionais de altura `≤ W`):

`log₂ H_can(R) ≤ 5 [(M+1) log₂(2W) + D + log₂(M+1)]`.

O resultado básico (em ℕ) é
`H_can(R) ≤ 2^(D+1) · (M+2) · W^(M+3)`.

Hipóteses (as do TeX): `ht c, ht q, ht a_j ≤ W`; quebras `τ_j` diádicas em `(0,1)`;
profundidade diádica máxima das quebras `≤ D`. Não se exige ordem estrita nem `a_j ≠ 0`
(a cota vale também sem a redução).
-/

namespace Pendencias.Marcada

open Artigo

namespace AlturaInversa

/-! ## Racionais com denominador comum -/

/-- `Inteiro n q`: `n · q` é um inteiro (i.e. `q.den ∣ n`). -/
def Inteiro (n : ℕ) (q : ℚ) : Prop := ∃ z : ℤ, q * n = z

lemma Inteiro.mono {n N : ℕ} {q : ℚ} (h : Inteiro n q) (hd : n ∣ N) : Inteiro N q := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨c, rfl⟩ := hd
  exact ⟨z * c, by push_cast; rw [← hz]; ring⟩

lemma Inteiro.add {N : ℕ} {q r : ℚ} (hq : Inteiro N q) (hr : Inteiro N r) :
    Inteiro N (q + r) := by
  obtain ⟨z, hz⟩ := hq
  obtain ⟨w, hw⟩ := hr
  exact ⟨z + w, by push_cast; rw [← hz, ← hw]; ring⟩

lemma Inteiro.sub {N : ℕ} {q r : ℚ} (hq : Inteiro N q) (hr : Inteiro N r) :
    Inteiro N (q - r) := by
  obtain ⟨z, hz⟩ := hq
  obtain ⟨w, hw⟩ := hr
  exact ⟨z - w, by push_cast; rw [← hz, ← hw]; ring⟩

lemma Inteiro.mul {n n' : ℕ} {q r : ℚ} (hq : Inteiro n q) (hr : Inteiro n' r) :
    Inteiro (n * n') (q * r) := by
  obtain ⟨z, hz⟩ := hq
  obtain ⟨w, hw⟩ := hr
  exact ⟨z * w, by push_cast; rw [← hz, ← hw]; ring⟩

lemma inteiro_den (q : ℚ) : Inteiro q.den q := ⟨q.num, Rat.mul_den_eq_num q⟩

lemma inteiro_zero (N : ℕ) : Inteiro N 0 := ⟨0, by simp⟩

lemma inteiro_ite (P : Prop) [Decidable P] : Inteiro 1 (if P then (1 : ℚ) else 0) := by
  by_cases h : P
  · exact ⟨1, by simp [h]⟩
  · exact ⟨0, by simp [h]⟩

lemma Inteiro.den_le {n : ℕ} {q : ℚ} (h : Inteiro n q) (hn : 0 < n) : q.den ≤ n := by
  obtain ⟨z, hz⟩ := h
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hq : q = (z : ℚ) / n := eq_div_of_mul_eq hn' hz
  have := den_div_le z n hn
  rwa [← hq] at this

/-- `|r| ≤ ht r`. -/
lemma abs_le_ht (r : ℚ) : |r| ≤ (ht r : ℚ) := by
  have h1 : (r.num : ℚ) = r * r.den := (Rat.mul_den_eq_num r).symm
  have hd : (1 : ℚ) ≤ r.den := by exact_mod_cast r.den_pos
  have h2 : |r| ≤ |(r.num : ℚ)| := by
    rw [h1, abs_mul, abs_of_pos (by linarith : (0 : ℚ) < r.den)]
    nlinarith [abs_nonneg r]
  have h3 : |(r.num : ℚ)| = (r.num.natAbs : ℚ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
  calc |r| ≤ |(r.num : ℚ)| := h2
    _ = (r.num.natAbs : ℚ) := h3
    _ ≤ (ht r : ℚ) := by unfold ht; exact_mod_cast le_max_left _ _

lemma den_le_ht (r : ℚ) : r.den ≤ ht r := le_max_right _ _

/-- altura de um racional com denominador comum `n` e módulo `≤ B`. -/
lemma ht_le_of_inteiro {n : ℕ} {q : ℚ} {B : ℕ} (hn : 0 < n) (h : Inteiro n q)
    (hB : |q| ≤ B) : ht q ≤ n * max B 1 := by
  have hden : q.den ≤ n := h.den_le hn
  have h3 : (q.num.natAbs : ℚ) = |q| * q.den := by
    have h1 : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
    have : |(q.num : ℚ)| = (q.num.natAbs : ℚ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
    rw [← this, h1, abs_mul, abs_of_pos (by exact_mod_cast q.den_pos : (0 : ℚ) < q.den)]
  have hnum : q.num.natAbs ≤ B * n := by
    have : (q.num.natAbs : ℚ) ≤ ((B * n : ℕ) : ℚ) := by
      rw [h3]; push_cast
      exact mul_le_mul hB (by exact_mod_cast hden) (by positivity) (by positivity)
    exact_mod_cast this
  unfold ht
  apply max_le
  · calc q.num.natAbs ≤ B * n := hnum
      _ ≤ n * max B 1 := by
        rw [mul_comm]; exact Nat.mul_le_mul_left _ (le_max_left _ _)
  · calc q.den ≤ n := hden
      _ ≤ n * max B 1 := Nat.le_mul_of_pos_right _ (lt_of_lt_of_le one_pos (le_max_right _ _))

/-- soma sobre uma lista com denominador comum `E · ∏ den(a_j)` -/
lemma inteiro_sum (E : ℕ) (g : ℚ × ℚ → ℚ) :
    ∀ l : List (ℚ × ℚ), (∀ p ∈ l, Inteiro E (g p)) →
      Inteiro (E * (l.map fun p => p.1.den).prod) ((l.map fun p => p.1 * g p).sum)
  | [], _ => ⟨0, by simp⟩
  | p :: l, h => by
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      have h1 : Inteiro (p.1.den * E) (p.1 * g p) := (inteiro_den p.1).mul (h p (by simp))
      have h2 := inteiro_sum E g l (fun p' hp' => h p' (List.mem_cons_of_mem _ hp'))
      exact (h1.mono ⟨(l.map fun p => p.1.den).prod, by ring⟩).add (h2.mono ⟨p.1.den, by ring⟩)

lemma abs_sum_le (W : ℚ) (g : ℚ × ℚ → ℚ) :
    ∀ l : List (ℚ × ℚ), (∀ p ∈ l, |p.1| ≤ W) → (∀ p ∈ l, |g p| ≤ 1) → 0 ≤ W →
      |(l.map fun p => p.1 * g p).sum| ≤ l.length * W
  | [], _, _, _ => by simp
  | p :: l, h1, h2, hW => by
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have ih := abs_sum_le W g l (fun p' hp' => h1 p' (List.mem_cons_of_mem _ hp'))
        (fun p' hp' => h2 p' (List.mem_cons_of_mem _ hp')) hW
      have hp : |p.1 * g p| ≤ W := by
        rw [abs_mul]
        calc |p.1| * |g p| ≤ W * 1 :=
              mul_le_mul (h1 p (by simp)) (h2 p (by simp)) (abs_nonneg _) hW
          _ = W := mul_one W
      refine (abs_add_le _ _).trans ?_
      push_cast
      linarith

lemma prod_den_le (l : List (ℚ × ℚ)) (W : ℕ) (ha : ∀ p ∈ l, ht p.1 ≤ W) :
    (l.map fun p => p.1.den).prod ≤ W ^ l.length ∧ 0 < (l.map fun p => p.1.den).prod := by
  constructor
  · have := List.prod_le_pow_card (l.map fun p => p.1.den) W (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact (den_le_ht _).trans (ha p hp))
    simpa using this
  · apply List.prod_pos
    intro x hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    exact p.1.den_pos

/-! ## Hipóteses de IV.5.4 (volta) -/

/-- coeficientes de altura `≤ W`, quebras diádicas em `(0,1)`, profundidade `≤ D` -/
structure Hip (R : RedReLU) (W D : ℕ) : Prop where
  hc : ht R.c ≤ W
  hq : ht R.q ≤ W
  ha : ∀ p ∈ R.data, ht p.1 ≤ W
  hτ : ∀ p ∈ R.data, IsDyadic p.2 ∧ 0 < p.2 ∧ p.2 < 1
  hD : R.depth ≤ D

lemma Hip.one_le {R : RedReLU} {W D : ℕ} (h : Hip R W D) : 1 ≤ W :=
  le_trans (one_le_ht _) h.hc

lemma Hip.log_le {R : RedReLU} {W D : ℕ} (h : Hip R W D) (p : ℚ × ℚ) (hp : p ∈ R.data) :
    Nat.log 2 p.2.den ≤ D := by
  have hmem : p.2 ∈ R.breaks := by
    unfold RedReLU.breaks
    rw [List.mem_toFinset]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  exact le_trans (Finset.le_sup (f := fun τ : ℚ => Nat.log 2 τ.den) hmem) h.hD

lemma inteiro_dyadic (τ : ℚ) (D : ℕ) (hτ : IsDyadic τ) (hD : Nat.log 2 τ.den ≤ D) :
    Inteiro (2 ^ (D + 1)) τ := by
  obtain ⟨d, hd⟩ := hτ
  have hD' := hD
  rw [hd, Nat.log_pow (by norm_num)] at hD'
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (show d ≤ D + 1 by omega)
  refine ⟨τ.num * 2 ^ j, ?_⟩
  have h := Rat.mul_den_eq_num τ
  rw [hd] at h
  push_cast at h
  rw [hj]
  push_cast
  calc τ * 2 ^ (d + j) = (τ * 2 ^ d) * 2 ^ j := by ring
    _ = τ.num * 2 ^ j := by rw [h]

lemma inteiro_center (k D : ℕ) (hk : k ≤ D) (m : ℤ) :
    Inteiro (2 ^ (D + 1)) (((m : ℚ) + 1 / 2) / 2 ^ k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨(2 * m + 1) * 2 ^ j, ?_⟩
  push_cast
  field_simp
  ring

/-! ## Altura da inclinação local e do valor central -/

lemma slopeAt_eq (R : RedReLU) (x : ℚ) :
    R.slopeAt x = R.q + (R.data.map fun p => p.1 * (if p.2 ≤ x then (1 : ℚ) else 0)).sum := by
  unfold RedReLU.slopeAt
  congr 1
  generalize R.data = l
  induction l with
  | nil => simp
  | cons p l ih => by_cases h : p.2 ≤ x <;> simp [h, ih]

lemma ht_slope_le (R : RedReLU) (W D : ℕ) (h : Hip R W D) (x : ℚ) :
    ht (R.slopeAt x) ≤ (R.data.length + 1) * W ^ (R.data.length + 2) := by
  have hW := h.one_le
  rw [slopeAt_eq]
  obtain ⟨hPle, hPpos⟩ := prod_den_le R.data W h.ha
  have hS := inteiro_sum 1 (fun p => if p.2 ≤ x then (1 : ℚ) else 0) R.data
    (fun _ _ => inteiro_ite _)
  have hI : Inteiro (R.q.den * (1 * (R.data.map fun p => p.1.den).prod))
      (R.q + (R.data.map fun p => p.1 * (if p.2 ≤ x then (1 : ℚ) else 0)).sum) :=
    ((inteiro_den R.q).mono ⟨_, rfl⟩).add (hS.mono ⟨R.q.den, mul_comm _ _⟩)
  have hq' : |R.q| ≤ W := (abs_le_ht _).trans (by exact_mod_cast h.hq)
  have hsum := abs_sum_le (W : ℚ) (fun p => if p.2 ≤ x then (1 : ℚ) else 0) R.data
    (fun p hp => (abs_le_ht p.1).trans (by exact_mod_cast h.ha p hp))
    (fun p _ => by by_cases hp : p.2 ≤ x <;> simp [hp]) (by positivity)
  have hB : |R.q + (R.data.map fun p => p.1 * (if p.2 ≤ x then (1 : ℚ) else 0)).sum|
      ≤ (((R.data.length + 1) * W : ℕ) : ℚ) := by
    refine (abs_add_le _ _).trans ?_
    push_cast
    nlinarith
  have hN : 0 < R.q.den * (1 * (R.data.map fun p => p.1.den).prod) :=
    Nat.mul_pos R.q.den_pos (by omega)
  have key := ht_le_of_inteiro hN hI hB
  have hmax : max ((R.data.length + 1) * W) 1 = (R.data.length + 1) * W :=
    max_eq_left (Nat.one_le_iff_ne_zero.mpr (by positivity))
  rw [hmax] at key
  have hqd : R.q.den ≤ W := (den_le_ht _).trans h.hq
  calc ht (R.q + _) ≤ _ := key
    _ ≤ (W * (1 * W ^ R.data.length)) * ((R.data.length + 1) * W) :=
        Nat.mul_le_mul (Nat.mul_le_mul hqd (by simpa using hPle)) le_rfl
    _ = (R.data.length + 1) * W ^ (R.data.length + 2) := by ring

lemma ht_evalQ_le (R : RedReLU) (W D : ℕ) (h : Hip R W D) (x : ℚ)
    (hxI : Inteiro (2 ^ (D + 1)) x) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ht (R.evalQ x) ≤ 2 ^ (D + 1) * ((R.data.length + 2) * W) * W ^ (R.data.length + 2) := by
  have hW := h.one_le
  obtain ⟨hPle, hPpos⟩ := prod_den_le R.data W h.ha
  have hg : ∀ p ∈ R.data, Inteiro (2 ^ (D + 1)) (max 0 (x - p.2)) := by
    intro p hp
    obtain ⟨hdy, _, _⟩ := h.hτ p hp
    have hs : Inteiro (2 ^ (D + 1)) (x - p.2) := hxI.sub (inteiro_dyadic _ D hdy (h.log_le p hp))
    rcases max_choice (0 : ℚ) (x - p.2) with e | e
    · rw [e]; exact inteiro_zero _
    · rw [e]; exact hs
  have hS := inteiro_sum (2 ^ (D + 1)) (fun p => max 0 (x - p.2)) R.data hg
  have hqx : Inteiro (R.q.den * 2 ^ (D + 1)) (R.q * x) := (inteiro_den R.q).mul hxI
  set P := (R.data.map fun p => p.1.den).prod with hP
  have hI : Inteiro (R.c.den * (R.q.den * (2 ^ (D + 1) * P))) (R.evalQ x) := by
    unfold RedReLU.evalQ
    exact (((inteiro_den R.c).mono ⟨_, rfl⟩).add
      (hqx.mono ⟨R.c.den * P, by ring⟩)).add (hS.mono ⟨R.c.den * R.q.den, by ring⟩)
  have hc' : |R.c| ≤ W := (abs_le_ht _).trans (by exact_mod_cast h.hc)
  have hq' : |R.q| ≤ W := (abs_le_ht _).trans (by exact_mod_cast h.hq)
  have hsum := abs_sum_le (W : ℚ) (fun p => max 0 (x - p.2)) R.data
    (fun p hp => (abs_le_ht p.1).trans (by exact_mod_cast h.ha p hp))
    (fun p hp => by
      obtain ⟨_, hτ0, _⟩ := h.hτ p hp
      exact abs_le.mpr ⟨le_trans (by norm_num) (le_max_left _ _),
        max_le (by norm_num) (by linarith)⟩)
    (by positivity)
  have hqx' : |R.q * x| ≤ W := by
    rw [abs_mul, abs_of_nonneg hx0]
    calc |R.q| * x ≤ W * 1 := mul_le_mul hq' hx1 hx0 (by positivity)
      _ = W := mul_one _
  have hB : |R.evalQ x| ≤ (((R.data.length + 2) * W : ℕ) : ℚ) := by
    unfold RedReLU.evalQ
    refine (abs_add_le _ _).trans ?_
    have h1 := abs_add_le R.c (R.q * x)
    push_cast
    linarith
  have hN : 0 < R.c.den * (R.q.den * (2 ^ (D + 1) * P)) :=
    Nat.mul_pos R.c.den_pos (Nat.mul_pos R.q.den_pos (Nat.mul_pos (by positivity) hPpos))
  have key := ht_le_of_inteiro hN hI hB
  have hmax : max ((R.data.length + 2) * W) 1 = (R.data.length + 2) * W :=
    max_eq_left (Nat.one_le_iff_ne_zero.mpr (by positivity))
  rw [hmax] at key
  have hcd : R.c.den ≤ W := (den_le_ht _).trans h.hc
  have hqd : R.q.den ≤ W := (den_le_ht _).trans h.hq
  calc ht (R.evalQ x) ≤ _ := key
    _ ≤ (W * (W * (2 ^ (D + 1) * W ^ R.data.length))) * ((R.data.length + 2) * W) :=
        Nat.mul_le_mul (Nat.mul_le_mul hcd (Nat.mul_le_mul hqd
          (Nat.mul_le_mul le_rfl hPle))) le_rfl
    _ = 2 ^ (D + 1) * ((R.data.length + 2) * W) * W ^ (R.data.length + 2) := by ring

/-! ## A cota em ℕ -/

lemma hShape_leaf_le (R : RedReLU) (W D : ℕ) (h : Hip R W D) (k : ℕ) (m : ℤ) (hk : k ≤ D)
    (hm0 : 0 ≤ m) (hm : m < 2 ^ k) :
    R.hShape .leaf k m ≤ 2 ^ (D + 1) * (R.data.length + 2) * W ^ (R.data.length + 3) := by
  have hW := h.one_le
  set M := R.data.length with hM
  have hE : D + 1 < 2 ^ (D + 1) := Nat.lt_two_pow_self
  have hP : 1 ≤ W ^ (M + 3) := Nat.one_le_pow _ _ hW
  have hBd : 2 ^ (D + 1) ≤ 2 ^ (D + 1) * (M + 2) * W ^ (M + 3) :=
    calc 2 ^ (D + 1) = 2 ^ (D + 1) * 1 * 1 := by ring
      _ ≤ 2 ^ (D + 1) * (M + 2) * W ^ (M + 3) :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by omega)) hP
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
  have hval := ht_evalQ_le R W D h _ hxI hx0 hx1
  have hslope := ht_slope_le R W D h ((m : ℚ) / 2 ^ k)
  have hval' : ht (R.evalQ (((m : ℚ) + 1 / 2) / 2 ^ k)) ≤
      2 ^ (D + 1) * (M + 2) * W ^ (M + 3) :=
    hval.trans (le_of_eq (by ring))
  have hslope' : ht (R.slopeAt ((m : ℚ) / 2 ^ k)) ≤
      2 ^ (D + 1) * (M + 2) * W ^ (M + 3) := by
    refine hslope.trans ?_
    calc (M + 1) * W ^ (M + 2) ≤ 1 * (M + 2) * W ^ (M + 3) := by
          apply Nat.mul_le_mul (by omega)
          exact Nat.pow_le_pow_right hW (by omega)
      _ ≤ 2 ^ (D + 1) * (M + 2) * W ^ (M + 3) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) le_rfl) le_rfl
  simp only [RedReLU.hShape]
  refine max_le (max_le (max_le (max_le ?_ ?_) ?_) hval') hslope'
  · omega
  · omega
  · omega

lemma hShape_canon_le (R : RedReLU) (W D : ℕ) (h : Hip R W D) :
    ∀ (d k : ℕ) (m : ℤ), 0 ≤ m → m < 2 ^ k → k + d ≤ D →
      R.hShape (canonShape R.breaks d k m) k m ≤
        2 ^ (D + 1) * (R.data.length + 2) * W ^ (R.data.length + 3) := by
  intro d
  induction d with
  | zero =>
      intro k m hm0 hm hkd
      simp only [canonShape]
      exact hShape_leaf_le R W D h k m (by omega) hm0 hm
  | succ d ih =>
      intro k m hm0 hm hkd
      unfold canonShape
      split_ifs with hex
      · simp only [RedReLU.hShape]
        have hm' : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
        refine max_le (ih (k + 1) (2 * m) (by omega) (by omega) (by omega))
          (ih (k + 1) (2 * m + 1) (by omega) (by omega) (by omega))
      · exact hShape_leaf_le R W D h k m (by omega) hm0 hm

lemma two_le_hShape (R : RedReLU) :
    ∀ (T : DShape) (k : ℕ) (m : ℤ), 2 ≤ R.hShape T k m
  | .leaf, k, m => by simp only [RedReLU.hShape]; omega
  | .node l r, k, m => by
      simp only [RedReLU.hShape]
      exact le_trans (two_le_hShape R l _ _) (le_max_left _ _)

/-- **IV.5.4, volta (forma em ℕ).** `H_can(R) ≤ 2^(D+1) (M+2) W^(M+3)`. -/
theorem Hcan_le (R : RedReLU) (W D : ℕ) (h : Hip R W D) :
    R.Hcan ≤ 2 ^ (D + 1) * (R.data.length + 2) * W ^ (R.data.length + 3) := by
  unfold RedReLU.Hcan
  exact hShape_canon_le R W D h R.depth 0 0 le_rfl (by norm_num) (by simpa using h.hD)

theorem two_le_Hcan (R : RedReLU) : 2 ≤ R.Hcan := two_le_hShape R _ 0 0

/-! ## A cota logarítmica corrigida -/

/-- **IV.5.4, volta (enunciado corrigido).**
`log₂ H_can(R) ≤ 5 [(M+1) log₂(2W) + D + log₂(M+1)]`, com `M = #hinges`. -/
theorem reverse_height_bit_bound (R : RedReLU) (W D : ℕ) (h : Hip R W D) :
    Real.logb 2 (R.Hcan : ℝ) ≤
      5 * (((R.data.length : ℝ) + 1) * Real.logb 2 (2 * W) + D +
        Real.logb 2 ((R.data.length : ℝ) + 1)) := by
  have hW := h.one_le
  set M := R.data.length with hM
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hHpos : (0 : ℝ) < R.Hcan := by
    have := two_le_Hcan R
    exact_mod_cast (by omega : 0 < R.Hcan)
  have hB : (R.Hcan : ℝ) ≤ (2 : ℝ) ^ (D + 1) * ((M : ℝ) + 2) * (W : ℝ) ^ (M + 3) := by
    exact_mod_cast Hcan_le R W D h
  have hMr : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hb : (1 : ℝ) < 2 := by norm_num
  have step1 : Real.logb 2 (R.Hcan : ℝ) ≤
      Real.logb 2 ((2 : ℝ) ^ (D + 1) * ((M : ℝ) + 2) * (W : ℝ) ^ (M + 3)) :=
    Real.logb_le_logb_of_le hb hHpos hB
  have hW0 : (0 : ℝ) < W := by linarith
  have e1 : Real.logb 2 ((2 : ℝ) ^ (D + 1) * ((M : ℝ) + 2) * (W : ℝ) ^ (M + 3)) =
      ((D : ℝ) + 1) + Real.logb 2 ((M : ℝ) + 2) + ((M : ℝ) + 3) * Real.logb 2 W := by
    rw [Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity),
      Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hb]
    push_cast
    ring
  set L := Real.logb 2 (W : ℝ) with hL
  have hL0 : 0 ≤ L := Real.logb_nonneg hb hWr
  have e2 : Real.logb 2 (2 * (W : ℝ)) = 1 + L := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one hb]
  have hℓ0 : 0 ≤ Real.logb 2 ((M : ℝ) + 1) := Real.logb_nonneg hb (by linarith)
  have e3 : Real.logb 2 ((M : ℝ) + 2) ≤ 1 + Real.logb 2 ((M : ℝ) + 1) := by
    have : Real.logb 2 ((M : ℝ) + 2) ≤ Real.logb 2 (2 * ((M : ℝ) + 1)) :=
      Real.logb_le_logb_of_le hb (by positivity) (by linarith)
    rwa [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one hb] at this
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  rw [e2]
  refine step1.trans ?_
  rw [e1]
  nlinarith [mul_nonneg hL0 hMr]

/-! ## O enunciado original é falso, e nenhuma constante aditiva o conserta -/

/-- `R(x) = W·x`: `M = 0`, `D = 0`. -/
def affineW (W : ℕ) : RedReLU := ⟨0, W, []⟩

lemma affineW_hip (W : ℕ) (hW : 1 ≤ W) : Hip (affineW W) W 0 := by
  refine ⟨?_, ?_, by simp [affineW], by simp [affineW], ?_⟩
  · simp [affineW, ht]; omega
  · simp [affineW, ht]; omega
  · simp [affineW, RedReLU.depth, RedReLU.breaks]

lemma affineW_Hcan_ge (W : ℕ) (hW : 1 ≤ W) : W ≤ (affineW W).Hcan := by
  have hb : (affineW W).breaks = ∅ := by simp [affineW, RedReLU.breaks]
  have hd : (affineW W).depth = 0 := by simp [RedReLU.depth, hb]
  have hH : (affineW W).Hcan = (affineW W).hShape .leaf 0 0 := by
    unfold RedReLU.Hcan; rw [hd]; simp [canonShape]
  have hs : ht ((affineW W).slopeAt ((((0 : ℤ) : ℚ)) / 2 ^ 0)) = W := by
    simp [affineW, RedReLU.slopeAt, ht]; omega
  rw [hH]
  simp only [RedReLU.hShape]
  rw [hs]
  exact le_max_right _ _

/-- Para quaisquer constantes `C, C'`, a cota `log₂ H_can ≤ C·[M log(2W) + D + log(M+1)] + C'`
(o enunciado impresso, mesmo com termo constante) falha para `R(x) = W x` com `W` grande.
Em particular `(M+1)` — e não `M` — é necessário em `(M+1) log(2W)`. -/
theorem no_additive_constant_fix (C C' : ℝ) :
    ∃ W : ℕ, 1 ≤ W ∧ Hip (affineW W) W 0 ∧
      ¬ (Real.logb 2 ((affineW W).Hcan : ℝ) ≤
        C * (((affineW W).data.length : ℝ) * Real.logb 2 (2 * W) + (0 : ℕ) +
          Real.logb 2 (((affineW W).data.length : ℝ) + 1)) + C') := by
  refine ⟨2 ^ (⌈C'⌉₊ + 1), Nat.one_le_two_pow, affineW_hip _ Nat.one_le_two_pow, ?_⟩
  intro hle
  have hb : (1 : ℝ) < 2 := by norm_num
  have h1 := affineW_Hcan_ge (2 ^ (⌈C'⌉₊ + 1)) Nat.one_le_two_pow
  have hpos : (0 : ℝ) < ((2 ^ (⌈C'⌉₊ + 1) : ℕ) : ℝ) := by positivity
  have h2 : Real.logb 2 (((2 ^ (⌈C'⌉₊ + 1) : ℕ) : ℝ)) ≤ Real.logb 2 (((affineW (2 ^ (⌈C'⌉₊ + 1))).Hcan : ℝ)) :=
    Real.logb_le_logb_of_le hb hpos (by exact_mod_cast h1)
  have h3 : Real.logb 2 (((2 ^ (⌈C'⌉₊ + 1) : ℕ) : ℝ)) = (⌈C'⌉₊ : ℝ) + 1 := by
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one hb]
    push_cast; ring
  have h4 : C' ≤ (⌈C'⌉₊ : ℝ) := Nat.le_ceil C'
  have hdata : (affineW (2 ^ (⌈C'⌉₊ + 1))).data.length = 0 := rfl
  have hle' : Real.logb 2 (((affineW (2 ^ (⌈C'⌉₊ + 1))).Hcan : ℝ)) ≤ C' := by
    simpa [hdata] using hle
  linarith

end AlturaInversa

end Pendencias.Marcada
