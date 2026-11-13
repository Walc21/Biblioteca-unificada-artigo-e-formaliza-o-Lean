import Pendencias.FormaAncorada
import RequestProject.Coding

/-!
# IV.5.4 (parte direta) — código prefix-free da forma ancorada

`anchoredCodec : Codec Anchored` codifica `(x_*, g(x_*), σ₀, [(τ_j, σ_j - σ_{j-1})])`:
`x_*` e os `τ_j` pelo código diádico, os demais racionais pelo código racional, e a lista de
hinges com cabeçalho `γ(M+1)`.  Mostramos decodificação exata (logo prefix-free) e
comprimento `≤ 40 N ⌊log₂ 2H⌋`.
-/

namespace Pendencias.Marcada

open Artigo

namespace Ancorada

lemma gamma_length (n : ℕ) : (gamma n).length = 2 * Nat.log 2 n + 1 := by
  simp [gamma, toBits]; ring

/-- lista com cabeçalho `γ(|L|+1)` -/
def listCodec {α : Type*} (c : Codec α) : Codec (List α) where
  enc L := gamma (L.length + 1) ++ c.encList L
  dec s := match decGamma s with
    | none => none
    | some (n, s₁) => c.decN (n - 1) s₁

lemma RT_mono {α : Type*} {c : Codec α} {P Q : α → Prop} (h : c.RT P)
    (hPQ : ∀ x, Q x → P x) : c.RT Q := fun x hx t => h x (hPQ x hx) t

lemma listCodec_RT {α : Type*} {c : Codec α} {P : α → Prop} (h : c.RT P) :
    (listCodec c).RT (fun L => ∀ x ∈ L, P x) := by
  intro L hL t
  simp only [listCodec, List.append_assoc]
  rw [decGamma_gamma (by omega)]
  simp only [Nat.add_sub_cancel]
  exact h.decN L hL t

/-- código de um hinge `(τ, a)` -/
abbrev hingeCodec : Codec (ℚ × ℚ) := dyadCodec.prod ratCodec

/-- código da forma ancorada -/
def anchoredCodec : Codec Anchored :=
  (dyadCodec.prod (ratCodec.prod (ratCodec.prod (listCodec hingeCodec)))).map
    (fun A => (A.xs, A.ys, A.s0, A.hinges))
    (fun p => some ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩)

/-- validade para a decodificação: `x_*` e os `τ_j` diádicos -/
def AnchoredValid (A : Anchored) : Prop := IsDyadic A.xs ∧ ∀ q ∈ A.hinges, IsDyadic q.1

theorem anchoredCodec_RT : anchoredCodec.RT AnchoredValid := by
  have hh : hingeCodec.RT (fun q => IsDyadic q.1) :=
    RT_mono (dyadCodec_RT.prod ratCodec_RT) (fun q hq => ⟨hq, trivial⟩)
  have hl := listCodec_RT hh
  have hr1 := RT_mono (ratCodec_RT.prod hl)
    (Q := fun p : ℚ × List (ℚ × ℚ) => ∀ x ∈ p.2, IsDyadic x.1) (fun p hp => ⟨trivial, hp⟩)
  have hr2 := RT_mono (ratCodec_RT.prod hr1)
    (Q := fun p : ℚ × ℚ × List (ℚ × ℚ) => ∀ x ∈ p.2.2, IsDyadic x.1)
    (fun p hp => ⟨trivial, hp⟩)
  have hall := dyadCodec_RT.prod hr2
  apply Codec.RT.map hall
  intro A hA
  exact ⟨⟨hA.1, hA.2⟩, rfl⟩

/-- comprimento exato do código -/
lemma anchoredCodec_length (A : Anchored) :
    (anchoredCodec.enc A).length =
      (dyadCodec.enc A.xs).length + ((ratCodec.enc A.ys).length + ((ratCodec.enc A.s0).length +
        (2 * Nat.log 2 (A.hinges.length + 1) + 1 +
          (A.hinges.map fun q => (dyadCodec.enc q.1).length + (ratCodec.enc q.2).length).sum))) := by
  simp only [anchoredCodec, Codec.map, Codec.prod, listCodec, hingeCodec, List.length_append,
    Codec.encList_length, gamma_length]

lemma log2_mul_le {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nat.log 2 (a * b) ≤ Nat.log 2 a + Nat.log 2 b + 1 := by
  have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) a
  have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) b
  have h3 : a * b < 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by
    calc a * b < 2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 b + 1) := Nat.mul_lt_mul'' h1 h2
      _ = 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by rw [← pow_add]; ring_nf
  have := Nat.log_lt_of_lt_pow (by positivity) h3
  omega

/-- uma fração `m/2^k` tem numerador e denominador reduzidos controlados -/
lemma dyadic_bounds {t : ℚ} {m : ℤ} {k : ℕ} (h : t = (m : ℚ) / 2 ^ k) :
    ∃ j, t.den = 2 ^ j ∧ j ≤ k ∧ t.num.natAbs ≤ m.natAbs := by
  have ht' : t = Rat.divInt m ((2 : ℤ) ^ k) := by
    rw [h, Rat.divInt_eq_div]; push_cast; rfl
  have hd : ((t.den : ℕ) : ℤ) ∣ ((2 : ℤ) ^ k) := by
    rw [ht']; exact Rat.den_dvd _ _
  have hd' : t.den ∣ 2 ^ k := by
    have : ((t.den : ℕ) : ℤ) ∣ (((2 ^ k : ℕ)) : ℤ) := by simpa using hd
    exact Int.natCast_dvd_natCast.mp this
  obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd'
  refine ⟨j, hj, hjk, ?_⟩
  by_cases hm : m = 0
  · subst hm; simp [h]
  · have hn : t.num ∣ m := by
      rw [ht']; exact Rat.num_dvd _ (by positivity)
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hm) (Int.natAbs_dvd_natAbs.mpr hn)

/-- **Comprimento**: `|C(A)| ≤ 40 · N · ⌊log₂ 2H⌋` para toda forma ancorada que satisfaz a
especificação de `anchored_form`. -/
theorem anchored_length {N H : ℕ} {g : ℝ → ℝ} {A : Anchored} (hH : 1 ≤ H)
    (hs : AnchoredSpec N H g A) :
    (anchoredCodec.enc A).length ≤ 40 * N * Nat.log 2 (2 * H) := by
  obtain ⟨-, ⟨k0, hk0, hxs⟩, -, hlen, -, -, hys, hs0, -, hjump, hknot⟩ := hs
  set ℓ := Nat.log 2 (2 * H) with hℓ
  have hℓ1 : 1 ≤ ℓ := by
    have : Nat.log 2 2 ≤ Nat.log 2 (2 * H) := Nat.log_mono_right (by omega)
    simpa using this
  have hlogH : Nat.log 2 H ≤ ℓ := Nat.log_mono_right (by omega)
  -- x_*
  have hxsl : (dyadCodec.enc A.xs).length ≤ 2 * ℓ + 6 := by
    obtain ⟨j, hj, hjk, hnum⟩ := dyadic_bounds (t := A.xs) (m := 1) (k := k0 + 1)
      (by rw [hxs]; simp)
    have := dyadCodec_length_le (t := A.xs) (A := 1) (B := 2 * H) le_rfl (by simpa using hnum)
      hj (by omega)
    simpa [hℓ] using this
  have hrat : ∀ r : ℚ, ht r ≤ H → (ratCodec.enc r).length ≤ 4 * ℓ + 7 := by
    intro r hr
    have := ratCodec_length_le hH hr
    omega
  have hys' := hrat _ hys
  have hs0' := hrat _ hs0
  -- hinges
  have hh : ∀ q ∈ A.hinges,
      (dyadCodec.enc q.1).length + (ratCodec.enc q.2).length ≤ 29 * ℓ := by
    intro q hq
    obtain ⟨k, m, hqm, hk, hm⟩ := hknot q hq
    obtain ⟨j, hj, hjk, hnum⟩ := dyadic_bounds hqm
    have h1 := dyadCodec_length_le (t := q.1) (A := H) (B := H) hH (by omega) hj (by omega)
    have h2 := ratCodec_length_le (r := q.2) (A := 2 * H ^ 2) (by have : 1 ≤ H ^ 2 := Nat.one_le_pow _ _ hH; omega) (hjump q hq)
    have h3 : Nat.log 2 (2 * H ^ 2) ≤ 2 * ℓ + 1 := by
      have := log2_mul_le (a := 2 * H) (b := H) (by omega) hH
      calc Nat.log 2 (2 * H ^ 2) ≤ Nat.log 2 ((2 * H) * H) :=
            Nat.log_mono_right (by nlinarith)
        _ ≤ ℓ + Nat.log 2 H + 1 := this
        _ ≤ 2 * ℓ + 1 := by omega
    omega
  have hsum : (A.hinges.map fun q => (dyadCodec.enc q.1).length + (ratCodec.enc q.2).length).sum
      ≤ A.hinges.length * (29 * ℓ) := by
    have := List.sum_le_card_nsmul
      (A.hinges.map fun q => (dyadCodec.enc q.1).length + (ratCodec.enc q.2).length) (29 * ℓ)
      (by
        intro x hx
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        exact hh q hq)
    simpa using this
  have hhdr : 2 * Nat.log 2 (A.hinges.length + 1) + 1 ≤ 2 * N + 1 := by
    have := Nat.log_le_self 2 (A.hinges.length + 1)
    omega
  rw [anchoredCodec_length]
  set M := A.hinges.length
  have hMl : M * ℓ + ℓ ≤ N * ℓ := by nlinarith
  have hNl : N ≤ N * ℓ := Nat.le_mul_of_pos_right N hℓ1
  have hN1 : 1 ≤ N := by omega
  nlinarith

lemma anchored_valid {N H : ℕ} {g : ℝ → ℝ} {A : Anchored} (hs : AnchoredSpec N H g A) :
    AnchoredValid A := by
  obtain ⟨-, ⟨k0, -, hxs⟩, -, -, -, -, -, -, -, -, hknot⟩ := hs
  refine ⟨?_, fun q hq => ?_⟩
  · obtain ⟨j, hj, -, -⟩ := dyadic_bounds (t := A.xs) (m := 1) (k := k0 + 1) (by rw [hxs]; simp)
    exact ⟨j, hj⟩
  · obtain ⟨k, m, hqm, -, -⟩ := hknot q hq
    obtain ⟨j, hj, -, -⟩ := dyadic_bounds hqm
    exact ⟨j, hj⟩

/-- **IV.5.4, parte direta (fechada).**  Toda `g ∈ 𝒜^□_{N,H}([0,1])` tem forma ancorada reduzida
com `M ≤ N-1` hinges, alturas `≤ H` (valor em `x_*` e inclinações locais), saltos de altura
`≤ 2H²` e pares estruturais de altura `≤ H`; essa forma é codificada de modo prefix-free
(decodificação exata) com `≤ 40 N ⌊log₂ 2H⌋ ≤ 40 N log₂ 2H` bits. -/
theorem direct_part {N H : ℕ} {g : ℝ → ℝ} (hg : g ∈ MAsmNH N H) :
    ∃ A : Anchored, AnchoredSpec N H g A ∧ AnchoredValid A ∧
      (∀ t, anchoredCodec.dec (anchoredCodec.enc A ++ t) = some (A, t)) ∧
      (anchoredCodec.enc A).length ≤ 40 * N * Nat.log 2 (2 * H) ∧
      ((anchoredCodec.enc A).length : ℝ) ≤ 40 * N * Real.logb 2 (2 * H) := by
  obtain ⟨A, hs⟩ := anchored_form hg
  have hys := hs.2.2.2.2.2.2.1
  have hH : 1 ≤ H := le_trans A.ys.den_pos (le_trans (le_max_right _ _) hys)
  have hv := anchored_valid hs
  have hlen := anchored_length hH hs
  refine ⟨A, hs, hv, fun t => anchoredCodec_RT A hv t, hlen, ?_⟩
  have h1 : ((Nat.log 2 (2 * H) : ℕ) : ℝ) ≤ Real.logb 2 ((2 * H : ℕ) : ℝ) :=
    Real.natLog_le_logb (2 * H) 2
  push_cast at h1
  have h2 : ((anchoredCodec.enc A).length : ℝ) ≤ 40 * (N : ℝ) * (Nat.log 2 (2 * H) : ℕ) := by
    exact_mod_cast hlen
  calc ((anchoredCodec.enc A).length : ℝ) ≤ 40 * (N : ℝ) * (Nat.log 2 (2 * H) : ℕ) := h2
    _ ≤ 40 * (N : ℝ) * Real.logb 2 (2 * H) := by gcongr

/-- consequência: prefix-free (injetividade e ausência de prefixos próprios) -/
theorem anchored_prefix_free {A B : Anchored} (hA : AnchoredValid A) (hB : AnchoredValid B)
    (h : anchoredCodec.enc A <+: anchoredCodec.enc B) : A = B :=
  anchoredCodec_RT.prefix_free hA hB h

end Ancorada

end Pendencias.Marcada
