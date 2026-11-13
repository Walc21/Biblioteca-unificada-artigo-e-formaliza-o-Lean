module

public import Unified.Fase1.Indexing

/-!
# The Calkin–Wilf enumeration

Section 2.3 of `artigo_fase1_autocontido.tex` states (without proof) that
`CW(n) = S_n / S_{n+1}`, `n ≥ 1`, enumerates `ℚ_{>0}` without repetitions.
This file proves that statement: `CWpos : ℕ+ → ℚ_{>0}` is a bijection.
-/

@[expose] public section

namespace Fase1

lemma stern_pos (n : ℕ) (hn : 1 ≤ n) : 0 < stern n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [stern_even]; exact ih j (by omega) (by omega)
    · rcases j with _ | j
      · simp [stern_one]
      · rw [stern_odd]; have := ih (j + 1) (by omega) (by omega); omega

lemma stern_coprime (n : ℕ) : Nat.Coprime (stern n) (stern (n + 1)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [stern_zero, stern_one]
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' (n + 1)
    · rw [hj, stern_even, stern_odd, add_comm]
      exact (Nat.coprime_add_self_right).2 (ih j (by omega))
    · rw [hj, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, stern_even, stern_odd, add_comm]
      exact (Nat.coprime_self_add_left).2 (ih j (by omega))

/-- Consecutive pairs `(S_n, S_{n+1})`, `n ≥ 1`, are pairwise distinct. -/
lemma stern_pair_injective {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (h1 : stern n = stern n') (h2 : stern (n + 1) = stern (n' + 1)) : n = n' := by
  induction n using Nat.strong_induction_on generalizing n' with
  | _ n ih =>
    have key : ∀ m, 1 ≤ m → (m = 1 ∧ stern m = stern (m+1)) ∨
        (∃ j, 1 ≤ j ∧ m = 2 * j ∧ stern m < stern (m + 1) ∧ stern m = stern j ∧
          stern (m+1) = stern j + stern (j+1)) ∨
        (∃ j, 1 ≤ j ∧ m = 2 * j + 1 ∧ stern (m + 1) < stern m ∧ stern (m+1) = stern (j+1) ∧
          stern m = stern j + stern (j+1)) := by
      intro m hm
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
      · right; left
        refine ⟨j, by omega, rfl, ?_, stern_even j, stern_odd j⟩
        rw [stern_even, stern_odd]; have := stern_pos (j+1) (by omega); omega
      · rcases j with _ | j
        · left; refine ⟨rfl, ?_⟩
          rw [show 2 * 0 + 1 + 1 = 2 * 1 by rfl, stern_even]
        · right; right
          refine ⟨j + 1, by omega, rfl, ?_, ?_, stern_odd (j+1)⟩
          · rw [show 2 * (j + 1) + 1 + 1 = 2 * (j + 1 + 1) by ring, stern_even, stern_odd]
            have := stern_pos (j+1) (by omega); omega
          · rw [show 2 * (j + 1) + 1 + 1 = 2 * (j + 1 + 1) by ring, stern_even]
    rcases key n hn with ⟨rfl, e⟩ | ⟨j, hj, rfl, lt, a1, a2⟩ | ⟨j, hj, rfl, lt, a1, a2⟩ <;>
    rcases key n' hn' with ⟨rfl, e'⟩ | ⟨j', hj', rfl, lt', b1, b2⟩ | ⟨j', hj', rfl, lt', b1, b2⟩
    all_goals first | rfl | omega | skip
    · have e1 : stern j = stern j' := by omega
      have := ih j (by omega) hj hj' e1 (by omega)
      omega
    · have e1 : stern (j + 1) = stern (j' + 1) := by omega
      have := ih j (by omega) hj hj' (by omega) e1
      omega

/-- Every coprime pair of positive integers occurs as `(S_n, S_{n+1})` with `n ≥ 1`. -/
lemma stern_pair_surjective (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : Nat.Coprime a b) :
    ∃ n, 1 ≤ n ∧ stern n = a ∧ stern (n + 1) = b := by
  induction h : a + b using Nat.strong_induction_on generalizing a b with
  | _ s ih =>
    rcases lt_trichotomy a b with hlt | heq | hgt
    · have hc : Nat.Coprime a (b - a) := by
        have : Nat.Coprime a (b - a + a) := by rwa [Nat.sub_add_cancel hlt.le]
        exact Nat.coprime_add_self_right.1 this
      obtain ⟨j, hj, h1, h2⟩ := ih (a + (b - a)) (by omega) a (b - a) ha (by omega) hc rfl
      refine ⟨2 * j, by omega, by rw [stern_even, h1], ?_⟩
      rw [stern_odd, h1, h2]; omega
    · subst heq
      have : a = 1 := by simpa using hab
      subst this
      exact ⟨1, le_rfl, stern_one, by rw [show 1 + 1 = 2 * 1 by rfl, stern_even, stern_one]⟩
    · have hc : Nat.Coprime (a - b) b := by
        have : Nat.Coprime (a - b + b) b := by rwa [Nat.sub_add_cancel hgt.le]
        exact Nat.coprime_add_self_left.1 this
      obtain ⟨j, hj, h1, h2⟩ := ih (a - b + b) (by omega) (a - b) b (by omega) hb hc rfl
      refine ⟨2 * j + 1, by omega, ?_, ?_⟩
      · rw [stern_odd, h1, h2]; omega
      · rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, stern_even, h2]

lemma CW_num_den (n : ℕ) (hn : 1 ≤ n) :
    (CW n).num = stern n ∧ (CW n).den = stern (n + 1) := by
  have := num_den_div_of_coprime (a := (stern n : ℤ)) (b := stern (n + 1))
    (stern_pos _ (by omega)) (by simpa using stern_coprime n)
  simpa [CW] using this

lemma CW_pos (n : ℕ+) : 0 < CW n := by
  unfold CW
  have := stern_pos n n.pos; have := stern_pos (n + 1) (by omega)
  positivity

/-- The Calkin–Wilf map `n ↦ S_n / S_{n+1}` as a map `ℕ_{≥1} → ℚ_{>0}`. -/
def CWpos (n : ℕ+) : {q : ℚ // 0 < q} := ⟨CW n, CW_pos n⟩

/-- `CW(n) = S_n/S_{n+1}`, `n ≥ 1`, enumerates `ℚ_{>0}` without repetitions. -/
theorem CWpos_bijective : Function.Bijective CWpos := by
  constructor
  · intro n n' h
    have h' : CW n = CW n' := congrArg Subtype.val h
    have a := CW_num_den n n.pos
    have b := CW_num_den n' n'.pos
    rw [h'] at a
    apply PNat.coe_injective
    exact stern_pair_injective n.pos n'.pos (by omega) (by omega)
  · rintro ⟨q, hq⟩
    have hnum : 0 < q.num := Rat.num_pos.2 hq
    obtain ⟨n, hn, h1, h2⟩ := stern_pair_surjective q.num.toNat q.den (by omega) q.den_pos
      (by have := q.reduced; rwa [show q.num.natAbs = q.num.toNat by omega] at this)
    refine ⟨⟨n, hn⟩, Subtype.ext ?_⟩
    show CW n = q
    unfold CW
    rw [h1, h2]
    have : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by
      exact_mod_cast (Int.toNat_of_nonneg hnum.le)
    rw [this, Rat.num_div_den]

end Fase1
