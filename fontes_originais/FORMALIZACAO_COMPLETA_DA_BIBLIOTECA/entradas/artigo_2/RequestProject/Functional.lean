import RequestProject.Interface

/-!
# Section 5 — Additive functional and canonical representation

* rational data, relative ownership, exact local loss,
* Lemma 5.1 (the recursive stream `ser_rec` is prefix-free, uniquely decodable and additive),
* the additive objective, the leaf cost `Φ_H`, the total tie key `κ`,
* Lemma 5.2 (compatibility of the tie-break with gluing).
-/

namespace Artigo

open Set LTree

/-! ## Lemma 5.1: the recursive stream -/

/-- `ser_rec(a) = 1 γ(n♯(a)+1)`, `ser_rec(R_L ∨ R_R) = 0 ser_rec(R_L) ser_rec(R_R)` -/
def serRec : LTree → List Bool
  | leaf a => true :: gamma (nSharp a + 1)
  | node l r => false :: (serRec l ++ serRec r)

/-- unique decodability in the strong form: a stream followed by anything determines the tree
and the remainder -/
theorem serRec_append_inj : ∀ (T T' : LTree) (s s' : List Bool),
    serRec T ++ s = serRec T' ++ s' → T = T' ∧ s = s' := by
  intro T
  induction T with
  | leaf a =>
    intro T' s s' h
    cases T' with
    | leaf b =>
      simp only [serRec, List.cons_append, List.cons.injEq, true_and] at h
      have h1 := decGamma_gamma (n := nSharp a + 1) (by omega) s
      have h2 := decGamma_gamma (n := nSharp b + 1) (by omega) s'
      rw [h] at h1
      rw [h1] at h2
      simp only [Option.some.injEq, Prod.mk.injEq, Nat.add_right_cancel_iff] at h2
      exact ⟨by rw [nSharp_injective h2.1.symm], h2.2⟩
    | node l r => simp [serRec] at h
  | node l r ihl ihr =>
    intro T' s s' h
    cases T' with
    | leaf b => simp [serRec] at h
    | node l' r' =>
      simp only [serRec, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨rfl, h2⟩ := ihl l' _ _ h
      obtain ⟨rfl, h4⟩ := ihr r' _ _ h2
      exact ⟨rfl, h4⟩

theorem serRec_injective : Function.Injective serRec := fun T T' h =>
  (serRec_append_inj T T' [] [] (by simpa using h)).1

/-- **Lemma 5.1 (decodificação e aditividade)**: the streams form a prefix-free set, each stream
determines a unique labelled tree, and `B(a) = 1 + |γ(n♯(a)+1)|`,
`B(R_L ∨ R_R) = 1 + B(R_L) + B(R_R)`. -/
theorem recursive_stream :
    (∀ T T' : LTree, serRec T <+: serRec T' → T = T') ∧ Function.Injective serRec ∧
    (∀ a : Atom, (serRec (leaf a)).length = 1 + (gamma (nSharp a + 1)).length) ∧
    (∀ l r : LTree, (serRec (node l r)).length = 1 + (serRec l).length + (serRec r).length) := by
  refine ⟨?_, serRec_injective, fun a => by simp [serRec]; ring, fun l r => by simp [serRec]; ring⟩
  rintro T T' ⟨s, hs⟩
  exact (serRec_append_inj T T' s [] (by simpa using hs)).1

/-! ## Data, ownership, loss and objective -/

/-- the data of a selection problem: dyadic root `K = J_{k₀,m₀}`, truncation `(D,H)`, rational
observations `(x_i, z_i, ω_i)` and rational penalties `λ_bits`, `λ_split` -/
structure Setup where
  H : ℕ
  D : ℕ
  k₀ : ℕ
  m₀ : ℤ
  data : List (ℚ × ℚ × ℚ)
  lb : ℚ
  ls : ℚ

/-- the line `ℓ_{J;u,v}` on `J = J_{k,m}` with end values `u, v` -/
def lineJ (k : ℕ) (m : ℤ) (u v x : ℚ) : ℚ := u + (v - u) * 2 ^ k * (x - m / 2 ^ k)

namespace Setup

variable (S : Setup)

/-- right end `β` of `K` -/
def beta : ℚ := (S.m₀ + 1) / 2 ^ S.k₀

/-- relative ownership `J^{own,K}`: `[a,b)` if `b < β`, `[a,b]` if `b = β` -/
def owns (k : ℕ) (m : ℤ) (x : ℚ) : Prop :=
  (m : ℚ) / 2 ^ k ≤ x ∧ (x < (m + 1) / 2 ^ k ∨ ((m + 1) / 2 ^ k = S.beta ∧ x = (m + 1) / 2 ^ k))

instance (k : ℕ) (m : ℤ) (x : ℚ) : Decidable (S.owns k m x) := by unfold owns; infer_instance

/-- the exact rational local loss `loss_𝒵(J;u,v)` -/
def loss (k : ℕ) (m : ℤ) (u v : ℚ) : ℚ :=
  ((S.data.filter fun p => S.owns k m p.1).map fun p => p.2.2 * (p.2.1 - lineJ k m u v p.1) ^ 2).sum

/-- the additive objective `cost_𝒵(R) = Σ_J loss + λ_bits B(R) + λ_split I(R)` (the leaf boundary
values of `g_R` are the end values of the leaf atoms, by continuity) -/
def costT (R : LTree) : ℚ :=
  (R.leaves.map fun a => S.loss a.k a.m a.lval a.rval).sum + S.lb * (serRec R).length +
    S.ls * R.numInternal

lemma costT_leaf (a : Atom) :
    S.costT (leaf a) = S.loss a.k a.m a.lval a.rval + S.lb * (1 + (gamma (nSharp a + 1)).length) := by
  simp only [costT, leaves, serRec, numInternal, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.length_cons]
  push_cast; ring

lemma costT_node (l r : LTree) : S.costT (node l r) = S.costT l + S.costT r + (S.lb + S.ls) := by
  simp only [costT, leaves, List.map_append, List.sum_append, serRec, List.length_cons,
    List.length_append, numInternal]
  push_cast; ring

/-- the leaf cost `Φ_H(J;u,v)` (`+∞` for inadmissible pairs) -/
noncomputable def Phi (k : ℕ) (m : ℤ) (u v : ℚ) : WithTop ℚ :=
  if h : (u, v) ∈ PH S.H k m then
    ((S.loss k m u v + S.lb * (1 + (gamma (nSharp (Atom.ofEndpoints k m u v
      (mem_PH.mp h).1) + 1)).length) : ℚ) : WithTop ℚ)
  else ⊤

/-- the cost of a leaf representation is its leaf cost -/
lemma Phi_atom {a : Atom} (ha : a.height ≤ S.H) :
    S.Phi a.k a.m a.lval a.rval = (S.costT (leaf a) : WithTop ℚ) := by
  have h2 : 2 ≤ S.H := le_trans a.two_le_height ha
  have hmem : (a.lval, a.rval) ∈ PH S.H a.k a.m :=
    (endpoint_dictionary h2).1.1 ⟨ha, rfl, rfl⟩
  unfold Phi
  rw [dif_pos hmem, costT_leaf, ← a.eq_ofEndpoints]

/-- the tie key `κ(R) = (cost(R), |ser_rec(R)|, ser_rec(R))`, ordered lexicographically.  The last
two coordinates are encoded by the shortlex rank (`slRank`), which orders by length first and
then lexicographically, exactly as `κ`. -/
def kappa (R : LTree) : Lex (ℚ × ℕ) := toLex (S.costT R, slRank (serRec R))

lemma kappa_injective : Function.Injective S.kappa := by
  intro R R' h
  simp only [kappa, toLex_inj, Prod.mk.injEq] at h
  exact serRec_injective (slRank_injective h.2)

end Setup

/-! ## Lemma 5.2 -/

lemma ofBits_append : ∀ (u w : List Bool), ofBits (u ++ w) = ofBits u * 2 ^ w.length + ofBits w := by
  intro u
  induction u with
  | nil => simp [ofBits]
  | cons b u ih =>
    intro w
    simp only [List.cons_append, ofBits, List.length_append, ih]
    split_ifs <;> ring

lemma slRank_le_iff (u v : List Bool) :
    slRank u ≤ slRank v ↔ u.length < v.length ∨ (u.length = v.length ∧ ofBits u ≤ ofBits v) := by
  rw [← not_lt, slRank_lt_iff]
  have := ofBits_lt u
  have := ofBits_lt v
  omega

lemma slRank_glue {u u' w w' : List Bool} (hu : slRank u ≤ slRank u') (hw : slRank w ≤ slRank w') :
    slRank (false :: (u ++ w)) ≤ slRank (false :: (u' ++ w')) := by
  rw [slRank_le_iff] at hu hw ⊢
  simp only [List.length_cons, List.length_append, ofBits, Bool.false_eq_true, if_false, zero_add,
    ofBits_append]
  rcases hu with hu | ⟨hu1, hu2⟩ <;> rcases hw with hw | ⟨hw1, hw2⟩
  · left; omega
  · left; omega
  · left; omega
  · right
    refine ⟨by omega, ?_⟩
    rw [hw1]
    have := Nat.mul_le_mul_right (2 ^ w'.length) hu2
    omega

/-- **Lemma 5.2 (compatibilidade do desempate com a colagem)**: if `κ(R_L) ≤ κ(R'_L)` and
`κ(R_R) ≤ κ(R'_R)` then `κ(R_L ∨ R_R) ≤ κ(R'_L ∨ R'_R)`. -/
theorem tie_concatenation (S : Setup) {L L' R R' : LTree} (hL : S.kappa L ≤ S.kappa L')
    (hR : S.kappa R ≤ S.kappa R') : S.kappa (node L R) ≤ S.kappa (node L' R') := by
  simp only [Setup.kappa, Prod.Lex.toLex_le_toLex] at hL hR ⊢
  rw [S.costT_node, S.costT_node]
  rcases hL with hL | ⟨hL1, hL2⟩ <;> rcases hR with hR | ⟨hR1, hR2⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · right
    refine ⟨by rw [hL1, hR1], ?_⟩
    exact slRank_glue hL2 hR2

end Artigo
