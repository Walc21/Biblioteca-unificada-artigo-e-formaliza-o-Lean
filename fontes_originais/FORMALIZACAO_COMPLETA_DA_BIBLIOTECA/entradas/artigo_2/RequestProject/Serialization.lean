import RequestProject.Addresses
import RequestProject.Formats

/-!
# Theorem 3.6 (serialização condicionada de montagens)

Given the shared root cell `J_{k,m}`, an assembly is transmitted as
`γ(N) γ(H)` followed by `N` fixed-width address blocks.  No separate skeleton is needed:
the tree is reconstructed from the (spatially ordered) leaf cells.
-/

namespace Artigo

open LTree

/-! ## Recovering the tree from the leaf cells -/

/-- every leaf cell of a well-formed tree rooted at `J_{k,m}` descends from `J_{k,m}` -/
lemma WF_leaf_anc : ∀ {k : ℕ} {m : ℤ} {T : LTree}, WF k m T → ∀ a ∈ T.leaves,
    k ≤ a.k ∧ a.m / 2 ^ (a.k - k) = m := by
  intro k m T
  induction T generalizing k m with
  | leaf a =>
    intro h b hb
    simp only [leaves, List.mem_singleton] at hb; subst hb
    obtain ⟨h1, h2⟩ := h; subst h1; subst h2; simp
  | node l r ihl ihr =>
    intro h b hb
    obtain ⟨hl, hr, _⟩ := h
    simp only [leaves, List.mem_append] at hb
    have key : ∀ (c : ℤ), (k + 1 ≤ b.k ∧ b.m / 2 ^ (b.k - (k + 1)) = 2 * m + c) → c = 0 ∨ c = 1 →
        k ≤ b.k ∧ b.m / 2 ^ (b.k - k) = m := by
      intro c ⟨h1, h2⟩ hc
      refine ⟨by omega, ?_⟩
      have hk : b.k - k = (b.k - (k + 1)) + 1 := by omega
      rw [hk, pow_succ, ← Int.ediv_ediv_of_nonneg (by positivity), h2]
      rcases hc with hc | hc <;> subst hc <;> omega
    rcases hb with hb | hb
    · exact key 0 (by simpa using ihl hl b hb) (Or.inl rfl)
    · exact key 1 (ihr hr b hb) (Or.inr rfl)

/-- membership test "the cell of `a` lies inside the left child of `J_{k,m}`" -/
def inLeft (k : ℕ) (m : ℤ) (a : Atom) : Bool := decide (k < a.k ∧ a.m / 2 ^ (a.k - (k + 1)) = 2 * m)

/-- reconstruction of the tree from the spatially ordered list of leaf atoms (with fuel) -/
def build : ℕ → ℕ → ℤ → List Atom → Option LTree
  | 0, _, _, L => L.head?.map leaf
  | f + 1, k, m, L =>
    if L.length ≤ 1 then L.head?.map leaf else
      match build f (k + 1) (2 * m) (L.takeWhile (inLeft k m)),
          build f (k + 1) (2 * m + 1) (L.dropWhile (inLeft k m)) with
      | some l, some r => some (node l r)
      | _, _ => none

lemma leaves_ne_nil (T : LTree) : T.leaves ≠ [] := by
  have := T.numLeaves_pos; intro h; simp [numLeaves, h] at this

theorem build_leaves : ∀ (T : LTree) {k : ℕ} {m : ℤ}, WF k m T → ∀ f, T.depth ≤ f →
    build f k m T.leaves = some T := by
  intro T
  induction T with
  | leaf a => intro k m _ f _; cases f <;> simp [build, leaves]
  | node l r ihl ihr =>
    intro k m h f hf
    obtain ⟨hl, hr, _⟩ := h
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [depth] at hf; omega⟩
    simp only [depth] at hf
    have hpos : ∀ a ∈ l.leaves, inLeft k m a = true := by
      intro a ha
      obtain ⟨h1, h2⟩ := WF_leaf_anc hl a ha
      simp only [inLeft, decide_eq_true_eq]; exact ⟨by omega, h2⟩
    obtain ⟨b, lb, hb⟩ := List.exists_cons_of_ne_nil (leaves_ne_nil r)
    have hneg : ¬ inLeft k m b = true := by
      obtain ⟨h1, h2⟩ := WF_leaf_anc hr b (by rw [hb]; simp)
      simp only [inLeft, decide_eq_true_eq]; omega
    have ht : (l.leaves ++ r.leaves).takeWhile (inLeft k m) = l.leaves := by
      rw [List.takeWhile_append_of_pos hpos, hb, List.takeWhile_cons_of_neg hneg]; simp
    have hd : (l.leaves ++ r.leaves).dropWhile (inLeft k m) = r.leaves := by
      rw [List.dropWhile_append_of_pos hpos, hb, List.dropWhile_cons_of_neg hneg]
    have hlen : ¬ (l.leaves ++ r.leaves).length ≤ 1 := by
      have := l.numLeaves_pos; have := r.numLeaves_pos
      simp only [numLeaves] at *; simp; omega
    simp only [leaves, build, hlen, if_false, ht, hd]
    rw [ihl hl f (by omega), ihr hr f (by omega)]

lemma depth_lt_numLeaves (T : LTree) : T.depth < T.numLeaves := by
  induction T with
  | leaf a => simp [depth, numLeaves, leaves]
  | node l r ihl ihr =>
    rw [numLeaves_node]; simp only [depth]
    have := l.numLeaves_pos; have := r.numLeaves_pos
    omega

lemma two_le_maxHeight (T : LTree) : 2 ≤ T.maxHeight := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ (leaves_ne_nil T)
  exact le_trans a.two_le_height (le_maxHeight ha)

/-! ## Fixed-width blocks -/

/-- fixed-width binary codec -/
def fixedCodec (w : ℕ) : Codec ℕ where
  enc n := toBits w n
  dec s := if w ≤ s.length then some (ofBits (s.take w), s.drop w) else none

lemma fixedCodec_RT (w : ℕ) : (fixedCodec w).RT (fun n => n < 2 ^ w) := by
  intro n hn t
  simp [fixedCodec, ofBits_toBits w n hn]

lemma length_flatten_const {α : Type*} (L : List α) (f : α → List Bool) (w : ℕ)
    (h : ∀ x, (f x).length = w) : (L.map f).flatten.length = L.length * w := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.flatten_cons, List.length_append, ih, h,
      List.length_cons]; ring

/-! ## Generic serializer parametrized by an address enumeration -/

/-- `γ(N) γ(H)` followed by the `N` addresses, each in a block of width `w H` -/
def serGen (A : Atom → ℕ) (w : ℕ → ℕ) (T : LTree) : List Bool :=
  gamma T.numLeaves ++ gamma T.maxHeight ++ (fixedCodec (w T.maxHeight)).encList (T.leaves.map A)

/-- the corresponding decoder; it needs neither `N` nor `H` in advance -/
def decGen (G : ℕ → Atom) (w : ℕ → ℕ) (k : ℕ) (m : ℤ) (s : List Bool) : Option (LTree × List Bool) :=
  match decGamma s with
  | none => none
  | some (N, s₁) => match decGamma s₁ with
    | none => none
    | some (H, s₂) => match (fixedCodec (w H)).decN N s₂ with
      | none => none
      | some (L, s₃) => match build N k m (L.map G) with
        | none => none
        | some T => some (T, s₃)

lemma decGen_serGen (A : Atom → ℕ) (G : ℕ → Atom) (hG : ∀ a, G (A a) = a) (w : ℕ → ℕ)
    (hw : ∀ a : Atom, ∀ H, a.height ≤ H → A a < 2 ^ w H) {k : ℕ} {m : ℤ} {T : LTree}
    (hT : WF k m T) (t : List Bool) : decGen G w k m (serGen A w T ++ t) = some (T, t) := by
  unfold serGen decGen
  rw [List.append_assoc, List.append_assoc, decGamma_gamma T.numLeaves_pos]
  simp only
  rw [decGamma_gamma (le_trans (by norm_num) (two_le_maxHeight T))]
  simp only
  have hdec := (fixedCodec_RT (w T.maxHeight)).decN (T.leaves.map A)
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨a, ha, rfl⟩ := hx
        exact hw a _ (le_maxHeight ha)) t
  rw [List.length_map] at hdec
  simp only [numLeaves] at hdec ⊢
  rw [hdec]
  simp only [List.map_map]
  have : (G ∘ A) = id := funext hG
  have hb := build_leaves T hT _ (le_of_lt (depth_lt_numLeaves T))
  simp only [numLeaves] at hb
  rw [this, List.map_id, hb]

lemma serGen_length (A : Atom → ℕ) (w : ℕ → ℕ) (T : LTree) :
    (serGen A w T).length = (2 * Nat.log 2 T.numLeaves + 1) + (2 * Nat.log 2 T.maxHeight + 1)
      + T.numLeaves * w T.maxHeight := by
  simp only [serGen, Codec.encList, List.length_append, gamma_length, List.map_map]
  rw [length_flatten_const _ _ (w T.maxHeight) (by intro x; simp [fixedCodec])]
  simp [numLeaves]

/-! ## Theorem 3.6 -/

/-- per-leaf width with `Γ♯` is `⌈log₂(18H⁶)⌉ = 6 log₂ H + O(1)` -/
lemma clog_sharp_le (H : ℕ) : Nat.clog 2 (18 * H ^ 6) ≤ 6 * Nat.log 2 H + 11 := by
  apply Nat.clog_le_of_le_pow
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) H
  have h6 : H ^ 6 ≤ (2 ^ (Nat.log 2 H + 1)) ^ 6 := Nat.pow_le_pow_left h.le 6
  calc 18 * H ^ 6 ≤ 2 ^ 5 * (2 ^ (Nat.log 2 H + 1)) ^ 6 := by omega
    _ = 2 ^ (6 * Nat.log 2 H + 11) := by rw [← pow_mul, ← pow_add]; ring_nf

/-- per-leaf width with `Γ` is `⌈log₂(2116H⁸+1)⌉ = 8 log₂ H + O(1)` -/
lemma clog_gamma_le (H : ℕ) : Nat.clog 2 (2116 * H ^ 8 + 1) ≤ 8 * Nat.log 2 H + 20 := by
  apply Nat.clog_le_of_le_pow
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) H
  have h8 : H ^ 8 ≤ (2 ^ (Nat.log 2 H + 1)) ^ 8 := Nat.pow_le_pow_left h.le 8
  have : 1 ≤ (2 ^ (Nat.log 2 H + 1)) ^ 8 := Nat.one_le_pow _ _ (by positivity)
  calc 2116 * H ^ 8 + 1 ≤ 2 ^ 12 * (2 ^ (Nat.log 2 H + 1)) ^ 8 := by omega
    _ = 2 ^ (8 * Nat.log 2 H + 20) := by rw [← pow_mul, ← pow_add]; ring_nf

/-- **Theorem 3.6 (serialização condicionada de montagens)**, `Γ♯` version.  For a shared root
cell `J_{k,m}` there is a self-delimiting bit stream, decodable without knowing `N` or `H`,
of length `≤ (2⌊log₂N⌋+1) + (2⌊log₂H⌋+1) + N⌈log₂(18H⁶)⌉`, where `N` is the number of leaves
and `H` the maximal atomic height; the per-leaf term is `6 log₂ H + O(1)`. -/
theorem assembly_serialization (k : ℕ) (m : ℤ) :
    ∃ (ser : LTree → List Bool) (dec : List Bool → Option (LTree × List Bool)),
      (∀ T, WF k m T → ∀ t, dec (ser T ++ t) = some (T, t)) ∧
      (∀ T, WF k m T → (ser T).length ≤ (2 * Nat.log 2 T.numLeaves + 1)
          + (2 * Nat.log 2 T.maxHeight + 1) + T.numLeaves * Nat.clog 2 (18 * T.maxHeight ^ 6)) ∧
      (∀ T, WF k m T → (ser T).length ≤ (2 * Nat.log 2 T.numLeaves + 1)
          + (2 * Nat.log 2 T.maxHeight + 1) + T.numLeaves * (6 * Nat.log 2 T.maxHeight + 11)) := by
  have hw : ∀ a : Atom, ∀ H, a.height ≤ H → nSharp a < 2 ^ (Nat.clog 2 (18 * H ^ 6)) := by
    intro a H hH
    have h2 : 2 ≤ H := le_trans a.two_le_height hH
    calc nSharp a < (LH H).card := nSharp_lt hH
      _ ≤ 18 * H ^ 6 := card_LH_le h2
      _ ≤ _ := Nat.le_pow_clog (by norm_num) _
  refine ⟨serGen nSharp (fun H => Nat.clog 2 (18 * H ^ 6)),
    decGen GammaSharp (fun H => Nat.clog 2 (18 * H ^ 6)) k m,
    fun T hT t => decGen_serGen _ _ GammaSharp_nSharp _ hw hT t,
    fun T _ => (serGen_length _ _ T).le, fun T _ => ?_⟩
  rw [serGen_length]
  have := clog_sharp_le T.maxHeight
  gcongr

/-- **Theorem 3.6**, version with the arithmetic generator `Γ`: the per-leaf term is
`⌈log₂(2116H⁸+1)⌉ ≤ 8 log₂ H + O(1)` bits. -/
theorem assembly_serialization_Gamma (k : ℕ) (m : ℤ) :
    ∃ (ser : LTree → List Bool) (dec : List Bool → Option (LTree × List Bool)),
      (∀ T, WF k m T → ∀ t, dec (ser T ++ t) = some (T, t)) ∧
      (∀ T, WF k m T → (ser T).length ≤ (2 * Nat.log 2 T.numLeaves + 1)
          + (2 * Nat.log 2 T.maxHeight + 1) + T.numLeaves * (8 * Nat.log 2 T.maxHeight + 20)) := by
  classical
  have hw : ∀ a : Atom, ∀ H, a.height ≤ H → a.addr < 2 ^ (Nat.clog 2 (2116 * H ^ 8 + 1)) := by
    intro a H hH
    calc a.addr ≤ 2116 * a.height ^ 8 := a.addr_le
      _ < 2116 * H ^ 8 + 1 := by have := Nat.pow_le_pow_left hH 8; omega
      _ ≤ _ := Nat.le_pow_clog (by norm_num) _
  haveI : Nonempty Atom := ⟨⟨0, 0, 0, 1, one_ne_zero⟩⟩
  refine ⟨serGen Atom.addr (fun H => Nat.clog 2 (2116 * H ^ 8 + 1)),
    decGen (Function.invFun Atom.addr) (fun H => Nat.clog 2 (2116 * H ^ 8 + 1)) k m,
    fun T hT t => decGen_serGen _ _ (Function.leftInverse_invFun Atom.addr_injective) _ hw hT t,
    fun T _ => ?_⟩
  rw [serGen_length]
  have := clog_gamma_le T.maxHeight
  gcongr

end Artigo
