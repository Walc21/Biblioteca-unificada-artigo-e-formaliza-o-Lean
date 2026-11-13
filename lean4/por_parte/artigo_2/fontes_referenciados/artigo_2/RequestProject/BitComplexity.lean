import RequestProject.Complexity

/-!
# Section 9.2 — Bit complexity of the rational costs

We define the bit length `bl(p/q) = 1 + ⌈log₂(|p|+1)⌉ + ⌈log₂(q+1)⌉` of a reduced fraction and
prove the growth bound of Theorem 9.2: every cost of a representation appearing in the recursion
has bit length `O(P (B_𝒵 + D + k₀ + log(2H)) + B_𝒵 + log(2L))`, with explicit constants.
-/

namespace Artigo

open Set LTree

/-- the bit length of a rational in lowest terms -/
def bl (r : ℚ) : ℕ := 1 + Nat.clog 2 (r.num.natAbs + 1) + Nat.clog 2 (r.den + 1)

/-- `r` is a quotient `a / b` with `|a|, b ≤ 2^e` (not necessarily reduced) -/
def QB (e : ℕ) (r : ℚ) : Prop :=
  ∃ (a : ℤ) (b : ℕ), 0 < b ∧ r = a / b ∧ a.natAbs ≤ 2 ^ e ∧ b ≤ 2 ^ e

lemma QB.mono {e e' : ℕ} {r : ℚ} (h : QB e r) (he : e ≤ e') : QB e' r := by
  obtain ⟨a, b, hb, rfl, ha, hb'⟩ := h
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) he
  exact ⟨a, b, hb, rfl, ha.trans this, hb'.trans this⟩

lemma QB_zero : QB 0 0 := ⟨0, 1, one_pos, by simp, by simp, by simp⟩

lemma QB_nat {n e : ℕ} (h : n ≤ 2 ^ e) : QB e (n : ℚ) :=
  ⟨n, 1, one_pos, by simp, by simpa using h, Nat.one_le_two_pow⟩

lemma QB.add {e f : ℕ} {r s : ℚ} (hr : QB e r) (hs : QB f s) : QB (e + f + 1) (r + s) := by
  obtain ⟨a, b, hb, rfl, ha, hb'⟩ := hr
  obtain ⟨c, d, hd, rfl, hc, hd'⟩ := hs
  refine ⟨a * d + c * b, b * d, Nat.mul_pos hb hd, ?_, ?_, ?_⟩
  · have : (b : ℚ) ≠ 0 := by positivity
    have : (d : ℚ) ≠ 0 := by positivity
    push_cast; field_simp
  · calc (a * d + c * b).natAbs ≤ (a * d).natAbs + (c * b).natAbs := Int.natAbs_add_le _ _
      _ = a.natAbs * d + c.natAbs * b := by simp [Int.natAbs_mul]
      _ ≤ 2 ^ e * 2 ^ f + 2 ^ f * 2 ^ e := Nat.add_le_add (Nat.mul_le_mul ha hd') (Nat.mul_le_mul hc hb')
      _ = 2 ^ (e + f + 1) := by rw [pow_succ, pow_add]; ring
  · calc b * d ≤ 2 ^ e * 2 ^ f := Nat.mul_le_mul hb' hd'
      _ ≤ 2 ^ (e + f + 1) := by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)

lemma QB.neg {e : ℕ} {r : ℚ} (hr : QB e r) : QB e (-r) := by
  obtain ⟨a, b, hb, rfl, ha, hb'⟩ := hr
  exact ⟨-a, b, hb, by push_cast; ring, by simpa using ha, hb'⟩

lemma QB.sub {e f : ℕ} {r s : ℚ} (hr : QB e r) (hs : QB f s) : QB (e + f + 1) (r - s) := by
  rw [sub_eq_add_neg]; exact hr.add hs.neg

lemma QB.mul {e f : ℕ} {r s : ℚ} (hr : QB e r) (hs : QB f s) : QB (e + f) (r * s) := by
  obtain ⟨a, b, hb, rfl, ha, hb'⟩ := hr
  obtain ⟨c, d, hd, rfl, hc, hd'⟩ := hs
  refine ⟨a * c, b * d, Nat.mul_pos hb hd, by push_cast; ring, ?_, ?_⟩
  · rw [Int.natAbs_mul, pow_add]; exact Nat.mul_le_mul ha hc
  · rw [pow_add]; exact Nat.mul_le_mul hb' hd'

lemma QB_sum {α : Type*} {e : ℕ} (g : α → ℚ) :
    ∀ l : List α, (∀ x ∈ l, QB e (g x)) → QB (l.length * (e + 1)) (l.map g).sum := by
  intro l
  induction l with
  | nil => intro _; simpa using QB_zero
  | cons x l ih =>
    intro h
    have h1 := h x (by simp)
    have h2 := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    exact (h1.add h2).mono (by nlinarith)

lemma clog_le_of_le {n e : ℕ} (h : n ≤ 2 ^ e) : Nat.clog 2 (n + 1) ≤ e + 1 := by
  apply Nat.clog_le_of_le_pow
  have := Nat.one_le_two_pow (n := e)
  rw [pow_succ]; omega

lemma QB_of_bl (r : ℚ) : QB (bl r) r := by
  refine ⟨r.num, r.den, r.pos, (Rat.num_div_den r).symm, ?_, ?_⟩
  · have := Nat.le_pow_clog (b := 2) (by norm_num) (r.num.natAbs + 1)
    have h2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num)
      (show Nat.clog 2 (r.num.natAbs + 1) ≤ bl r by unfold bl; omega)
    omega
  · have := Nat.le_pow_clog (b := 2) (by norm_num) (r.den + 1)
    have h2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num)
      (show Nat.clog 2 (r.den + 1) ≤ bl r by unfold bl; omega)
    omega

lemma bl_le_of_QB {e : ℕ} {r : ℚ} (h : QB e r) : bl r ≤ 2 * e + 3 := by
  obtain ⟨a, b, hb, rfl, ha, hb'⟩ := h
  have hdiv : ((a : ℚ) / (b : ℚ)) = Rat.divInt a b := by
    rw [← Rat.intCast_div_eq_divInt]; push_cast; rfl
  have hnum : ((a : ℚ) / b).num.natAbs ≤ 2 ^ e := by
    rw [hdiv]
    rcases eq_or_ne a 0 with rfl | ha0
    · simp
    · exact le_trans (Nat.le_of_dvd (Int.natAbs_pos.mpr ha0)
        (Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd a (by exact_mod_cast hb.ne')))) ha
  have hden : ((a : ℚ) / b).den ≤ 2 ^ e := by
    rw [hdiv]
    have := Rat.den_dvd a b
    exact le_trans (Nat.le_of_dvd hb (by exact_mod_cast this)) hb'
  unfold bl
  have := clog_le_of_le hnum
  have := clog_le_of_le hden
  omega

/-! ## Local losses -/

/-- `ℓ_{J;u,v}` at the end values of an atom is the atom itself -/
lemma lineJ_atom (a : Atom) (x : ℚ) : lineJ a.k a.m a.lval a.rval x = a.evalQ x := by
  rw [lineJ, Atom.lval_eq, Atom.rval_eq, Atom.evalQ, Atom.x0]
  field_simp
  ring

lemma QB_of_ht {r : ℚ} {H : ℕ} (h : ht r ≤ H) : QB (Nat.clog 2 H) r := by
  have hH := Nat.le_pow_clog (b := 2) (by norm_num) H
  refine ⟨r.num, r.den, r.pos, (Rat.num_div_den r).symm, ?_, ?_⟩
  · exact le_trans (le_trans (le_max_left _ _) h) hH
  · exact le_trans (le_trans (le_max_right _ _) h) hH

/-- the value of an admissible atom at a sample abscissa of bit size `≤ B` -/
lemma QB_atom_eval {a : Atom} {H B : ℕ} (ha : a.height ≤ H) {x : ℚ} (hx : QB B x) :
    QB (B + 3 * Nat.clog 2 H + a.k + 3) (a.evalQ x) := by
  set h := Nat.clog 2 H
  have hy : QB h a.y0 := QB_of_ht (a.ht_y0_le_height.trans ha)
  have hs : QB h a.s := QB_of_ht (a.ht_s_le_height.trans ha)
  have hHp : H ≤ 2 ^ h := Nat.le_pow_clog (b := 2) (by norm_num) H
  have hm : a.m.natAbs + 1 ≤ H := a.m_lt_height.trans ha
  have hx0 : QB (h + a.k + 1) a.x0 := by
    refine ⟨2 * a.m + 1, 2 ^ (a.k + 1), by positivity, ?_, ?_, ?_⟩
    · rw [Atom.x0]; push_cast; field_simp; ring
    · calc (2 * a.m + 1).natAbs ≤ (2 * a.m).natAbs + (1 : ℤ).natAbs := Int.natAbs_add_le _ _
        _ = 2 * a.m.natAbs + 1 := by simp [Int.natAbs_mul]
        _ ≤ 2 * 2 ^ h := by omega
        _ ≤ 2 ^ (h + a.k + 1) := by
          rw [pow_succ, mul_comm]
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have := hy.add (hs.mul (hx.sub hx0))
  unfold Atom.evalQ
  exact this.mono (by omega)

/-- one term `ω (z - ℓ(x))²` of a local loss -/
lemma QB_term {a : Atom} {H B : ℕ} (ha : a.height ≤ H) {p : ℚ × ℚ × ℚ} (hx : QB B p.1)
    (hz : QB B p.2.1) (hw : QB B p.2.2) :
    QB (5 * B + 6 * Nat.clog 2 H + 2 * a.k + 8)
      (p.2.2 * (p.2.1 - lineJ a.k a.m a.lval a.rval p.1) ^ 2) := by
  rw [lineJ_atom, sq]
  have h1 := hz.sub (QB_atom_eval ha hx)
  have := hw.mul (h1.mul h1)
  exact this.mono (by omega)

/-! ## Disjointness of ownership -/

lemma sum_filter_length_le {α β : Type*} (data : List α) (P : β → α → Prop) [∀ b, DecidablePred (P b)] :
    ∀ L : List β, L.Pairwise (fun b c => ∀ x, ¬ (P b x ∧ P c x)) →
      (L.map fun b => (data.filter fun x => P b x).length).sum ≤ data.length := by
  intro L
  induction L generalizing data with
  | nil => intro _; simp
  | cons b L ih =>
    intro h
    rw [List.pairwise_cons] at h
    simp only [List.map_cons, List.sum_cons]
    have hrest : (L.map fun c => (data.filter fun x => P c x).length) =
        (L.map fun c => ((data.filter fun x => ¬ P b x).filter fun x => P c x).length) := by
      refine List.map_congr_left fun c hc => ?_
      rw [List.filter_filter]
      congr 1
      refine List.filter_congr fun x _ => ?_
      by_cases hc' : P c x
      · have : ¬ P b x := fun hb => h.1 c hc x ⟨hb, hc'⟩
        simp [hc', this]
      · simp [hc']
    rw [hrest]
    have := ih (data.filter fun x => ¬ P b x) h.2
    have hsplit : (data.filter fun x => P b x).length + (data.filter fun x => ¬ P b x).length =
        data.length := by
      have := List.length_eq_length_filter_add (l := data) (f := fun x => decide (P b x))
      simp only [decide_not] at this ⊢
      omega
    omega

lemma cR_eq_cast (k : ℕ) (m : ℤ) : cR k m = ((((m : ℚ) + 1) / 2 ^ k : ℚ) : ℝ) := by
  unfold cR; push_cast; ring

lemma cL_eq_cast (k : ℕ) (m : ℤ) : cL k m = ((((m : ℚ)) / 2 ^ k : ℚ) : ℝ) := by
  unfold cL; push_cast; ring

/-- the right end of a descendant cell is at most the right end `β` of `K` -/
lemma right_le_beta {k₀ k r : ℕ} {m₀ m : ℤ} (hd : IsDesc k₀ m₀ k m r) :
    ((m : ℚ) + 1) / 2 ^ k ≤ ((m₀ : ℚ) + 1) / 2 ^ k₀ := by
  obtain ⟨rfl, hm⟩ := hd
  have hpos : (0 : ℤ) < 2 ^ r := by positivity
  have h1 : m < 2 ^ r * (m₀ + 1) := by
    rw [← hm]
    have := Int.lt_ediv_add_one_mul_self m hpos
    linarith
  have h2 : (m : ℚ) + 1 ≤ 2 ^ r * ((m₀ : ℚ) + 1) := by exact_mod_cast (show m + 1 ≤ 2 ^ r * (m₀ + 1) by omega)
  rw [div_le_div_iff₀ (by positivity) (by positivity), pow_add]
  have : (0 : ℚ) < 2 ^ k₀ := by positivity
  nlinarith

namespace Setup

variable (S : Setup)

/-- two different leaves of a representation rooted at a descendant cell own disjoint sets of
abscissae -/
lemma leaves_owns_pairwise {k r : ℕ} {m : ℤ} (hd : IsDesc S.k₀ S.m₀ k m r) {R : LTree}
    (hR : WF k m R) :
    R.leaves.Pairwise (fun a b => ∀ x, ¬ (S.owns a.k a.m x ∧ S.owns b.k b.m x)) := by
  have hbefore : R.leaves.Pairwise (fun a b : Atom => ((a.m : ℚ) + 1) / 2 ^ a.k ≤ (b.m : ℚ) / 2 ^ b.k) := by
    have hlt : ∀ c : Atom, (c.m : ℚ) / 2 ^ c.k < ((c.m : ℚ) + 1) / 2 ^ c.k := fun c =>
      div_lt_div_of_pos_right (by linarith) (by positivity)
    haveI : Trans (fun a b : Atom => ((a.m : ℚ) + 1) / 2 ^ a.k ≤ (b.m : ℚ) / 2 ^ b.k)
        (fun a b : Atom => ((a.m : ℚ) + 1) / 2 ^ a.k ≤ (b.m : ℚ) / 2 ^ b.k)
        (fun a b : Atom => ((a.m : ℚ) + 1) / 2 ^ a.k ≤ (b.m : ℚ) / 2 ^ b.k) :=
      ⟨fun h1 h2 => h1.trans ((hlt _).le.trans h2)⟩
    rw [← List.isChain_iff_pairwise]
    refine (leaves_isChain hR).imp fun a b hab => ?_
    have := hab.1
    rw [cR_eq_cast, cL_eq_cast] at this
    exact (Rat.cast_injective this).le
  refine hbefore.imp_of_mem fun {a b} ha hb hab x ⟨hxa, hxb⟩ => ?_
  -- `b` lies inside `K`
  have hbK : ((b.m : ℚ) + 1) / 2 ^ b.k ≤ S.beta := by
    have hsub := leaves_cell_sub hR b hb
    have hmem : cR b.k b.m ∈ cellIcc k m := hsub (right_mem_Icc.mpr (cL_lt_cR _ _).le)
    have h1 : cR b.k b.m ≤ cR k m := hmem.2
    rw [cR_eq_cast, cR_eq_cast, Rat.cast_le] at h1
    exact h1.trans (right_le_beta hd)
  have hblt : (b.m : ℚ) / 2 ^ b.k < ((b.m : ℚ) + 1) / 2 ^ b.k :=
    div_lt_div_of_pos_right (by linarith) (by positivity)
  obtain ⟨hb1, -⟩ := hxb
  obtain ⟨-, hxa' | ⟨hβ, hxe⟩⟩ := hxa
  · linarith
  · linarith

/-- the losses of the leaves of a representation, as a single sum over owned observations -/
lemma sum_losses_eq (R : LTree) :
    (R.leaves.map fun a => S.loss a.k a.m a.lval a.rval).sum =
      ((R.leaves.flatMap fun a => (S.data.filter fun p => S.owns a.k a.m p.1).map fun p => (a, p)).map
        fun q => q.2.2.2 * (q.2.2.1 - lineJ q.1.k q.1.m q.1.lval q.1.rval q.2.1) ^ 2).sum := by
  induction R.leaves with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append, ih]
    congr 1
    unfold loss
    simp [List.map_map, Function.comp_def]

lemma numInternal_le_serRec : ∀ R : LTree, R.numInternal ≤ (serRec R).length := by
  intro R
  induction R with
  | leaf a => simp [numInternal]
  | node l r ihl ihr => simp only [numInternal, serRec, List.length_cons, List.length_append]; omega

/-- **Theorem 9.2 (cota grosseira de complexidade de bits)**, growth of the rational costs.
Let `B` bound the bit length `bl` of all abscissae, responses, weights and penalties, let
`P = |𝒵|` be the number of observations and `L` a bound on the stream lengths. Then every cost
`cost_𝒵(R)` occurring in the recursion — of a representation `R` rooted at a descendant `J` of
`K` within the depth budget, with atoms in `𝓛_H` and `|ser_rec(R)| ≤ L` — satisfies
`bl(cost_𝒵(R)) ≤ 2 (P (5B + 6⌈log₂H⌉ + 2(k₀+D) + 9) + 2B + 2⌈log₂L⌉ + 2) + 3`,
i.e. `bl = O(P (B_𝒵 + D + k₀ + log(2H)) + B_𝒵 + log(2L))`. -/
theorem bit_complexity {B L : ℕ}
    (hdata : ∀ p ∈ S.data, bl p.1 ≤ B ∧ bl p.2.1 ≤ B ∧ bl p.2.2 ≤ B) (hlb : bl S.lb ≤ B)
    (hls : bl S.ls ≤ B) {k r : ℕ} {m : ℤ} (hd : IsDesc S.k₀ S.m₀ k m r) {R : LTree}
    (hR : WF k m R) (hdep : r + R.depth ≤ S.D) (hh : R.maxHeight ≤ S.H) (hL : (serRec R).length ≤ L) :
    bl (S.costT R) ≤ 2 * (S.data.length * (5 * B + 6 * Nat.clog 2 S.H + 2 * (S.k₀ + S.D) + 9) +
      2 * B + 2 * Nat.clog 2 L + 2) + 3 := by
  classical
  set eT := 5 * B + 6 * Nat.clog 2 S.H + 2 * (S.k₀ + S.D) + 8
  -- the flattened list of (leaf, owned observation) pairs
  set Q := R.leaves.flatMap fun a => (S.data.filter fun p => S.owns a.k a.m p.1).map fun p => (a, p)
  have hQlen : Q.length ≤ S.data.length := by
    rw [List.length_flatMap]
    simp only [List.length_map]
    exact sum_filter_length_le S.data (fun (a : Atom) (p : ℚ × ℚ × ℚ) => S.owns a.k a.m p.1) R.leaves
      ((S.leaves_owns_pairwise hd hR).imp fun h (x : ℚ × ℚ × ℚ) => h x.1)
  have hterm : ∀ q ∈ Q, QB eT (q.2.2.2 * (q.2.2.1 - lineJ q.1.k q.1.m q.1.lval q.1.rval q.2.1) ^ 2) := by
    intro q hq
    simp only [Q, List.mem_flatMap, List.mem_map, List.mem_filter] at hq
    obtain ⟨a, ha, p, ⟨hp, -⟩, rfl⟩ := hq
    have hah : a.height ≤ S.H := le_trans (le_maxHeight ha) hh
    have hak : a.k ≤ S.k₀ + S.D := by
      have := WF_leaf_depth hR a ha; have := hd.1; omega
    obtain ⟨h1, h2, h3⟩ := hdata p hp
    exact (QB_term hah ((QB_of_bl _).mono h1) ((QB_of_bl _).mono h2) ((QB_of_bl _).mono h3)).mono
      (by omega)
  have hloss : QB (S.data.length * (eT + 1)) (R.leaves.map fun a => S.loss a.k a.m a.lval a.rval).sum := by
    rw [S.sum_losses_eq]
    exact (QB_sum _ Q hterm).mono (Nat.mul_le_mul_right _ hQlen)
  have hLp := Nat.le_pow_clog (b := 2) (by norm_num) L
  have hpen1 : QB (B + Nat.clog 2 L) (S.lb * (serRec R).length) :=
    ((QB_of_bl _).mono hlb).mul (QB_nat (hL.trans hLp))
  have hpen2 : QB (B + Nat.clog 2 L) (S.ls * R.numInternal) :=
    ((QB_of_bl _).mono hls).mul (QB_nat (((numInternal_le_serRec R).trans hL).trans hLp))
  have htot := (hloss.add hpen1).add hpen2
  have := bl_le_of_QB htot
  unfold costT
  refine this.trans ?_
  have : S.data.length * (eT + 1) = S.data.length * (5 * B + 6 * Nat.clog 2 S.H + 2 * (S.k₀ + S.D) + 9) := rfl
  omega

end Setup

end Artigo
