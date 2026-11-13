import RequestProject.Serialization

/-!
# Section 3.6 — Finite catalogues, minimizers and truncation

* Proposition 3.17 (no minimizer over the infinite library),
* Definition 3.18 (truncated catalogue `𝔑_{D,H}(K)`, `Σ_{D,H}(K)`),
* Theorem 3.19 (finiteness, existence, canonical tie-break by the shortlex-least stream `ser♯`),
* Proposition 3.20 (consistency under truncation, stabilization of the canonical selector).
-/

namespace Artigo

open Set LTree

/-! ## Proposition 3.17 -/

lemma Atom.eval_rat (a : Atom) (x : ℚ) : a.eval (x : ℝ) = ((a.evalQ x : ℚ) : ℝ) := a.eval_eq x

/-- **Proposition 3.17**: for `x = 1/4` and `y = √2`, the infimum of `|y - ℓ_n(x)|` over atoms
whose cell contains `x` is `0`, but no atom attains it. -/
theorem no_minimizer :
    (⨅ a : {a : Atom // (1 / 4 : ℝ) ∈ cellIcc a.k a.m},
        |Real.sqrt 2 - a.1.eval (1 / 4)|) = 0 ∧
    ∀ a : Atom, 0 < |Real.sqrt 2 - a.eval (1 / 4)| := by
  have hrat : ∀ a : Atom, a.eval (1 / 4) ≠ Real.sqrt 2 := by
    intro a h
    have := a.eval_rat (1 / 4)
    push_cast at this
    rw [this] at h
    exact irrational_sqrt_two ⟨_, h⟩
  refine ⟨?_, fun a => abs_pos.mpr (sub_ne_zero.mpr (hrat a).symm)⟩
  -- the atom on `J_{2,1} = [1/4,1/2]` with slope 1 through `(1/4, q)`
  let at4 : ℚ → {a : Atom // (1 / 4 : ℝ) ∈ cellIcc a.k a.m} := fun q =>
    ⟨⟨2, 1, q + 1 / 8, 1, one_ne_zero⟩, by simp [cellIcc]; norm_num⟩
  have hval : ∀ q : ℚ, (at4 q).1.eval (1 / 4) = q := by
    intro q; simp [at4, Atom.eval, Atom.x0]; norm_num
  have hbdd : BddBelow (Set.range fun a : {a : Atom // (1 / 4 : ℝ) ∈ cellIcc a.k a.m} =>
      |Real.sqrt 2 - a.1.eval (1 / 4)|) := ⟨0, by rintro _ ⟨a, rfl⟩; exact abs_nonneg _⟩
  haveI : Nonempty {a : Atom // (1 / 4 : ℝ) ∈ cellIcc a.k a.m} := ⟨at4 0⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro η hη
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show Real.sqrt 2 - η < Real.sqrt 2 by linarith)
    refine (ciInf_le hbdd (at4 q)).trans ?_
    rw [hval, abs_of_nonneg (by linarith)]
    linarith
  · exact le_ciInf fun a => abs_nonneg _

/-! ## Definition 3.18: the truncated catalogue -/

/-- `T₀ = 1`, `T_{d+1} = 1 + T_d²`: number of ordered tree shapes of depth `≤ d` -/
def Tshape : ℕ → ℕ
  | 0 => 1
  | d + 1 => 1 + Tshape d ^ 2

/-- all labelled trees of relative depth `≤ D` whose atoms lie in `𝓛_H` (no support/continuity
constraint) -/
def allTrees (H : ℕ) : ℕ → Finset LTree
  | 0 => (LH H).image leaf
  | D + 1 => (LH H).image leaf ∪ ((allTrees H D) ×ˢ (allTrees H D)).image fun p => node p.1 p.2

lemma mem_allTrees {H : ℕ} : ∀ (D : ℕ) (T : LTree),
    T ∈ allTrees H D ↔ T.depth ≤ D ∧ ∀ a ∈ T.leaves, a.height ≤ H := by
  intro D
  induction D with
  | zero =>
    intro T
    cases T with
    | leaf a => simp [allTrees, depth, leaves, mem_LH]
    | node l r => simp [allTrees, depth]
  | succ D ih =>
    intro T
    cases T with
    | leaf a => simp [allTrees, depth, leaves, mem_LH]
    | node l r =>
      simp only [allTrees, Finset.mem_union, Finset.mem_image, Finset.mem_product, Prod.exists,
        node.injEq, depth, leaves, List.mem_append]
      constructor
      · rintro (⟨a, -, h⟩ | ⟨l', r', ⟨hl, hr⟩, rfl, rfl⟩)
        · cases h
        · rw [ih] at hl hr
          refine ⟨by omega, fun a ha => ha.elim (hl.2 a) (hr.2 a)⟩
      · rintro ⟨hd, ha⟩
        right
        exact ⟨l, r, ⟨(ih l).mpr ⟨by omega, fun a h => ha a (Or.inl h)⟩,
          (ih r).mpr ⟨by omega, fun a h => ha a (Or.inr h)⟩⟩, rfl, rfl⟩

open Classical in
/-- the represented catalogue `𝔑_{D,H}(K)` for `K = J_{k,m}`: well-formed trees of relative depth
`≤ D` with maximal atomic height `≤ H` -/
noncomputable def RepCat (H D k : ℕ) (m : ℤ) : Finset LTree := (allTrees H D).filter (WF k m)

lemma mem_RepCat {H D k : ℕ} {m : ℤ} {T : LTree} :
    T ∈ RepCat H D k m ↔ WF k m T ∧ T.depth ≤ D ∧ T.maxHeight ≤ H := by
  classical
  unfold RepCat
  rw [Finset.mem_filter, mem_allTrees, maxHeight_le_iff]
  tauto

/-- the evaluation of a representation, as a function on `K` -/
noncomputable def evalK (k : ℕ) (m : ℤ) (T : LTree) : cellIcc k m → ℝ :=
  (cellIcc k m).restrict (T.eval k m)

open Classical in
/-- the catalogue `Σ_{D,H}(K) = Eval(𝔑_{D,H}(K))` of functions on `K` -/
noncomputable def SigmaCat (H D k : ℕ) (m : ℤ) : Finset (cellIcc k m → ℝ) :=
  (RepCat H D k m).image (evalK k m)

/-- `H_K = max {2, k₀+1, |m₀|+1}` -/
def HK (k : ℕ) (m : ℤ) : ℕ := max (max 2 (k + 1)) (m.natAbs + 1)

/-! ## The canonical stream `ser♯` and the shortlex order -/

/-- pre-order skeleton: `0` for an internal node, `1` for a leaf -/
def skel : LTree → List Bool
  | leaf _ => [true]
  | node l r => false :: (skel l ++ skel r)

/-- `ser♯(R)`: skeleton followed by `γ(n♯(J)+1)` for the leaves in spatial order -/
def serSharp (T : LTree) : List Bool :=
  skel T ++ gammaCodec.encList (T.leaves.map fun a => nSharp a + 1)

lemma skel_append_inj : ∀ (T T' : LTree) (s s' : List Bool), skel T ++ s = skel T' ++ s' →
    skel T = skel T' ∧ s = s' := by
  intro T
  induction T with
  | leaf a =>
    intro T' s s' h
    cases T' with
    | leaf b => simp [skel] at h ⊢; exact h
    | node l r => simp [skel] at h
  | node l r ihl ihr =>
    intro T' s s' h
    cases T' with
    | leaf b => simp [skel] at h
    | node l' r' =>
      simp only [skel, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h ⊢
      obtain ⟨h1, h2⟩ := ihl l' _ _ h
      obtain ⟨h3, h4⟩ := ihr r' _ _ h2
      exact ⟨by rw [h1, h3], h4⟩

lemma count_skel (T : LTree) : (skel T).count true = T.numLeaves := by
  induction T with
  | leaf a => simp [skel, numLeaves, leaves]
  | node l r ihl ihr => simp [skel, List.count_append, ihl, ihr, numLeaves_node]

lemma eq_of_skel_leaves : ∀ (T T' : LTree), skel T = skel T' → T.leaves = T'.leaves → T = T' := by
  intro T
  induction T with
  | leaf a =>
    intro T' h hl
    cases T' with
    | leaf b => simp [leaves] at hl; rw [hl]
    | node l r => simp [skel] at h
  | node l r ihl ihr =>
    intro T' h hl
    cases T' with
    | leaf b => simp [skel] at h
    | node l' r' =>
      simp only [skel, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := skel_append_inj l l' _ _ h
      have hlen : l.leaves.length = l'.leaves.length := by
        have := count_skel l; have := count_skel l'; simp only [numLeaves] at *; rw [← h1] at *; omega
      simp only [leaves] at hl
      obtain ⟨hl1, hl2⟩ := List.append_inj hl hlen
      rw [ihl l' h1 hl1, ihr r' h2 hl2]

/-- `ser♯` is injective on representations -/
theorem serSharp_injective : Function.Injective serSharp := by
  intro T T' h
  unfold serSharp at h
  obtain ⟨h1, h2⟩ := skel_append_inj T T' _ _ h
  have hn : T.leaves.length = T'.leaves.length := by
    have := count_skel T; have := count_skel T'; simp only [numLeaves] at *; rw [← h1] at *; omega
  have hd := gammaCodec_RT.decN (T.leaves.map fun a => nSharp a + 1) (by simp) []
  have hd' := gammaCodec_RT.decN (T'.leaves.map fun a => nSharp a + 1) (by simp) []
  rw [List.length_map, h2, hn] at hd
  rw [List.length_map] at hd'
  rw [hd'] at hd
  have hmap : T'.leaves.map (fun a => nSharp a + 1) = T.leaves.map (fun a => nSharp a + 1) := by
    simpa using hd
  have hinj : Function.Injective (fun a : Atom => nSharp a + 1) :=
    fun a b hab => nSharp_injective (by simpa using hab)
  exact eq_of_skel_leaves T T' h1 ((List.map_injective_iff.mpr hinj) hmap).symm

/-- shortlex rank of a binary word: `2^{|u|} + bin(u)`.  Comparing ranks is exactly the shortlex
order: first by length, then lexicographically (most significant bit first) -/
def slRank (u : List Bool) : ℕ := 2 ^ u.length + ofBits u

lemma ofBits_inj : ∀ (u v : List Bool), u.length = v.length → ofBits u = ofBits v → u = v := by
  intro u
  induction u with
  | nil => intro v h _; cases v <;> simp_all
  | cons b u ih =>
    intro v h hv
    cases v with
    | nil => simp at h
    | cons c v =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [ofBits] at hv
      have hu := ofBits_lt u
      have hv' := ofBits_lt v
      rw [h] at hu hv
      have hbc : b = c := by
        cases b <;> cases c
        · rfl
        · simp only [Bool.false_eq_true, if_false, if_true, zero_add] at hv; omega
        · simp only [Bool.false_eq_true, if_false, if_true, zero_add] at hv; omega
        · rfl
      subst hbc
      have : ofBits u = ofBits v := by omega
      rw [ih v h this]

lemma slRank_lt_iff (u v : List Bool) :
    slRank u < slRank v ↔ u.length < v.length ∨ (u.length = v.length ∧ ofBits u < ofBits v) := by
  unfold slRank
  have hu := ofBits_lt u
  have hv := ofBits_lt v
  constructor
  · intro h
    rcases lt_trichotomy u.length v.length with hl | hl | hl
    · exact Or.inl hl
    · right; rw [hl] at h ⊢; exact ⟨rfl, by omega⟩
    · exfalso
      have : 2 ^ (v.length + 1) ≤ 2 ^ u.length := Nat.pow_le_pow_right (by norm_num) hl
      rw [pow_succ] at this; omega
  · rintro (hl | ⟨hl, hb⟩)
    · have : 2 ^ (u.length + 1) ≤ 2 ^ v.length := Nat.pow_le_pow_right (by norm_num) hl
      rw [pow_succ] at this; omega
    · rw [hl]; omega

lemma slRank_injective : Function.Injective slRank := by
  intro u v h
  have hlen : u.length = v.length := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · exact absurd h ((slRank_lt_iff u v).mpr (Or.inl hl)).ne
    · exact absurd h.symm ((slRank_lt_iff v u).mpr (Or.inl hl)).ne
  unfold slRank at h
  rw [hlen] at h
  exact ofBits_inj u v hlen (by omega)

/-- the canonical key of a representation: the shortlex rank of `ser♯` -/
def canKey (T : LTree) : ℕ := slRank (serSharp T)

lemma canKey_injective : Function.Injective canKey := slRank_injective.comp serSharp_injective

/-! ## Theorem 3.19 -/

lemma card_allTrees_le (H : ℕ) : ∀ D : ℕ,
    (allTrees H D).card ≤ Tshape D * (LH H).card ^ 2 ^ D := by
  intro D
  induction D with
  | zero => simpa [allTrees, Tshape] using Finset.card_image_le
  | succ D ih =>
    set L := (LH H).card
    simp only [allTrees, Tshape]
    have h1 : L ≤ L ^ 2 ^ (D + 1) := Nat.le_self_pow (by positivity) L
    calc _ ≤ ((LH H).image leaf).card + (((allTrees H D) ×ˢ (allTrees H D)).image
          fun p => node p.1 p.2).card := Finset.card_union_le _ _
      _ ≤ L + (allTrees H D).card * (allTrees H D).card := by
          gcongr
          · exact Finset.card_image_le
          · exact Finset.card_image_le.trans (by rw [Finset.card_product])
      _ ≤ L + (Tshape D * L ^ 2 ^ D) * (Tshape D * L ^ 2 ^ D) := by gcongr
      _ = L + Tshape D ^ 2 * L ^ 2 ^ (D + 1) := by rw [pow_succ 2 D, pow_mul]; ring
      _ ≤ L ^ 2 ^ (D + 1) + Tshape D ^ 2 * L ^ 2 ^ (D + 1) := by gcongr
      _ = _ := by ring

/-- the root leaf `⟨k, m, 0, 1⟩` belongs to every catalogue with `H ≥ H_K` -/
lemma rootLeaf_mem {H D k : ℕ} {m : ℤ} (hH : HK k m ≤ H) :
    leaf ⟨k, m, 0, 1, one_ne_zero⟩ ∈ RepCat H D k m := by
  rw [mem_RepCat]
  refine ⟨⟨rfl, rfl⟩, by simp [depth], ?_⟩
  rw [maxHeight_le_iff]
  intro a ha
  simp only [leaves, List.mem_singleton] at ha
  subst ha
  rw [Atom.height_le_iff]
  dsimp only
  simp only [HK] at hH
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · simp [ht]; omega
  · simp [ht]; omega

/-- the minimizers of `J ∘ Eval` in the represented catalogue -/
noncomputable def minSet (H D k : ℕ) (m : ℤ) (J : (cellIcc k m → ℝ) → ℝ) : Finset LTree := by
  classical
  exact (RepCat H D k m).filter fun R => ∀ R' ∈ RepCat H D k m, J (evalK k m R) ≤ J (evalK k m R')

lemma mem_minSet {H D k : ℕ} {m : ℤ} {J : (cellIcc k m → ℝ) → ℝ} {R : LTree} :
    R ∈ minSet H D k m J ↔
      R ∈ RepCat H D k m ∧ ∀ R' ∈ RepCat H D k m, J (evalK k m R) ≤ J (evalK k m R') := by
  classical
  unfold minSet; rw [Finset.mem_filter]

lemma minSet_nonempty {H D k : ℕ} {m : ℤ} (hH : HK k m ≤ H) (J : (cellIcc k m → ℝ) → ℝ) :
    (minSet H D k m J).Nonempty := by
  have hne : (RepCat H D k m).Nonempty := ⟨_, rootLeaf_mem hH⟩
  obtain ⟨R, hR, hmin⟩ := (RepCat H D k m).exists_min_image (fun R => J (evalK k m R)) hne
  exact ⟨R, mem_minSet.mpr ⟨hR, hmin⟩⟩

open Classical in
/-- the canonical selector: the minimizer whose `ser♯` stream is shortlex-least -/
noncomputable def canon (H D k : ℕ) (m : ℤ) (J : (cellIcc k m → ℝ) → ℝ) : LTree :=
  if h : (minSet H D k m J).Nonempty then
    Classical.choose ((minSet H D k m J).exists_min_image canKey h)
  else leaf ⟨k, m, 0, 1, one_ne_zero⟩

lemma canon_spec {H D k : ℕ} {m : ℤ} (hH : HK k m ≤ H) (J : (cellIcc k m → ℝ) → ℝ) :
    canon H D k m J ∈ minSet H D k m J ∧
      ∀ R ∈ minSet H D k m J, canKey (canon H D k m J) ≤ canKey R := by
  have h := minSet_nonempty (D := D) hH J
  unfold canon
  rw [dif_pos h]
  exact Classical.choose_spec ((minSet H D k m J).exists_min_image canKey h)

lemma canon_unique {H D k : ℕ} {m : ℤ} (hH : HK k m ≤ H) (J : (cellIcc k m → ℝ) → ℝ) {R : LTree}
    (hR : R ∈ minSet H D k m J) (hmin : ∀ R' ∈ minSet H D k m J, canKey R ≤ canKey R') :
    R = canon H D k m J := by
  obtain ⟨h1, h2⟩ := canon_spec (D := D) hH J
  exact canKey_injective (le_antisymm (hmin _ h1) (h2 _ hR))

/-- **Theorem 3.19 (finitude, existência e desempate canônico)**.  For `H ≥ H_K`:
`1 ≤ |Σ_{D,H}(K)| ≤ |𝔑_{D,H}(K)| ≤ T_D |𝓛_H|^{2^D}`; every functional `J` on `Σ_{D,H}(K)` attains
its minimum; and among all minimizing representations exactly one has the shortlex-least stream
`ser♯` (hence a unique canonical function and representation). -/
theorem finite_catalog_minimizer {H D k : ℕ} {m : ℤ} (hH : HK k m ≤ H) :
    1 ≤ (SigmaCat H D k m).card ∧ (SigmaCat H D k m).card ≤ (RepCat H D k m).card ∧
    (RepCat H D k m).card ≤ Tshape D * (LH H).card ^ 2 ^ D ∧
    (∀ J : (cellIcc k m → ℝ) → ℝ, ∃ g ∈ SigmaCat H D k m, ∀ g' ∈ SigmaCat H D k m, J g ≤ J g') ∧
    (∀ J : (cellIcc k m → ℝ) → ℝ, ∃! R, R ∈ minSet H D k m J ∧
      ∀ R' ∈ minSet H D k m J, canKey R ≤ canKey R') := by
  classical
  have hne : (RepCat H D k m).Nonempty := ⟨_, rootLeaf_mem hH⟩
  refine ⟨?_, Finset.card_image_le, ?_, fun J => ?_, fun J => ?_⟩
  · exact Finset.card_pos.mpr (hne.image _)
  · exact (Finset.card_filter_le _ _).trans (card_allTrees_le H D)
  · exact (SigmaCat H D k m).exists_min_image J (hne.image _)
  · refine ⟨canon H D k m J, canon_spec hH J, fun R hR => canon_unique hH J hR.1 hR.2⟩

/-! ## Proposition 3.20 -/

lemma RepCat_mono {H H' D D' k : ℕ} {m : ℤ} (hD : D ≤ D') (hH : H ≤ H') :
    RepCat H D k m ⊆ RepCat H' D' k m := by
  intro R hR
  rw [mem_RepCat] at hR ⊢
  exact ⟨hR.1, hR.2.1.trans hD, hR.2.2.trans hH⟩

/-- the minimal value `min_{g ∈ Σ_{D,H}(K)} J(g)` -/
noncomputable def minVal (H D k : ℕ) (m : ℤ) (J : (cellIcc k m → ℝ) → ℝ) : ℝ :=
  sInf (J '' (SigmaCat H D k m : Set (cellIcc k m → ℝ)))

/-- **Proposition 3.20 (consistência sob truncagem)**.
(i) `Σ_{D,H}(K) ⊆ Σ_{D',H'}(K)` for `D ≤ D'`, `H ≤ H'`; (ii) hence the minimal values are
non-increasing; (iii) if `J` has a global minimizer on the union of all catalogues, then the
canonical selector stabilizes: there are truncation levels beyond which it always returns the
shortlex-least representation `R⋆` among all representations of global minimizers. -/
theorem catalog_consistency {k : ℕ} {m : ℤ} :
    (∀ {H H' D D' : ℕ}, D ≤ D' → H ≤ H' → SigmaCat H D k m ⊆ SigmaCat H' D' k m) ∧
    (∀ {H H' D D' : ℕ}, HK k m ≤ H → D ≤ D' → H ≤ H' → ∀ J : (cellIcc k m → ℝ) → ℝ,
      minVal H' D' k m J ≤ minVal H D k m J) ∧
    (∀ J : (cellIcc k m → ℝ) → ℝ,
      (∃ H D, ∃ g ∈ SigmaCat H D k m, ∀ H' D', ∀ g' ∈ SigmaCat H' D' k m, J g ≤ J g') →
      ∃ (Rs : LTree) (H₀ D₀ : ℕ), ∀ H D, H₀ ≤ H → D₀ ≤ D → canon H D k m J = Rs) := by
  classical
  refine ⟨fun hD hH => Finset.image_subset_image (RepCat_mono hD hH), ?_, ?_⟩
  · intro H H' D D' hH hD hHH' J
    unfold minVal
    apply csInf_le_csInf
    · exact ((SigmaCat H' D' k m).finite_toSet.image J).bddBelow
    · exact ⟨_, ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (rootLeaf_mem hH)), rfl⟩⟩
    · exact Set.image_mono (Finset.coe_subset.mpr (Finset.image_subset_image (RepCat_mono hD hHH')))
  · rintro J ⟨H₁, D₁, g, hg, hmin⟩
    obtain ⟨R₁, hR₁, rfl⟩ := Finset.mem_image.mp hg
    -- representations of global minimizers
    let G : LTree → Prop := fun R => WF k m R ∧
      ∀ H' D', ∀ g' ∈ SigmaCat H' D' k m, J (evalK k m R) ≤ J g'
    have hG : ∃ n, ∃ R, G R ∧ canKey R = n := ⟨_, R₁, ⟨(mem_RepCat.mp hR₁).1, hmin⟩, rfl⟩
    set n₀ := Nat.find hG
    obtain ⟨Rs, hRs, hkey⟩ := Nat.find_spec hG
    have hleast : ∀ R, G R → canKey Rs ≤ canKey R := fun R hR => by
      rw [hkey]; exact Nat.find_min' hG ⟨R, hR, rfl⟩
    refine ⟨Rs, max Rs.maxHeight (HK k m), Rs.depth, fun H D hH hD => ?_⟩
    have hHK : HK k m ≤ H := le_trans (le_max_right _ _) hH
    have hRsmem : Rs ∈ RepCat H D k m :=
      mem_RepCat.mpr ⟨hRs.1, hD, le_trans (le_max_left _ _) hH⟩
    have hRsmin : Rs ∈ minSet H D k m J :=
      mem_minSet.mpr ⟨hRsmem, fun R' hR' => hRs.2 H D _ (Finset.mem_image_of_mem _ hR')⟩
    refine (canon_unique hHK J hRsmin fun R' hR' => hleast R' ⟨(mem_RepCat.mp (mem_minSet.mp hR').1).1,
      fun H' D' g' hg' => ?_⟩).symm
    exact (mem_minSet.mp hR').2 Rs hRsmem |>.trans (hRs.2 H' D' g' hg')

end Artigo
