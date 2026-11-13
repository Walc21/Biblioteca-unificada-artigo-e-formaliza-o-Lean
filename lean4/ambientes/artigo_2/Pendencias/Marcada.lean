import RequestProject.Dyadic
import RequestProject.Coding
import RequestProject.JointBudget

/-!
# IV.5.1 (biblioteca marcada completa) e IV.5.3 (altura canônica de rede)

* `MAtom`: quádruplas `(k, m, y₀, s) ∈ ℕ × ℤ × ℚ × ℚ` (inclinação nula permitida), com o mesmo
  segmento `ℓ(x) = y₀ + s(x - x_{k,m})` e a mesma altura `max{2, k+1, |m|+1, ht y₀, ht s}`;
* `MTree`, `MWF`, `MTree.eval`: montagens contínuas marcadas `𝒜^□(J_{k,m})`;
  `MAsmNH N H`: a classe `𝒜^□_{N,H}([0,1])`;
* `Atom.toM`, `LTree.toM`: a inclusão `𝓛 ⊂ 𝓛^□` e `𝒜 ⊂ 𝒜^□`, `𝒜_{N,H} ⊂ 𝒜^□_{N,H}`;
* `canonShape S`: a árvore `𝒯(S)` (subdivide uma célula enquanto algum ponto de `S` está no
  interior); `canonShape_no_interior`: com profundidade suficiente nenhuma folha contém ponto de
  `S` no interior;
* `RedReLU`, `Hcan`: a altura canônica `H_can(R)` da eq. (canonical-network-height), igual à maior
  altura dos átomos da montagem canônica (`maxHeight_canonTree`).
-/

namespace Pendencias.Marcada

open Set Artigo

/-! ## IV.5.1 -/

/-- átomo marcado `(k, m, y₀, s)`, `s ∈ ℚ` qualquer -/
structure MAtom where
  k : ℕ
  m : ℤ
  y0 : ℚ
  s : ℚ
deriving DecidableEq

namespace MAtom

variable (a : MAtom)

/-- centro `x_{k,m} = (m + 1/2) 2^{-k}` -/
def x0 : ℚ := (a.m + 1 / 2) / 2 ^ a.k
def evalQ (x : ℚ) : ℚ := a.y0 + a.s * (x - a.x0)
noncomputable def eval (x : ℝ) : ℝ := (a.y0 : ℝ) + (a.s : ℝ) * (x - (a.x0 : ℝ))
def lval : ℚ := a.evalQ (a.m / 2 ^ a.k)
def rval : ℚ := a.evalQ ((a.m + 1) / 2 ^ a.k)
/-- mesma altura do átomo original -/
def height : ℕ := max (max (max (max 2 (a.k + 1)) (a.m.natAbs + 1)) (ht a.y0)) (ht a.s)

end MAtom

/-- `𝓛 ⊂ 𝓛^□` -/
def _root_.Artigo.Atom.toM (a : Atom) : MAtom := ⟨a.k, a.m, a.y0, a.s⟩

lemma Atom.toM_injective : Function.Injective Atom.toM := by
  rintro ⟨k, m, y, s, hs⟩ ⟨k', m', y', s', hs'⟩ h
  simp only [Atom.toM, MAtom.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

lemma Atom.toM_height (a : Atom) : a.toM.height = a.height := rfl

lemma Atom.toM_eval (a : Atom) (x : ℝ) : a.toM.eval x = a.eval x := rfl

lemma Atom.toM_lval (a : Atom) : a.toM.lval = a.lval := rfl

lemma Atom.toM_rval (a : Atom) : a.toM.rval = a.rval := rfl

/-- a marca guarda o suporte mesmo com `s = 0`: o átomo marcado é determinado pelas quatro
coordenadas, e com `s = 0` ele é a constante `y₀` -/
lemma MAtom.eval_of_s_zero (a : MAtom) (h : a.s = 0) (x : ℝ) : a.eval x = a.y0 := by
  simp [MAtom.eval, h]

/-- árvores com folhas marcadas -/
inductive MTree
  | leaf (a : MAtom)
  | node (l r : MTree)

namespace MTree

def leaves : MTree → List MAtom
  | leaf a => [a]
  | node l r => l.leaves ++ r.leaves

def numLeaves (T : MTree) : ℕ := T.leaves.length

/-- altura atômica máxima -/
def maxHeight : MTree → ℕ
  | leaf a => a.height
  | node l r => max l.maxHeight r.maxHeight

def lval : MTree → ℚ
  | leaf a => a.lval
  | node l _ => l.lval

def rval : MTree → ℚ
  | leaf a => a.rval
  | node _ r => r.rval

/-- boa formação em `J_{k,m}`: suportes nas células e continuidade nas fronteiras -/
def MWF : ℕ → ℤ → MTree → Prop
  | k, m, leaf a => a.k = k ∧ a.m = m
  | k, m, node l r => MWF (k + 1) (2 * m) l ∧ MWF (k + 1) (2 * m + 1) r ∧ l.rval = r.lval

noncomputable def eval : ℕ → ℤ → MTree → ℝ → ℝ
  | _, _, leaf a, x => a.eval x
  | k, m, node l r, x => if x < cL (k + 1) (2 * m + 1) then eval (k + 1) (2 * m) l x
      else eval (k + 1) (2 * m + 1) r x

lemma maxHeight_le_iff {T : MTree} {H : ℕ} : T.maxHeight ≤ H ↔ ∀ a ∈ T.leaves, a.height ≤ H := by
  induction T with
  | leaf a => simp [maxHeight, leaves]
  | node l r ihl ihr =>
      simp only [maxHeight, leaves, List.mem_append, max_le_iff, ihl, ihr]
      constructor
      · rintro ⟨h1, h2⟩ a (ha | ha); exacts [h1 a ha, h2 a ha]
      · intro h; exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩

end MTree

open MTree

/-- `𝒜^□(J_{k,m})` -/
def MAsm (k : ℕ) (m : ℤ) : Set (ℝ → ℝ) := {g | ∃ T, MWF k m T ∧ g = T.eval k m}

/-- `𝒜^□_{N,H}([0,1])` -/
def MAsmNH (N H : ℕ) : Set (ℝ → ℝ) :=
  {g | ∃ T, MWF 0 0 T ∧ T.numLeaves ≤ N ∧ T.maxHeight ≤ H ∧ g = T.eval 0 0}

/-- `LTree ↪ MTree` -/
def _root_.Artigo.LTree.toM : LTree → MTree
  | .leaf a => .leaf a.toM
  | .node l r => .node l.toM r.toM

lemma toM_leaves : ∀ T : LTree, T.toM.leaves = T.leaves.map Atom.toM
  | .leaf _ => rfl
  | .node l r => by simp [LTree.toM, MTree.leaves, LTree.leaves, toM_leaves l, toM_leaves r]

lemma toM_lval : ∀ T : LTree, T.toM.lval = T.lval
  | .leaf _ => rfl
  | .node l _ => toM_lval l

lemma toM_rval : ∀ T : LTree, T.toM.rval = T.rval
  | .leaf _ => rfl
  | .node _ r => toM_rval r

lemma toM_WF : ∀ {k : ℕ} {m : ℤ} {T : LTree}, LTree.WF k m T → MWF k m T.toM
  | _, _, .leaf _, h => h
  | _, _, .node _ _, h => ⟨toM_WF h.1, toM_WF h.2.1, by rw [toM_rval, toM_lval]; exact h.2.2⟩

lemma toM_eval : ∀ (k : ℕ) (m : ℤ) (T : LTree), T.toM.eval k m = T.eval k m
  | _, _, .leaf _ => rfl
  | k, m, .node l r => by
      funext x
      simp only [LTree.toM, MTree.eval, LTree.eval, toM_eval (k + 1) (2 * m) l,
        toM_eval (k + 1) (2 * m + 1) r]

/-- **Definição IV.5.1**, inclusões: `𝒜(J_{k,m}) ⊂ 𝒜^□(J_{k,m})` e
`𝒜_{N,H}([0,1]) ⊂ 𝒜^□_{N,H}([0,1])`. -/
theorem marked_extends (k : ℕ) (m : ℤ) (N H : ℕ) :
    LTree.Assemblies k m ⊆ MAsm k m ∧
    {g | ∃ T, AdmNH N H T ∧ g = T.eval 0 0} ⊆ MAsmNH N H := by
  constructor
  · rintro g ⟨T, hT, rfl⟩
    exact ⟨T.toM, toM_WF hT, (toM_eval k m T).symm⟩
  · rintro g ⟨T, ⟨hw, hn, hh⟩, rfl⟩
    refine ⟨T.toM, toM_WF hw, ?_, ?_, (toM_eval 0 0 T).symm⟩
    · simpa [MTree.numLeaves, toM_leaves, LTree.numLeaves] using hn
    · rw [MTree.maxHeight_le_iff, toM_leaves]
      simpa using LTree.maxHeight_le_iff.mp hh

/-! ## IV.5.3 -/

/-- um ponto cujo denominador divide `2^k` não está no interior de nenhuma célula de nível `k` -/
lemma not_interior_of_den_dvd {τ : ℚ} {k : ℕ} (h : τ.den ∣ 2 ^ k) (m : ℤ) :
    ¬ (cL k m < τ ∧ (τ : ℝ) < cR k m) := by
  rintro ⟨h1, h2⟩
  obtain ⟨q, hq⟩ := h
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hd : (0 : ℝ) < τ.den := by exact_mod_cast τ.den_pos
  have e : (τ : ℝ) * 2 ^ k = ((τ.num * q : ℤ) : ℝ) := by
    have h2k : (2 : ℝ) ^ k = (τ.den : ℝ) * q := by exact_mod_cast hq
    rw [Rat.cast_def, h2k]; push_cast; field_simp
  unfold cL at h1; unfold cR at h2
  rw [div_lt_iff₀ hpos, e] at h1
  rw [lt_div_iff₀ hpos, e] at h2
  have a1 : m < τ.num * q := by exact_mod_cast h1
  have a2 : τ.num * q < m + 1 := by exact_mod_cast h2
  omega

open Classical in
/-- `𝒯(S)` com profundidade relativa no máximo `d`, a partir de `J_{k,m}` -/
noncomputable def canonShape (S : Finset ℚ) : ℕ → ℕ → ℤ → DShape
  | 0, _, _ => DShape.leaf
  | d + 1, k, m =>
      if ∃ τ ∈ S, cL k m < τ ∧ (τ : ℝ) < cR k m then
        DShape.node (canonShape S d (k + 1) (2 * m)) (canonShape S d (k + 1) (2 * m + 1))
      else DShape.leaf

/-- células-folha de uma forma enraizada em `J_{k,m}` -/
def cellsOf : DShape → ℕ → ℤ → List (ℕ × ℤ)
  | .leaf, k, m => [(k, m)]
  | .node l r, k, m => cellsOf l (k + 1) (2 * m) ++ cellsOf r (k + 1) (2 * m + 1)

/-- folhas de `𝒯(S)` não contêm pontos de `S` no interior, desde que `d` cubra as profundidades -/
theorem canonShape_no_interior (S : Finset ℚ) :
    ∀ (d k : ℕ) (m : ℤ), (∀ τ ∈ S, τ.den ∣ 2 ^ (k + d)) →
      ∀ J ∈ cellsOf (canonShape S d k m) k m, ∀ τ ∈ S, ¬ (cL J.1 J.2 < τ ∧ (τ : ℝ) < cR J.1 J.2) := by
  intro d
  induction d with
  | zero =>
      intro k m hS J hJ τ hτ
      simp only [canonShape, cellsOf, List.mem_singleton] at hJ
      subst hJ
      exact not_interior_of_den_dvd (by simpa using hS τ hτ) m
  | succ d ih =>
      intro k m hS J hJ τ hτ
      unfold canonShape at hJ
      split_ifs at hJ with hex
      · simp only [cellsOf, List.mem_append] at hJ
        have hS' : ∀ τ ∈ S, τ.den ∣ 2 ^ (k + 1 + d) := fun τ hτ => by
          rw [show k + 1 + d = k + (d + 1) by omega]; exact hS τ hτ
        rcases hJ with hJ | hJ
        · exact ih (k + 1) (2 * m) hS' J hJ τ hτ
        · exact ih (k + 1) (2 * m + 1) hS' J hJ τ hτ
      · simp only [cellsOf, List.mem_singleton] at hJ
        subst hJ
        push_neg at hex
        exact fun h => absurd h.2 (not_lt.mpr (hex τ hτ h.1))

/-- forma ReLU reduzida com dados racionais: `R(x) = c + qx + ∑ a_j ρ(x - τ_j)` -/
structure RedReLU where
  c : ℚ
  q : ℚ
  data : List (ℚ × ℚ)   -- pares `(a_j, τ_j)`

namespace RedReLU

variable (R : RedReLU)

def evalQ (x : ℚ) : ℚ := R.c + R.q * x + (R.data.map fun p => p.1 * max 0 (x - p.2)).sum

/-- inclinação à direita de `x`: `σ = q + ∑_{τ_j ≤ x} a_j` -/
def slopeAt (x : ℚ) : ℚ := R.q + ((R.data.filter fun p => p.2 ≤ x).map Prod.fst).sum

/-- conjunto das quebras `S = {τ_j}` -/
def breaks : Finset ℚ := (R.data.map Prod.snd).toFinset

/-- profundidade diádica máxima das quebras -/
def depth : ℕ := R.breaks.sup fun τ => Nat.log 2 τ.den

/-- átomo marcado da montagem canônica na folha `J_{k,m}` -/
def atomAt (k : ℕ) (m : ℤ) : MAtom :=
  ⟨k, m, R.evalQ ((m + 1 / 2) / 2 ^ k), R.slopeAt (m / 2 ^ k)⟩

/-- montagem canônica sobre uma forma -/
def canonTree : DShape → ℕ → ℤ → MTree
  | .leaf, k, m => .leaf (R.atomAt k m)
  | .node l r, k, m => .node (canonTree l (k + 1) (2 * m)) (canonTree r (k + 1) (2 * m + 1))

/-- `max_{J_{k,m} ∈ leaf(T)} max{2, k+1, |m|+1, ht R(x_{k,m}), ht R'|_{J_{k,m}}}` -/
def hShape : DShape → ℕ → ℤ → ℕ
  | .leaf, k, m => max (max (max (max 2 (k + 1)) (m.natAbs + 1))
      (ht (R.evalQ ((m + 1 / 2) / 2 ^ k)))) (ht (R.slopeAt (m / 2 ^ k)))
  | .node l r, k, m => max (hShape l (k + 1) (2 * m)) (hShape r (k + 1) (2 * m + 1))

/-- **Definição IV.5.3 (altura canônica de rede)**: `H_can(R)` sobre `𝒯(S)`, `S` = quebras -/
noncomputable def Hcan : ℕ := R.hShape (canonShape R.breaks R.depth 0 0) 0 0

/-- `H_can(R)` é a maior altura dos átomos da montagem canônica -/
theorem maxHeight_canonTree :
    ∀ (T : DShape) (k : ℕ) (m : ℤ), (R.canonTree T k m).maxHeight = R.hShape T k m
  | .leaf, _, _ => rfl
  | .node l r, k, m => by
      simp only [canonTree, hShape, MTree.maxHeight, maxHeight_canonTree l, maxHeight_canonTree r]

theorem Hcan_eq_maxHeight :
    R.Hcan = (R.canonTree (canonShape R.breaks R.depth 0 0) 0 0).maxHeight :=
  (R.maxHeight_canonTree _ 0 0).symm

/-- com quebras diádicas (`τ_j ∈ 𝔻`), as folhas de `𝒯(S)` usadas em `H_can` não contêm quebras
no interior -/
theorem canon_leaves_free (hdy : ∀ τ ∈ R.breaks, IsDyadic τ) :
    ∀ J ∈ cellsOf (canonShape R.breaks R.depth 0 0) 0 0, ∀ τ ∈ R.breaks,
      ¬ (cL J.1 J.2 < τ ∧ (τ : ℝ) < cR J.1 J.2) := by
  refine canonShape_no_interior R.breaks R.depth 0 0 fun τ hτ => ?_
  obtain ⟨d, hd⟩ := hdy τ hτ
  have hle : Nat.log 2 τ.den ≤ R.depth := Finset.le_sup (f := fun τ => Nat.log 2 τ.den) hτ
  rw [hd, Nat.log_pow (by norm_num)] at hle
  rw [hd, zero_add]
  exact pow_dvd_pow 2 hle

end RedReLU

end Pendencias.Marcada
