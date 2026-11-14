import Pendencias.ReversaoQuantizada
import Mathlib

/-!
# IV.5.6 — redes profundas medidas pela função realizada (`map:artigo_3:5.6`)

Teorema final: `Pendencias.Marcada.DeepIV56.deep_functional_reverse`.

Formalização:
* `NetFun`/`IsReLUNetwork`: redes ReLU univariadas feedforward arbitrárias (camadas afins e ReLU
  alternadas, qualquer profundidade e largura);
* `FinPL`/`IsPL`: funções contínuas lineares por partes com finitas quebras; toda função de rede
  é `IsPL` (`IsReLUNetwork.isPL`), por fecho sob combinações afins, e sob `max 0 ·`
  (`IsPL.relu`, via colagem `FinPL.glue` e remoção da última quebra `FinPL.peel`);
* `reduced_of_PL`: forma hinge reduzida real em `[0,1]` (quebras estritamente crescentes em
  `(0,1)`, saltos não nulos), a mesma forma `RealReLU` de IV.5.2/IV.5.5;
* `regionCount F = R(F)`: menor número de peças afins em `[0,1]` (regiões afins máximas);
  `regionCount_eq` prova `R(F) = M + 1`;
* `sigma_abs_le`: as inclinações locais são limitadas pela constante de Lipschitz, daí
  `|c| ≤ B`, `|q| ≤ L`, `|a_j| ≤ 2L`, todos `≤ W = 2 max{1,B,L}`;
* o enunciado final aplica `QuantIV55.quantized_approximate_reverse` com esses `M` e `W`.
-/

/-!
# IV.5.6 — parte 1: funções contínuas lineares por partes (`FinPL`)

`FinPL g S`: `g` é contínua e afim em todo intervalo fechado `[a,b]` cujo interior não contém
ponto de `S` (conjunto finito de "quebras permitidas").
-/

namespace Pendencias.Marcada

open Set

namespace DeepIV56

/-- `g` contínua e afim em todo `[a,b]` com `Ioo a b` livre de `S`. -/
def FinPL (g : ℝ → ℝ) (S : Finset ℝ) : Prop :=
  Continuous g ∧ ∀ a b : ℝ, a < b → (∀ s ∈ S, s ∉ Ioo a b) →
    ∃ α β : ℝ, ∀ x ∈ Icc a b, g x = α + β * x

/-- `g` é contínua linear por partes com conjunto finito de quebras. -/
def IsPL (g : ℝ → ℝ) : Prop := ∃ S : Finset ℝ, FinPL g S

lemma line_unique {α β α' β' u v : ℝ} (huv : u < v) (hu : α + β * u = α' + β' * u)
    (hv : α + β * v = α' + β' * v) : α = α' ∧ β = β' := by
  have hβ : β = β' := by
    have : (β - β') * (v - u) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h (by linarith)
  refine ⟨?_, hβ⟩
  subst hβ; nlinarith

lemma FinPL.mono {g : ℝ → ℝ} {S T : Finset ℝ} (h : FinPL g S) (hST : S ⊆ T) : FinPL g T :=
  ⟨h.1, fun a b hab hT => h.2 a b hab fun s hs => hT s (hST hs)⟩

lemma FinPL.const (c : ℝ) : FinPL (fun _ => c) ∅ :=
  ⟨continuous_const, fun _ _ _ _ => ⟨c, 0, fun x _ => by simp⟩⟩

lemma FinPL.id : FinPL (fun x => x) ∅ :=
  ⟨continuous_id, fun _ _ _ _ => ⟨0, 1, fun x _ => by simp⟩⟩

lemma FinPL.add {g h : ℝ → ℝ} {S T : Finset ℝ} (hg : FinPL g S) (hh : FinPL h T) :
    FinPL (fun x => g x + h x) (S ∪ T) := by
  refine ⟨hg.1.add hh.1, fun a b hab hfree => ?_⟩
  obtain ⟨α, β, hab1⟩ := hg.2 a b hab fun s hs => hfree s (Finset.mem_union_left _ hs)
  obtain ⟨α', β', hab2⟩ := hh.2 a b hab fun s hs => hfree s (Finset.mem_union_right _ hs)
  exact ⟨α + α', β + β', fun x hx => by show g x + h x = _; rw [hab1 x hx, hab2 x hx]; ring⟩

lemma FinPL.smul {g : ℝ → ℝ} {S : Finset ℝ} (hg : FinPL g S) (k : ℝ) :
    FinPL (fun x => k * g x) S := by
  refine ⟨continuous_const.mul hg.1, fun a b hab hfree => ?_⟩
  obtain ⟨α, β, h⟩ := hg.2 a b hab hfree
  exact ⟨k * α, k * β, fun x hx => by show k * g x = _; rw [h x hx]; ring⟩

lemma IsPL.add {g h : ℝ → ℝ} (hg : IsPL g) (hh : IsPL h) : IsPL (fun x => g x + h x) := by
  obtain ⟨S, hS⟩ := hg; obtain ⟨T, hT⟩ := hh; exact ⟨_, hS.add hT⟩

lemma IsPL.smul {g : ℝ → ℝ} (hg : IsPL g) (k : ℝ) : IsPL (fun x => k * g x) := by
  obtain ⟨S, hS⟩ := hg; exact ⟨_, hS.smul k⟩

lemma IsPL.const (c : ℝ) : IsPL (fun _ => c) := ⟨_, FinPL.const c⟩

lemma IsPL.id : IsPL (fun x => x) := ⟨_, FinPL.id⟩

lemma IsPL.sum {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℝ) (h : ∀ i ∈ s, IsPL (g i)) :
    IsPL (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsPL.const 0
  | insert a s ha ih =>
      have h1 := h a (Finset.mem_insert_self _ _)
      have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      simpa [Finset.sum_insert ha] using h1.add h2

/-- se `S = ∅`, `g` é globalmente afim -/
lemma FinPL.global_affine {g : ℝ → ℝ} (h : FinPL g ∅) : ∃ α β : ℝ, ∀ x, g x = α + β * x := by
  obtain ⟨α, β, h0⟩ := h.2 0 1 zero_lt_one (by simp)
  refine ⟨α, β, fun x => ?_⟩
  obtain ⟨α', β', h1⟩ := h.2 (min 0 x - 1) (max 1 x + 1) (by
    have := min_le_left 0 x; have := le_max_left 1 x; linarith) (by simp)
  have e0 := h1 0 ⟨by have := min_le_left 0 x; linarith, by have := le_max_left 1 x; linarith⟩
  have e1 := h1 1 ⟨by have := min_le_left 0 x; linarith, by have := le_max_left 1 x; linarith⟩
  have f0 := h0 0 ⟨le_rfl, zero_le_one⟩
  have f1 := h0 1 ⟨zero_le_one, le_rfl⟩
  obtain ⟨ha, hb⟩ := line_unique (α := α) (β := β) (α' := α') (β' := β') zero_lt_one
    (by linarith) (by linarith)
  have := h1 x ⟨by have := min_le_right 0 x; linarith, by have := le_max_right 1 x; linarith⟩
  rw [this, ha, hb]

end DeepIV56

end Pendencias.Marcada

/-!
# IV.5.6 — parte 2: colagem, remoção da última quebra, fecho por ReLU e forma hinge
-/

namespace Pendencias.Marcada

open Set

namespace DeepIV56

lemma FinPL.glue {p q : ℝ → ℝ} {Sp Sq : Finset ℝ} {s : ℝ} (hp : FinPL p Sp) (hq : FinPL q Sq)
    (hs : p s = q s) :
    FinPL (fun x => if x ≤ s then p x else q x) (insert s (Sp ∪ Sq)) := by
  refine ⟨?_, fun a b hab hfree => ?_⟩
  · exact Continuous.if_le (f := fun x : ℝ => x) (g := fun _ : ℝ => s) hp.1 hq.1 continuous_id
      continuous_const (fun x hx => by simp only at hx; subst hx; exact hs)
  · have hsn : s ∉ Ioo a b := hfree s (Finset.mem_insert_self _ _)
    have hfp : ∀ t ∈ Sp, t ∉ Ioo a b := fun t ht =>
      hfree t (Finset.mem_insert_of_mem (Finset.mem_union_left _ ht))
    have hfq : ∀ t ∈ Sq, t ∉ Ioo a b := fun t ht =>
      hfree t (Finset.mem_insert_of_mem (Finset.mem_union_right _ ht))
    have : b ≤ s ∨ s ≤ a := by
      by_contra h; push_neg at h; exact hsn ⟨h.2, h.1⟩
    rcases this with h | h
    · obtain ⟨α, β, hab'⟩ := hp.2 a b hab hfp
      refine ⟨α, β, fun x hx => ?_⟩
      show (if x ≤ s then p x else q x) = _
      rw [if_pos (hx.2.trans h)]; exact hab' x hx
    · obtain ⟨α, β, hab'⟩ := hq.2 a b hab hfq
      refine ⟨α, β, fun x hx => ?_⟩
      show (if x ≤ s then p x else q x) = _
      by_cases hxs : x ≤ s
      · have : x = s := le_antisymm hxs (h.trans hx.1)
        subst this
        rw [if_pos le_rfl, hs]; exact hab' _ hx
      · rw [if_neg hxs]; exact hab' x hx

lemma exists_left_gap (S : Finset ℝ) (s : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ S, t ∉ Ioo (s - δ) s := by
  classical
  by_cases hT : (S.filter (· < s)).Nonempty
  · refine ⟨s - (S.filter (· < s)).max' hT, ?_, fun t ht hmem => ?_⟩
    · have := (Finset.mem_filter.mp ((S.filter (· < s)).max'_mem hT)).2; linarith
    · have hts : t ∈ S.filter (· < s) := Finset.mem_filter.mpr ⟨ht, hmem.2⟩
      have := (S.filter (· < s)).le_max' t hts
      linarith [hmem.1]
  · refine ⟨1, one_pos, fun t ht hmem => hT ⟨t, Finset.mem_filter.mpr ⟨ht, hmem.2⟩⟩⟩

lemma FinPL.peel {g : ℝ → ℝ} {S : Finset ℝ} (hg : FinPL g S) (hS : S.Nonempty) :
    ∃ a α β : ℝ, FinPL (fun x => g x - a * max 0 (x - S.max' hS)) (S.erase (S.max' hS)) ∧
      ∀ x, S.max' hS ≤ x → g x = α + β * x := by
  set s := S.max' hS with hsdef
  have hle : ∀ t ∈ S, t ≤ s := fun t ht => S.le_max' t ht
  -- parte direita
  obtain ⟨αr, βr, hr⟩ := hg.2 s (s + 1) (by linarith) (fun t ht hmem => by
    have := hle t ht; linarith [hmem.1])
  have hrall : ∀ x, s ≤ x → g x = αr + βr * x := by
    intro x hx
    obtain ⟨α', β', h1⟩ := hg.2 s (max (s + 1) x) (by have := le_max_left (s + 1) x; linarith)
      (fun t ht hmem => by have := hle t ht; linarith [hmem.1])
    have e0 := h1 s ⟨le_rfl, by have := le_max_left (s + 1) x; linarith⟩
    have e1 := h1 (s + 1) ⟨by linarith, le_max_left _ _⟩
    have f0 := hr s ⟨le_rfl, by linarith⟩
    have f1 := hr (s + 1) ⟨by linarith, le_rfl⟩
    obtain ⟨ha, hb⟩ := line_unique (α := αr) (β := βr) (α' := α') (β' := β')
      (u := s) (v := s + 1) (by linarith) (by linarith) (by linarith)
    rw [h1 x ⟨hx, le_max_right _ _⟩, ← ha, ← hb]
  -- parte esquerda
  obtain ⟨δ, hδ, hgap⟩ := exists_left_gap S s
  obtain ⟨αl, βl, hl⟩ := hg.2 (s - δ) s (by linarith) hgap
  have hgs_l := hl s ⟨by linarith, le_rfl⟩
  have hgs_r := hrall s le_rfl
  have hcont : αl + βl * s = αr + βr * s := by rw [← hgs_l, ← hgs_r]
  refine ⟨βr - βl, αr, βr, ⟨?_, fun a' b' hab hfree' => ?_⟩, hrall⟩
  · exact hg.1.sub (continuous_const.mul (continuous_const.max (continuous_id.sub continuous_const)))
  · by_cases hsm : s ∈ Ioo a' b'
    · -- s no interior: ambos os lados com a mesma inclinação
      have hfl : ∀ t ∈ S, t ∉ Ioo a' s := by
        intro t ht hmem
        have htne : t ≠ s := ne_of_lt hmem.2
        exact hfree' t (Finset.mem_erase.mpr ⟨htne, ht⟩) ⟨hmem.1, hmem.2.trans hsm.2⟩
      obtain ⟨α1, β1, h1⟩ := hg.2 a' s hsm.1 hfl
      have hu : max a' (s - δ) < s := max_lt hsm.1 (by linarith)
      have hu1 : max a' (s - δ) ∈ Icc a' s := ⟨le_max_left _ _, hu.le⟩
      have hu2 : max a' (s - δ) ∈ Icc (s - δ) s := ⟨le_max_right _ _, hu.le⟩
      have e1 := h1 _ hu1
      have e2 := hl _ hu2
      have f1 := h1 s ⟨hsm.1.le, le_rfl⟩
      have f2 := hl s ⟨by linarith, le_rfl⟩
      obtain ⟨ha, hb⟩ := line_unique (α := α1) (β := β1) (α' := αl) (β' := βl) hu
        (by linarith) (by linarith)
      refine ⟨αl, βl, fun x hx => ?_⟩
      show g x - (βr - βl) * max 0 (x - s) = _
      by_cases hxs : x ≤ s
      · rw [max_eq_left (by linarith), mul_zero, sub_zero, h1 x ⟨hx.1, hxs⟩, ha, hb]
      · push_neg at hxs
        rw [max_eq_right (by linarith), hrall x hxs.le]
        linear_combination (-1 : ℝ) * hcont
    · have hfa : ∀ t ∈ S, t ∉ Ioo a' b' := by
        intro t ht hmem
        by_cases hts : t = s
        · subst hts; exact hsm hmem
        · exact hfree' t (Finset.mem_erase.mpr ⟨hts, ht⟩) hmem
      obtain ⟨α1, β1, h1⟩ := hg.2 a' b' hab hfa
      have : b' ≤ s ∨ s ≤ a' := by
        by_contra h; push_neg at h; exact hsm ⟨h.2, h.1⟩
      rcases this with h | h
      · refine ⟨α1, β1, fun x hx => ?_⟩
        show g x - (βr - βl) * max 0 (x - s) = _
        rw [max_eq_left (by linarith [hx.2]), mul_zero, sub_zero]; exact h1 x hx
      · refine ⟨α1 + (βr - βl) * s, β1 - (βr - βl), fun x hx => ?_⟩
        show g x - (βr - βl) * max 0 (x - s) = _
        rw [max_eq_right (by linarith [hx.1]), h1 x hx]; ring

lemma relu_affine (α β : ℝ) : IsPL (fun x => max 0 (α + β * x)) := by
  by_cases hβ : β = 0
  · subst hβ; simpa using IsPL.const (max 0 α)
  · set z : ℝ := -α / β with hz
    have hα : α = -(β * z) := by rw [hz]; field_simp
    have hg : ∀ x, α + β * x = β * (x - z) := fun x => by rw [hα]; ring
    refine ⟨{z}, ?_, fun a b hab hfree => ?_⟩
    · exact continuous_const.max (continuous_const.add (continuous_const.mul continuous_id))
    · have hzn : z ∉ Ioo a b := hfree z (Finset.mem_singleton_self _)
      have : b ≤ z ∨ z ≤ a := by
        by_contra h; push_neg at h; exact hzn ⟨h.2, h.1⟩
      rcases lt_or_gt_of_ne hβ with hneg | hpos
      · rcases this with h | h
        · refine ⟨α, β, fun x hx => ?_⟩
          show max 0 (α + β * x) = _
          rw [max_eq_right]
          rw [hg]; nlinarith [hx.2]
        · refine ⟨0, 0, fun x hx => ?_⟩
          show max 0 (α + β * x) = _
          rw [max_eq_left]; · ring
          rw [hg]; nlinarith [hx.1]
      · rcases this with h | h
        · refine ⟨0, 0, fun x hx => ?_⟩
          show max 0 (α + β * x) = _
          rw [max_eq_left]; · ring
          rw [hg]; nlinarith [hx.2]
        · refine ⟨α, β, fun x hx => ?_⟩
          show max 0 (α + β * x) = _
          rw [max_eq_right]
          rw [hg]; nlinarith [hx.1]

lemma FinPL.relu : ∀ (n : ℕ) (g : ℝ → ℝ) (S : Finset ℝ), S.card = n → FinPL g S →
    IsPL (fun x => max 0 (g x)) := by
  intro n
  induction n with
  | zero =>
      intro g S hc hg
      have hS : S = ∅ := Finset.card_eq_zero.mp hc
      subst hS
      obtain ⟨α, β, h⟩ := hg.global_affine
      have : (fun x => max 0 (g x)) = fun x => max 0 (α + β * x) := by funext x; rw [h x]
      rw [this]; exact relu_affine α β
  | succ n ih =>
      intro g S hc hg
      have hS : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨a, α, β, hL, hR⟩ := hg.peel hS
      set s := S.max' hS with hsdef
      have hcard : (S.erase s).card = n := by
        rw [Finset.card_erase_of_mem (S.max'_mem hS)]; omega
      obtain ⟨S1, h1⟩ := ih _ _ hcard hL
      obtain ⟨S2, h2⟩ := relu_affine α β
      have hgs : max 0 (g s - a * max 0 (s - s)) = max 0 (α + β * s) := by
        rw [hR s le_rfl]; simp
      have hglue := FinPL.glue (s := s) h1 h2 hgs
      have heq : (fun x => max 0 (g x)) = fun x =>
          if x ≤ s then max 0 (g x - a * max 0 (x - s)) else max 0 (α + β * x) := by
        funext x
        by_cases hxs : x ≤ s
        · rw [if_pos hxs, max_eq_left (by linarith : x - s ≤ 0)]; simp
        · push_neg at hxs
          rw [if_neg (not_le.mpr hxs), hR x hxs.le]
      rw [heq]
      exact ⟨_, hglue⟩

lemma IsPL.relu {g : ℝ → ℝ} (hg : IsPL g) : IsPL (fun x => max 0 (g x)) := by
  obtain ⟨S, hS⟩ := hg
  exact FinPL.relu _ g S rfl hS

lemma FinPL.hinge : ∀ (n : ℕ) (g : ℝ → ℝ) (S : Finset ℝ), S.card = n → FinPL g S →
    ∃ (c q : ℝ) (a : ℝ → ℝ), ∀ x, g x = c + q * x + ∑ s ∈ S, a s * max 0 (x - s) := by
  classical
  intro n
  induction n with
  | zero =>
      intro g S hc hg
      have hS : S = ∅ := Finset.card_eq_zero.mp hc
      subst hS
      obtain ⟨α, β, h⟩ := hg.global_affine
      exact ⟨α, β, fun _ => 0, fun x => by simp [h x]⟩
  | succ n ih =>
      intro g S hc hg
      have hS : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨a0, α, β, hL, hR⟩ := hg.peel hS
      set s := S.max' hS with hsdef
      have hcard : (S.erase s).card = n := by
        rw [Finset.card_erase_of_mem (S.max'_mem hS)]; omega
      obtain ⟨c, q, a, hh⟩ := ih _ _ hcard hL
      refine ⟨c, q, fun t => if t = s then a0 else a t, fun x => ?_⟩
      have hsm : s ∈ S := S.max'_mem hS
      rw [← Finset.add_sum_erase S _ hsm]
      have e1 := hh x
      have e2 : ∑ t ∈ S.erase s, (fun t => if t = s then a0 else a t) t * max 0 (x - t) =
          ∑ t ∈ S.erase s, a t * max 0 (x - t) := by
        apply Finset.sum_congr rfl
        intro t ht
        simp [(Finset.mem_erase.mp ht).1]
      rw [e2]
      simp only [if_true]
      simp only at e1
      linarith

end DeepIV56

end Pendencias.Marcada

/-!
# IV.5.6 — parte 3: redes ReLU, forma reduzida e contagem de regiões afins máximas
-/

namespace Pendencias.Marcada

open Set Filter
open scoped Topology

namespace DeepIV56

/-- Funções realizadas por redes ReLU univariadas feedforward de profundidade e largura
arbitrárias, com saída vetorial de dimensão `m`: a entrada é `x ∈ ℝ` (dimensão 1); cada camada
é uma transformação afim `v ↦ A v + b` seguida, nas camadas ocultas, da ReLU coordenada a
coordenada. Como composições de afins são afins, todo `affine`/`relu` alternado (qualquer
arquitetura feedforward) está coberto, e esta é a classe de redes do TeX. -/
inductive NetFun : (m : ℕ) → (ℝ → Fin m → ℝ) → Prop
  | input : NetFun 1 (fun x _ => x)
  | affine {m n : ℕ} {f : ℝ → Fin m → ℝ} (h : NetFun m f)
      (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) :
      NetFun n (fun x => A.mulVec (f x) + b)
  | relu {m : ℕ} {f : ℝ → Fin m → ℝ} (h : NetFun m f) :
      NetFun m (fun x i => max 0 (f x i))

/-- `F : ℝ → ℝ` é a função realizada por uma rede ReLU univariada de saída escalar. -/
def IsReLUNetwork (F : ℝ → ℝ) : Prop := ∃ f, NetFun 1 f ∧ ∀ x, F x = f x 0

lemma NetFun.isPL {m : ℕ} {f : ℝ → Fin m → ℝ} (h : NetFun m f) : ∀ i, IsPL (fun x => f x i) := by
  induction h with
  | input => intro i; exact IsPL.id
  | affine h A b ih =>
      intro i
      have := (IsPL.sum Finset.univ (fun k x => A i k * _) (fun k _ => (ih k).smul (A i k))).add
        (IsPL.const (b i))
      simpa [Matrix.mulVec, dotProduct] using this
  | relu h ih => intro i; exact (ih i).relu

lemma IsReLUNetwork.isPL {F : ℝ → ℝ} (h : IsReLUNetwork F) : IsPL F := by
  obtain ⟨f, hf, hF⟩ := h
  have := hf.isPL 0
  have e : F = fun x => f x 0 := funext hF
  rw [e]; exact this

/-- Partição afim de `F` em `[0,1]`: pontos interiores `P` tais que `F` é afim em todo
subintervalo de `[0,1]` sem ponto de `P` no interior. -/
def IsAffPartition (F : ℝ → ℝ) (P : Finset ℝ) : Prop :=
  (∀ p ∈ P, 0 < p ∧ p < 1) ∧ ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → (∀ p ∈ P, p ∉ Ioo a b) →
    ∃ α β : ℝ, ∀ x ∈ Icc a b, F x = α + β * x

/-- `R(F)`: número de regiões afins máximas de `F` em `[0,1]`, isto é, o menor número de peças
afins de uma partição de `[0,1]` (`1 +` o menor número de quebras interiores). Para `F` contínua,
as regiões afins máximas são exatamente as peças da partição mínima. -/
noncomputable def regionCount (F : ℝ → ℝ) : ℕ :=
  sInf {n | ∃ P : Finset ℝ, IsAffPartition F P ∧ P.card + 1 = n}

/-- forma reduzida real de uma função contínua linear por partes em `[0,1]` -/
theorem reduced_of_PL {F : ℝ → ℝ} (hF : IsPL F) :
    ∃ (M : ℕ) (R : RealReLU M), R.Reduced ∧ ∀ x ∈ Icc (0 : ℝ) 1, R.eval x = F x := by
  classical
  obtain ⟨S, hS⟩ := hF
  obtain ⟨c, q, a, hh⟩ := FinPL.hinge _ F S rfl hS
  set B : Finset ℝ := S.filter (fun s => 0 < s ∧ s < 1 ∧ a s ≠ 0) with hB
  set L : Finset ℝ := S.filter (fun s => s ≤ 0) with hL
  let e := B.orderEmbOfFin rfl
  have hmemB : ∀ i, e i ∈ B := fun i => B.orderEmbOfFin_mem rfl i
  have hBprop : ∀ i, 0 < e i ∧ e i < 1 ∧ a (e i) ≠ 0 := fun i =>
    (Finset.mem_filter.mp (hmemB i)).2
  refine ⟨B.card, ⟨c - ∑ s ∈ L, a s * s, q + ∑ s ∈ L, a s, fun i => a (e i), e⟩,
    ⟨e.strictMono, fun i => ⟨(hBprop i).1, (hBprop i).2.1⟩, fun i => (hBprop i).2.2⟩, ?_⟩
  intro x hx
  show c - ∑ s ∈ L, a s * s + (q + ∑ s ∈ L, a s) * x +
      ∑ i, a (e i) * max 0 (x - e i) = F x
  have hsumB : ∑ i, a (e i) * max 0 (x - e i) = ∑ s ∈ B, a s * max 0 (x - s) := by
    calc ∑ i, a (e i) * max 0 (x - e i)
        = ∑ s ∈ Finset.univ.image e, a s * max 0 (x - s) :=
          (Finset.sum_image (f := fun s => a s * max 0 (x - s)) (s := Finset.univ) (g := ⇑e)
            (fun i _ j _ h => e.injective h)).symm
      _ = ∑ s ∈ B, a s * max 0 (x - s) := by
          rw [show Finset.univ.image e = B from Finset.image_orderEmbOfFin_univ B rfl]
  rw [hsumB, hh x]
  have hsplit : ∀ s ∈ S, a s * max 0 (x - s) =
      (if s ∈ B then a s * max 0 (x - s) else 0) + (if s ≤ 0 then a s * (x - s) else 0) := by
    intro s hs
    by_cases hs0 : s ≤ 0
    · have h1 : s ∉ B := fun h => by
        have := (Finset.mem_filter.mp h).2.1; linarith
      rw [if_neg h1, if_pos hs0, max_eq_right (by linarith [hx.1])]; ring
    · push_neg at hs0
      rw [if_neg (not_le.mpr hs0), add_zero]
      by_cases hs1 : s < 1
      · by_cases ha : a s = 0
        · simp [ha]
        · rw [if_pos (Finset.mem_filter.mpr ⟨hs, hs0, hs1, ha⟩)]
      · push_neg at hs1
        have h1 : s ∉ B := fun h => by
          have := (Finset.mem_filter.mp h).2.2.1; linarith
        rw [if_neg h1, max_eq_left (by linarith [hx.2])]; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  have e1 : S.filter (fun s => s ∈ B) = B := by
    ext s; simp only [Finset.mem_filter]; constructor
    · exact fun h => h.2
    · intro h; exact ⟨(Finset.mem_filter.mp h).1, h⟩
  rw [e1]
  have e2 : ∑ s ∈ S.filter (fun s => s ≤ 0), a s * (x - s) = (∑ s ∈ L, a s) * x - ∑ s ∈ L, a s * s := by
    rw [hL, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro s _; ring
  rw [e2]; ring

end DeepIV56

end Pendencias.Marcada

/-!
# IV.5.6 — parte 4: número de regiões, cotas de inclinação e corolário final
-/

namespace Pendencias.Marcada

open Artigo Set Filter
open scoped Topology

namespace DeepIV56

lemma exists_pos_dist (P : Finset ℝ) (τ : ℝ) (h : τ ∉ P) : ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ P, δ ≤ |p - τ| := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert p P hp ih =>
      obtain ⟨δ, hδ, hP⟩ := ih (fun h' => h (Finset.mem_insert_of_mem h'))
      have hne : p ≠ τ := fun e => h (e ▸ Finset.mem_insert_self _ _)
      refine ⟨min δ |p - τ|, lt_min hδ (abs_pos.mpr (sub_ne_zero.mpr hne)), ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hP q hq)

lemma regionCount_le {M : ℕ} (R : RealReLU M) (hR : R.Reduced) (F : ℝ → ℝ)
    (hRF : ∀ x ∈ Icc (0 : ℝ) 1, R.eval x = F x) :
    ∃ P : Finset ℝ, IsAffPartition F P ∧ P.card = M := by
  classical
  refine ⟨Finset.univ.image R.τ, ⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hR.2.1 i
  · intro a b ha hab hb hfree
    set I : Finset (Fin M) := Finset.univ.filter (fun i => R.τ i ≤ a) with hI
    refine ⟨R.c - ∑ i ∈ I, R.a i * R.τ i, R.q + ∑ i ∈ I, R.a i, fun x hx => ?_⟩
    rw [← hRF x ⟨ha.trans hx.1, hx.2.trans hb⟩]
    have hterm : ∀ i : Fin M, R.a i * max 0 (x - R.τ i) =
        if R.τ i ≤ a then R.a i * x - R.a i * R.τ i else 0 := by
      intro i
      have hi : R.τ i ∉ Ioo a b := hfree _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      by_cases h1 : R.τ i ≤ a
      · rw [if_pos h1, max_eq_right (by linarith [hx.1])]; ring
      · push_neg at h1
        have h2 : b ≤ R.τ i := by
          by_contra h; push_neg at h; exact hi ⟨h1, h⟩
        rw [if_neg (not_le.mpr h1), max_eq_left (by linarith [hx.2])]; ring
    unfold RealReLU.eval
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_filter, Finset.sum_sub_distrib,
      ← Finset.sum_mul]
    ring
  · rw [Finset.card_image_of_injective _ hR.1.injective, Finset.card_univ, Fintype.card_fin]

lemma regionCount_eq {M : ℕ} (R : RealReLU M) (hR : R.Reduced) (F : ℝ → ℝ)
    (hRF : ∀ x ∈ Icc (0 : ℝ) 1, R.eval x = F x) : regionCount F = M + 1 := by
  classical
  obtain ⟨P0, hP0, hc0⟩ := regionCount_le R hR F hRF
  have hne : {n | ∃ P : Finset ℝ, IsAffPartition F P ∧ P.card + 1 = n}.Nonempty :=
    ⟨_, P0, hP0, rfl⟩
  apply le_antisymm
  · have : P0.card + 1 ∈ {n | ∃ P : Finset ℝ, IsAffPartition F P ∧ P.card + 1 = n} :=
      ⟨P0, hP0, rfl⟩
    have h := Nat.sInf_le this
    rw [hc0] at h; exact h
  · obtain ⟨P, hP, hcard⟩ := Nat.sInf_mem hne
    unfold regionCount
    rw [← hcard]
    have hsub : Finset.univ.image R.τ ⊆ P := by
      intro t ht
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
      by_contra hnot
      obtain ⟨δ, hδ, hdist⟩ := exists_pos_dist P (R.τ i) hnot
      obtain ⟨h0, h1⟩ := hR.2.1 i
      set δ' := min δ (min (R.τ i) (1 - R.τ i)) with hδ'
      have hδ'pos : 0 < δ' := lt_min hδ (lt_min h0 (by linarith))
      have hδ1 : δ' ≤ δ := min_le_left _ _
      have hδ2 : δ' ≤ R.τ i := (min_le_right _ _).trans (min_le_left _ _)
      have hδ3 : δ' ≤ 1 - R.τ i := (min_le_right _ _).trans (min_le_right _ _)
      obtain ⟨α, β, haff⟩ := hP.2 (R.τ i - δ') (R.τ i + δ') (by linarith) (by linarith)
        (by linarith) (fun p hp hmem => by
          have := hdist p hp
          have h2 : |p - R.τ i| < δ' := abs_lt.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
          linarith)
      apply R.not_differentiableAt_break hR i
      have hd : HasDerivAt (fun x : ℝ => α + β * x) β (R.τ i) := by
        simpa using ((hasDerivAt_id (R.τ i)).const_mul β).const_add α
      apply hd.differentiableAt.congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds (show R.τ i - δ' < R.τ i by linarith)
        (show R.τ i < R.τ i + δ' by linarith)] with x hx
      rw [hRF x ⟨by linarith [hx.1], by linarith [hx.2]⟩]
      exact haff x ⟨hx.1.le, hx.2.le⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hR.1.injective, Finset.card_univ, Fintype.card_fin] at this
    omega

lemma sigma_abs_le {M : ℕ} (R : RealReLU M) (hR : R.Reduced) (L : ℝ) (hL0 : 0 ≤ L)
    (hlip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |R.eval x - R.eval y| ≤ L * |x - y|)
    (n : ℕ) (hn : n ≤ M) : |R.sigma n| ≤ L := by
  obtain ⟨l, r, hl, hlr, hr1, hreg⟩ := R.exists_region hR n hn
  set x₀ := (l + r) / 2 with hx₀
  have hx : x₀ ∈ Ioo l r := ⟨by rw [hx₀]; linarith, by rw [hx₀]; linarith⟩
  have hknots : ∀ i, x₀ ≠ R.τ i := by
    intro i
    have hi := hreg x₀ hx i
    split_ifs at hi with h
    · exact ne_of_gt hi
    · exact ne_of_lt hi
  have hslope : R.slope x₀ = R.sigma n := by
    unfold RealReLU.slope RealReLU.sigma
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hi := hreg x₀ hx i
    by_cases hin : i.val < n
    · rw [if_pos hin] at hi
      simp only [if_pos hin, if_pos hi]
    · rw [if_neg hin] at hi
      simp only [if_neg hin, if_neg (not_lt.mpr hi.le)]
  have hd := R.hasDerivAt_eval hknots
  rw [hslope] at hd
  have := hd.le_of_lip' hL0 (by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    have h1 : y ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have h2 : x₀ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simpa [Real.norm_eq_abs] using hlip y h1 x₀ h2)
  simpa [Real.norm_eq_abs] using this


/-- **IV.5.6 (redes profundas medidas pela função realizada)**. Seja `F` a função realizada por
uma rede ReLU univariada arbitrária (qualquer profundidade e largura), com norma uniforme em
`[0,1]` no máximo `B` e constante de Lipschitz em `[0,1]` no máximo `L`. Então `F` coincide em
`[0,1]` com uma forma ReLU reduzida real `R` com exatamente `M = R(F) - 1` hinges
(`R(F)` = número de regiões afins máximas, `regionCount`), cujos coeficientes satisfazem
`|c|, |q|, |a_j| ≤ W := 2 max{1, B, L}` (e `W ≥ 1`); em particular o teorema IV.5.5
(`quantized_approximate_reverse`) vale para `F` com esses `M` e `W`: para todo `0 < ε ≤ 1`
existe uma montagem `U` da biblioteca original com erro `≤ ε` em `[0,1]`, folhas
`≤ 1 + M D_ε` e altura `≤ C (M+1)³ (W+1)³ ε⁻²`. -/
theorem deep_functional_reverse :
    ∃ C : ℝ, 0 < C ∧ ∀ F : ℝ → ℝ, IsReLUNetwork F → ∀ B L : ℝ,
      (∀ x ∈ Icc (0 : ℝ) 1, |F x| ≤ B) →
      (∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |F x - F y| ≤ L * |x - y|) →
      ∃ (M : ℕ) (R : RealReLU M), R.Reduced ∧ M + 1 = regionCount F ∧
        (∀ x ∈ Icc (0 : ℝ) 1, R.eval x = F x) ∧
        1 ≤ 2 * max 1 (max B L) ∧ |R.c| ≤ 2 * max 1 (max B L) ∧
        |R.q| ≤ 2 * max 1 (max B L) ∧ (∀ i, |R.a i| ≤ 2 * max 1 (max B L)) ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          ∃ U : LTree, LTree.WF 0 0 U ∧
            (∀ x ∈ Icc (0 : ℝ) 1, |F x - U.eval 0 0 x| ≤ ε) ∧
            (U.numLeaves : ℝ) ≤ 1 + M * (⌈Real.logb 2
              (C * (M + 1) * (2 * max 1 (max B L) + 1) / ε)⌉₊ : ℝ) ∧
            (U.maxHeight : ℝ) ≤
              C * (M + 1) ^ 3 * (2 * max 1 (max B L) + 1) ^ 3 / ε ^ 2 := by
  obtain ⟨C, hC, hmain⟩ := QuantIV55.quantized_approximate_reverse
  refine ⟨C, hC, ?_⟩
  intro F hnet B L hB hLip
  obtain ⟨M, R, hR, hRF⟩ := reduced_of_PL hnet.isPL
  have hL0 : 0 ≤ L := by
    have := hLip 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
    simp at this
    linarith [abs_nonneg (F 0 - F 1)]
  have hlipR : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |R.eval x - R.eval y| ≤ L * |x - y| := fun x hx y hy => by
    rw [hRF x hx, hRF y hy]; exact hLip x hx y hy
  have hσ := sigma_abs_le R hR L hL0 hlipR
  set m : ℝ := max 1 (max B L) with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hBm : B ≤ m := (le_max_left B L).trans (le_max_right _ _)
  have hLm : L ≤ m := (le_max_right B L).trans (le_max_right _ _)
  have hc : |R.c| ≤ 2 * m := by
    have := hRF 0 ⟨le_rfl, zero_le_one⟩
    rw [R.eval_zero hR] at this
    rw [this]; linarith [hB 0 ⟨le_rfl, zero_le_one⟩]
  have hq : |R.q| ≤ 2 * m := by
    have h0 : R.sigma 0 = R.q := by simp [RealReLU.sigma]
    have := hσ 0 (Nat.zero_le _)
    rw [h0] at this; linarith
  have ha : ∀ i, |R.a i| ≤ 2 * m := by
    intro i
    rw [← R.sigma_succ_sub i]
    have h1 := hσ (i.val + 1) (by omega)
    have h2 := hσ i.val (by omega)
    calc |R.sigma (i.val + 1) - R.sigma i.val| ≤ |R.sigma (i.val + 1)| + |R.sigma i.val| :=
          abs_sub _ _
      _ ≤ 2 * m := by linarith
  refine ⟨M, R, hR, (regionCount_eq R hR F hRF).symm, hRF, by linarith, hc, hq, ha, ?_⟩
  intro ε hε0 hε1
  obtain ⟨U, hw, he, hn, hh⟩ := hmain M R hR (2 * m) ε (by linarith) hc hq ha hε0 hε1
  refine ⟨U, hw, fun x hx => ?_, hn, hh⟩
  rw [← hRF x hx]; exact he x hx

end DeepIV56

end Pendencias.Marcada

