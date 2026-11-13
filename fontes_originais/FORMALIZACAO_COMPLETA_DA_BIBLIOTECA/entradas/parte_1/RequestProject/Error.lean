module
public import RequestProject.Normalization

/-!
# Seção 6: orçamentos e erro com codomínio completo

Formalização da Seção 6 (`sec:error`).
-/

@[expose] public section

open scoped Classical

noncomputable section

namespace Montagens

open Atom

variable {α β : ℝ}

/-- `Budget_{N,H}(Λ) :⟺ |Λ| ≤ N ∧ ∀ a ∈ Λ, h(a) ≤ H`. -/
def Budget (N H : ℕ) (Λ : Finset Atom) : Prop :=
  Λ.card ≤ N ∧ ∀ a ∈ Λ, a.height ≤ H

/-- `𝒜^loc_{N,H}(K) ⊆ C_K`. -/
def AlocNH (α β : ℝ) (N H : ℕ) : Set (CK α β) :=
  {g | ∃ Λ, LocalRep α β g Λ ∧ Budget N H Λ}

/-- `𝒜^con_{N,H}(K) ⊆ C_K`. -/
def AstrNH (α β : ℝ) (N H : ℕ) : Set (CK α β) :=
  {g | ∃ Λ, StrongRep α β g Λ ∧ Budget N H Λ}

/-- Teorema `thm:budget` (igualdade sob os mesmos recursos). O documento
enuncia o resultado para `H ≥ 2`; a demonstração não usa essa hipótese, e o
enunciado vale para todo `H`. -/
theorem AlocNH_eq_AstrNH (hK : α < β) (N H : ℕ) : AlocNH α β N H = AstrNH α β N H := by
  ext g; constructor
  · rintro ⟨Λ, h, hb⟩
    obtain ⟨⟨hsub, hcard⟩, -, -, hstr, -⟩ := normalization hK h
    exact ⟨_, hstr, le_trans hcard hb.1, fun a ha => hb.2 a (hsub ha)⟩
  · rintro ⟨Λ, h, hb⟩; exact ⟨Λ, h.1, hb⟩

/-- Distância uniforme `d_K(f, g) = max_{z : K} |f(z) - g(z)|`
(definida como supremo; o máximo é atingido, ver `dK_isMax`). -/
def dK (f g : CK α β) : ℝ := ⨆ z : Set.Icc α β, |f z - g z|

/-- O máximo em `d_K` existe (domínio compacto não vazio) e `d_K(f,g) = ‖f - g‖`. -/
theorem dK_isMax (hK : α < β) (f g : CK α β) :
    (∃ z₀ : Set.Icc α β, dK f g = |f z₀ - g z₀| ∧ ∀ z, |f z - g z| ≤ |f z₀ - g z₀|) ∧
    dK f g = ‖f - g‖ ∧ 0 ≤ dK f g := by
  haveI : Nonempty (Set.Icc α β) := ⟨⟨α, le_rfl, hK.le⟩⟩
  have hc : Continuous (fun z : Set.Icc α β => |f z - g z|) := by fun_prop
  obtain ⟨z₀, -, hz⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
  have hmax : ∀ z, |f z - g z| ≤ |f z₀ - g z₀| := fun z => hz (Set.mem_univ z)
  have hd : dK f g = |f z₀ - g z₀| := by
    apply le_antisymm
    · exact ciSup_le hmax
    · exact le_ciSup ⟨_, by rintro _ ⟨z, rfl⟩; exact hmax z⟩ z₀
  refine ⟨⟨z₀, hd, hmax⟩, ?_, by rw [hd]; exact abs_nonneg _⟩
  rw [ContinuousMap.norm_eq_iSup_norm]
  simp [dK, Real.norm_eq_abs]

/-- `Err_K(f, 𝒮) = inf {ofReal(d_K(f, g)) : g ∈ 𝒮}` em `[0, +∞]`. -/
def Err (f : CK α β) (S : Set (CK α β)) : ENNReal :=
  ⨅ g ∈ S, ENNReal.ofReal (dK f g)

/-- `E^loc_{N,H}(f)`. -/
def Eloc (N H : ℕ) (f : CK α β) : ENNReal := Err f (AlocNH α β N H)

/-- `E^con_{N,H}(f)`. -/
def Econ (N H : ℕ) (f : CK α β) : ENNReal := Err f (AstrNH α β N H)

theorem Err_empty (f : CK α β) : Err f ∅ = ⊤ := by
  simp [Err]

/-- Corolário: igualdade dos erros e de suas condições de altura. -/
theorem errors_eq (hK : α < β) (f : CK α β) (N H : ℕ) :
    Eloc N H f = Econ N H f := by
  simp only [Eloc, Econ, AlocNH_eq_AstrNH hK]

theorem heights_eq (hK : α < β) (f : CK α β) (N : ℕ) (ε : ℝ) :
    {H : ℕ | 2 ≤ H ∧ Eloc N H f ≤ ENNReal.ofReal ε} =
    {H : ℕ | 2 ≤ H ∧ Econ N H f ≤ ENNReal.ofReal ε} ∧
    sInf {H : ℕ | 2 ≤ H ∧ Eloc N H f ≤ ENNReal.ofReal ε} =
    sInf {H : ℕ | 2 ≤ H ∧ Econ N H f ≤ ENNReal.ofReal ε} := by
  have : ∀ H, Eloc N H f = Econ N H f := fun H => errors_eq hK f N H
  simp only [this, and_self]

/-- Proposição `prop:fixed` (testemunhas já ativas). -/
theorem norm_fixed_of_active {Λ : Finset Atom} (h : ∀ a ∈ Λ, Active α β a) :
    NormK α β Λ = Λ :=
  Finset.filter_true_of_mem h

theorem norm_fixed_of_subset {Λ : Finset Atom} (h : ∀ a ∈ Λ, a.Ja ⊆ K α β) :
    NormK α β Λ = Λ := by
  apply Finset.filter_true_of_mem
  intro a ha
  have hg := geometry a.C
  have hJ := h a ha
  have hL : a.La ∈ K α β := hJ ⟨le_rfl, hg.2.2.2.2.1.le⟩
  have hR : a.Ra ∈ K α β := hJ ⟨hg.2.2.2.2.1.le, le_rfl⟩
  unfold Active
  rw [← Set.nonempty_iff_ne_empty]
  refine ⟨a.Xa, ⟨hg.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2.1⟩, ?_, ?_⟩
  · exact lt_of_le_of_lt hL.1 hg.2.2.2.2.2.2.1
  · exact lt_of_lt_of_le hg.2.2.2.2.2.2.2.1 hR.2

end Montagens

end
