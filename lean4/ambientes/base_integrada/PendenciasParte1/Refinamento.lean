import Unified.Fase3.Refinement
import Unified.Fase3.IntervalArith

/-!
# I.6.3 (refinamento certificado) e I.6.4 (correção, término e tamanho) com o majorante
intervalar concreto

`Fase3.refineCell/refineAll/refine_terminates/refine_correct` usam um majorante abstrato
`M : ℕ × ℤ → ℝ` sob o contrato (40). Aqui o majorante é o do avaliador intervalar:
`M(J) = M_int(J)` com `BoundSecondDerivative(E, J; P, d)` (I.6.2), e o algoritmo **aborta**
(`none`) se a certificação falhar em alguma célula consultada.

* `certRefine E P d εI roots r : Option (List (ℕ × ℤ))`: o algoritmo 6.3 para `F` dada por
  uma expressão `E ∈ 𝓔`;
* `certified_refinement`: o algoritmo devolve `none` exatamente quando alguma célula consultada
  falha; se devolve `some L`, então `f = E` é `C²` em `[α,β]`, `L` é a refinação com
  `M = M_int`, toda folha tem `η_cert ≤ ε_I`, nenhum ramo passa de `r*` níveis, há no máximo
  `R₀ 2^{r*}` folhas e vale a conclusão de `refine_correct` (`‖f - g‖ ≤ ε_I + ε_R`).

A cota `M_int(J) ≤ M*` para as células certificadas dentro de `[α,β]` é o contrato (40) sobre
`M*`.
-/

namespace PendenciasParte1

open Set Fase3

/-- a célula `J` como intervalo racional -/
def cellIv (J : ℕ × ℤ) : Iv := ⟨(J.2 : ℚ) / 2 ^ J.1, ((J.2 : ℚ) + 1) / 2 ^ J.1⟩

lemma mem_cellIv {J : ℕ × ℤ} {x : ℝ} : (cellIv J).Mem x ↔ x ∈ cC J := by
  simp [cellIv, Iv.Mem, cell, cellL, cellR]

/-- `BoundSecondDerivative(E, J; P, d)` na célula `J` -/
def bsdCell (E : Expr) (P d : ℕ) (J : ℕ × ℤ) : Option Iv := boundSecondDerivative E (cellIv J) P d

/-- `M(J) = M_int(J)` (valor irrelevante se a certificação falha: nesse caso o algoritmo aborta) -/
noncomputable def Mcell (E : Expr) (P d : ℕ) (J : ℕ × ℤ) : ℝ :=
  match bsdCell E P d J with
  | some I => (Mint I : ℝ)
  | none => 0

/-- células cujo `η_cert` o passo (iii) consulta, a partir de `J`, com `r` níveis -/
noncomputable def queried (M : ℕ × ℤ → ℝ) (ε : ℝ) : ℕ → ℕ × ℤ → List (ℕ × ℤ)
  | 0, J => [J]
  | r + 1, J => J :: (if cert M J ≤ ε then [] else
      queried M ε r (child0 J) ++ queried M ε r (child1 J))

noncomputable def queriedAll (M : ℕ × ℤ → ℝ) (ε : ℝ) (roots : List (ℕ × ℤ)) (r : ℕ) :
    List (ℕ × ℤ) := roots.flatMap (queried M ε r)

open Classical in
/-- **Algoritmo I.6.3** com o majorante intervalar: aborta (`none`) se alguma célula consultada
não é certificada; caso contrário emite as folhas da refinação -/
noncomputable def certRefine (E : Expr) (P d : ℕ) (εI : ℝ) (roots : List (ℕ × ℤ)) (r : ℕ) :
    Option (List (ℕ × ℤ)) :=
  if ∀ J ∈ queriedAll (Mcell E P d) εI roots r, (bsdCell E P d J).isSome then
    some (refineAll (Mcell E P d) εI roots r)
  else none

/-! ## Lemas sobre as células consultadas -/

section queried

variable {M M' : ℕ × ℤ → ℝ} {ε : ℝ}

lemma self_mem_queried (r : ℕ) (J : ℕ × ℤ) : J ∈ queried M ε r J := by
  cases r <;> simp [queried]

lemma queried_sub : ∀ (r : ℕ) (J L : ℕ × ℤ), L ∈ queried M ε r J → cC L ⊆ cC J := by
  intro r
  induction r with
  | zero => intro J L h; simp only [queried, List.mem_singleton] at h; subst h; exact subset_rfl
  | succ r ih =>
      intro J L h
      simp only [queried, List.mem_cons] at h
      rcases h with rfl | h
      · exact subset_rfl
      · split_ifs at h
        · simp at h
        · rcases List.mem_append.mp h with h | h
          · exact (ih _ _ h).trans (cC_child0 J)
          · exact (ih _ _ h).trans (cC_child1 J)

lemma refineCell_sub_queried : ∀ (r : ℕ) (J L : ℕ × ℤ), L ∈ refineCell M ε r J →
    L ∈ queried M ε r J := by
  intro r
  induction r with
  | zero => intro J L h; simpa [refineCell, queried] using h
  | succ r ih =>
      intro J L h
      simp only [refineCell] at h
      simp only [queried, List.mem_cons]
      split_ifs at h ⊢ with hc
      · left; simpa using h
      · right
        rcases List.mem_append.mp h with h | h
        · exact List.mem_append_left _ (ih _ _ h)
        · exact List.mem_append_right _ (ih _ _ h)

lemma refineCell_congr : ∀ (r : ℕ) (J : ℕ × ℤ), (∀ L ∈ queried M ε r J, M L = M' L) →
    refineCell M ε r J = refineCell M' ε r J := by
  intro r
  induction r with
  | zero => intro J _; rfl
  | succ r ih =>
      intro J h
      have hJ : cert M J = cert M' J := by
        unfold cert; rw [h J (self_mem_queried _ J)]
      simp only [refineCell, hJ]
      split_ifs with hc
      · rfl
      · have hq : ∀ L ∈ queried M ε r (child0 J) ++ queried M ε r (child1 J), M L = M' L :=
          fun L hL => h L (by
            simp only [queried, List.mem_cons]
            right; rw [if_neg (by rwa [hJ])]; exact hL)
        rw [ih _ fun L hL => hq L (List.mem_append_left _ hL),
          ih _ fun L hL => hq L (List.mem_append_right _ hL)]

end queried

/-- `d2 f α β = f''` num ponto admissível de `E` em `[α,β]` -/
lemma d2_eq_eval2 {E : Expr} {α β x : ℝ} (hαβ : α < β) (hx : x ∈ Icc α β) (hw : E.WD x) :
    d2 E.eval α β x = deriv (deriv E.eval) x := by
  have hu := uniqueDiffOn_Icc hαβ
  have hev : ∀ᶠ y in nhds x, E.WD y := (Expr.isOpen_WD E).mem_nhds hw
  have h1 : d1 E.eval α β =ᶠ[nhdsWithin x (Icc α β)] Expr.eval1 E := by
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with y hy hyI
    exact (Expr.hasDerivAt_eval E hy).1.hasDerivWithinAt.derivWithin (hu y hyI)
  unfold d2
  rw [h1.derivWithin_eq (h1.eq_of_nhdsWithin hx), Expr.deriv2_eval E hw]
  exact (Expr.hasDerivAt_eval E hw).2.hasDerivWithinAt.derivWithin (hu x hx)

/-- **Teorema I.6.4 / Algoritmo I.6.3** com o majorante intervalar certificado. -/
theorem certified_refinement {E : Expr} {P d : ℕ} {α β εI εR h0 Mstar : ℝ} (hαβ : α < β)
    (hεI : 0 < εI) (hεR : 0 < εR) {roots : List (ℕ × ℤ)} (hroots : roots.Pairwise DisjInt)
    (hcov : Icc α β ⊆ ⋃ J ∈ roots, cC J) (hsub : ∀ J ∈ roots, cC J ⊆ Icc α β)
    (hh0 : ∀ J ∈ roots, mesh J.1 ≤ h0)
    (hMstar : ∀ J I, cC J ⊆ Icc α β → bsdCell E P d J = some I → (Mint I : ℝ) ≤ Mstar) :
    (certRefine E P d εI roots (rStar h0 Mstar εI) = none ↔
      ∃ J ∈ queriedAll (Mcell E P d) εI roots (rStar h0 Mstar εI), bsdCell E P d J = none) ∧
    ∀ L, certRefine E P d εI roots (rStar h0 Mstar εI) = some L →
      L = refineAll (Mcell E P d) εI roots (rStar h0 Mstar εI) ∧
      ContDiffOn ℝ 2 E.eval (Icc α β) ∧
      (∀ J ∈ L, cert (Mcell E P d) J ≤ εI) ∧
      (∀ J ∈ L, ∃ J0 ∈ roots, J0.1 ≤ J.1 ∧ J.1 ≤ J0.1 + rStar h0 Mstar εI ∧ cC J ⊆ cC J0) ∧
      L.length ≤ roots.length * 2 ^ rStar h0 Mstar εI ∧
      (∃ v : ℝ → ℚ, (∀ J ∈ L, |(v (cL J) : ℝ) - extF E.eval α β (cL J)| < εR ∧
          |(v (cR J) : ℝ) - extF E.eval α β (cR J)| < εR) ∧ ∀ J ∈ L, v (cL J) ≠ v (cR J)) ∧
      ∀ v : ℝ → ℚ, (∀ J ∈ L, |(v (cL J) : ℝ) - extF E.eval α β (cL J)| < εR ∧
          |(v (cR J) : ℝ) - extF E.eval α β (cR J)| < εR) →
        (∀ J ∈ L, v (cL J) ≠ v (cR J)) →
        IsAssembly α β (cellInterp L.toFinset (fun t => (v t : ℝ))) ∧
        (∀ J ∈ L, ∃! n, gK n = J.1 ∧ gM n = J.2 ∧
            ∀ x, atomLine n x = lin J (fun t => (v t : ℝ)) x) ∧
        supNormOn (Icc α β) (fun x => E.eval x - cellInterp L.toFinset (fun t => (v t : ℝ)) x) ≤
          εI + εR := by
  classical
  set r := rStar h0 Mstar εI
  set Mc := Mcell E P d
  constructor
  · unfold certRefine
    split_ifs with h
    · simp only [reduceCtorEq, false_iff, not_exists, not_and]
      intro J hJ hn; have := h J hJ; rw [hn] at this; simp at this
    · simp only [true_iff]
      push_neg at h
      obtain ⟨J, hJ, hn⟩ := h
      exact ⟨J, hJ, Option.not_isSome_iff_eq_none.mp hn⟩
  intro L hL
  unfold certRefine at hL
  split_ifs at hL with hall
  simp only [Option.some.injEq] at hL
  subst hL
  -- células consultadas estão dentro de `[α,β]` e são certificadas
  have hq : ∀ J ∈ queriedAll Mc εI roots r, cC J ⊆ Icc α β ∧ ∃ I, bsdCell E P d J = some I := by
    intro J hJ
    obtain ⟨R, hR, hJR⟩ := List.mem_flatMap.mp hJ
    exact ⟨(queried_sub r R J hJR).trans (hsub R hR), Option.isSome_iff_exists.mp (hall J hJ)⟩
  have hroot : ∀ R ∈ roots, R ∈ queriedAll Mc εI roots r := fun R hR =>
    List.mem_flatMap.mpr ⟨R, hR, self_mem_queried r R⟩
  -- certificação ⟹ admissibilidade e cota pontual em cada ponto de `[α,β]`
  have hpt : ∀ x ∈ Icc α β, ∃ I, E.WD x ∧ |deriv (deriv E.eval) x| ≤ (Mint I : ℝ) ∧
      (Mint I : ℝ) ≤ Mstar := by
    intro x hx
    obtain ⟨R, hR, hxR⟩ := mem_iUnion₂.mp (hcov hx)
    obtain ⟨hRsub, I, hI⟩ := hq R (hroot R hR)
    have hm : (cellIv R).Mem x := mem_cellIv.mpr hxR
    exact ⟨I, (bsdAux_sound P E d _ I hI x hm).1,
      (boundSecondDerivative_correct E _ P d I hI x hm).2.2, hMstar R I hRsub hI⟩
  have hf : ContDiffOn ℝ 2 E.eval (Icc α β) := fun x hx => by
    obtain ⟨I, hw, -⟩ := hpt x hx
    exact (Expr.contDiffAt_eval E hw).contDiffWithinAt
  have hnorm : normD2 E.eval α β ≤ Mstar := by
    refine supNormOn_le ⟨α, le_rfl, hαβ.le⟩ fun x hx => ?_
    obtain ⟨I, hw, h1, h2⟩ := hpt x hx
    rw [d2_eq_eval2 hαβ hx hw]
    exact h1.trans h2
  -- majorante válido em todas as células
  let M' : ℕ × ℤ → ℝ := fun J =>
    if cC J ⊆ Icc α β then (match bsdCell E P d J with
      | some I => (Mint I : ℝ)
      | none => Mstar) else Mstar
  have hglob : ∀ x, |deriv (deriv (extF E.eval α β)) x| ≤ Mstar := fun x => by
    rw [deriv2_extF hαβ hf]; exact (abs_extF2_le hαβ hf x).trans hnorm
  have hM' : ∀ J, (∀ x ∈ cC J, |deriv (deriv (extF E.eval α β)) x| ≤ M' J) ∧ M' J ≤ Mstar := by
    intro J
    by_cases hJ : cC J ⊆ Icc α β
    · cases hb : bsdCell E P d J with
      | none => simp only [M', if_pos hJ, hb]; exact ⟨fun x _ => hglob x, le_rfl⟩
      | some I =>
          simp only [M', if_pos hJ, hb]
          refine ⟨fun x hx => ?_, hMstar J I hJ hb⟩
          have hm : (cellIv J).Mem x := mem_cellIv.mpr hx
          rw [deriv2_extF hαβ hf, extF2_eq_comp hαβ, clamp_of_mem (hJ hx),
            d2_eq_eval2 hαβ (hJ hx) (bsdAux_sound P E d _ I hb x hm).1]
          exact (boundSecondDerivative_correct E _ P d I hb x hm).2.2
    · simp only [M', if_neg hJ]; exact ⟨fun x _ => hglob x, le_rfl⟩
  -- `M_int` e `M'` coincidem nas células consultadas
  have hagree : ∀ J ∈ queriedAll Mc εI roots r, Mc J = M' J := by
    intro J hJ
    obtain ⟨hJsub, I, hI⟩ := hq J hJ
    simp only [Mc, Mcell, M', if_pos hJsub, hI]
  have hL : refineAll Mc εI roots r = refineAll M' εI roots r := by
    unfold refineAll
    refine List.flatMap_congr fun R hR => refineCell_congr r R fun J hJ =>
      hagree J (List.mem_flatMap.mpr ⟨R, hR, hJ⟩)
  have hleafq : ∀ J ∈ refineAll Mc εI roots r, J ∈ queriedAll Mc εI roots r := by
    intro J hJ
    obtain ⟨R, hR, hJR⟩ := List.mem_flatMap.mp hJ
    exact List.mem_flatMap.mpr ⟨R, hR, refineCell_sub_queried r R J hJR⟩
  obtain ⟨-, hcert, hdepth, hlen⟩ := refine_terminates M' (fun J => (hM' J).2) hεI roots hh0
  have hcorr := refine_correct hαβ hf M' hM' hεI hεR roots hroots hcov hh0
  rw [← hL] at hcert hdepth hlen hcorr
  refine ⟨rfl, hf, fun J hJ => ?_, hdepth, hlen, hcorr⟩
  have := hcert J hJ
  unfold cert at this ⊢
  rwa [hagree J (hleafq J hJ)]

end PendenciasParte1
