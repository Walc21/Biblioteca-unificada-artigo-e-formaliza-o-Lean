import PendenciasParte1.Refinamento

/-!
# I.6.3–I.6.4: certificados da extensão em coberturas externas

A extensão quadrática satisfaz `F'' x = d2 f α β (clamp α β x)`.
O certificado de uma célula é calculado em uma caixa racional que contém a
imagem projetada da célula. Não se exige que as raízes estejam em `[α,β]`.
A caixa pode incluir pontos adicionais; nesse caso a rotina pode falhar,
mas uma falha nunca é usada como certificado.
-/

namespace PendenciasParte1.CoberturaExterna

open Set Fase3

/-- Extremo racional inferior na malha `2⁻ᵖ`; corresponde a
`2⁻ᵖ floor(2ᵖ x)` no LaTeX. O arredondamento é sempre para fora. -/
noncomputable def lowerQ (p : ℕ) (x : ℝ) : ℚ :=
  (⌊x * (2 : ℝ) ^ p⌋ : ℤ) / (2 : ℚ) ^ p

/-- Extremo racional superior `2⁻ᵖ ceil(2ᵖ x)` do LaTeX. -/
noncomputable def upperQ (p : ℕ) (x : ℝ) : ℚ :=
  (⌈x * (2 : ℝ) ^ p⌉ : ℤ) / (2 : ℚ) ^ p

lemma lowerQ_le (p : ℕ) (x : ℝ) : (lowerQ p x : ℝ) ≤ x := by
  unfold lowerQ
  push_cast
  exact (div_le_iff₀ (by positivity)).2 (Int.floor_le _)

lemma le_upperQ (p : ℕ) (x : ℝ) : x ≤ (upperQ p x : ℝ) := by
  unfold upperQ
  push_cast
  exact (le_div_iff₀ (by positivity)).2 (Int.le_ceil _)

lemma clamp_mono {α β x y : ℝ} (h : x ≤ y) :
    clamp α β x ≤ clamp α β y := by
  unfold clamp
  exact max_le_max le_rfl (min_le_min h le_rfl)

/-- Caixa `Bₚ(J)` do texto corrigido. Seus extremos racionais envolvem
`[clamp α β (cL J), clamp α β (cR J)]`, inclusive quando `J` sai de `K`. -/
noncomputable def projectedBox (α β : ℝ) (p : ℕ) (J : ℕ × ℤ) : Iv :=
  ⟨lowerQ p (clamp α β (cL J)), upperQ p (clamp α β (cR J))⟩

lemma clamp_mem_projectedBox {α β : ℝ} (p : ℕ) {J : ℕ × ℤ} {x : ℝ}
    (hx : x ∈ cC J) : (projectedBox α β p J).Mem (clamp α β x) := by
  constructor
  · exact (lowerQ_le _ _).trans (clamp_mono hx.1)
  · exact (clamp_mono hx.2).trans (le_upperQ _ _)

/-- Avaliação intervalar de `E''` na caixa projetada, não na parte de `J`
exterior a `K`. Pela identidade de `F''`, certifica a extensão de Taylor. -/
noncomputable def bsdProjected (E : Expr) (α β : ℝ) (p P d : ℕ) (J : ℕ × ℤ) :
    Option Iv := boundSecondDerivative E (projectedBox α β p J) P d

/-- Majorante `M(J)` do texto. O valor 0 na falha serve apenas para definir
as consultas; `certRefineProjected` rejeita qualquer consulta sem certificado. -/
noncomputable def Mprojected (E : Expr) (α β : ℝ) (p P d : ℕ) (J : ℕ × ℤ) : ℝ :=
  match bsdProjected E α β p P d J with
  | some I => (Mint I : ℝ)
  | none => 0

open Classical in
/-- I.6.3 corrigido: refina a cobertura com os certificados da extensão.
Retorna `none` se alguma caixa consultada não for certificada. O resultado
`some L` é a lista de folhas; as escolhas nodais e os endereços são
especificados pelo teorema `certified_refinement_external`. -/
noncomputable def certRefineProjected (E : Expr) (α β : ℝ) (p P d : ℕ)
    (εI : ℝ) (roots : List (ℕ × ℤ)) (r : ℕ) : Option (List (ℕ × ℤ)) :=
  if ∀ J ∈ queriedAll (Mprojected E α β p P d) εI roots r,
      (bsdProjected E α β p P d J).isSome then
    some (refineAll (Mprojected E α β p P d) εI roots r)
  else none

/-- Uma caixa bem-sucedida limita `F''` em toda a célula original.
Esta é a ponte que permite dispensar `hsub`. -/
theorem projected_certificate_sound {E : Expr} {α β : ℝ} (hαβ : α < β)
    (hf : ContDiffOn ℝ 2 E.eval (Icc α β)) {p P d : ℕ} {J : ℕ × ℤ} {I : Iv}
    (hI : bsdProjected E α β p P d J = some I) {x : ℝ} (hx : x ∈ cC J) :
    |deriv (deriv (extF E.eval α β)) x| ≤ (Mint I : ℝ) := by
  have hm := clamp_mem_projectedBox (α := α) (β := β) p hx
  have hw := (bsdAux_sound P E d _ I hI (clamp α β x) hm).1
  rw [deriv2_extF hαβ hf, extF2_eq_comp hαβ,
    d2_eq_eval2 hαβ (clamp_mem hαβ.le x) hw]
  exact (boundSecondDerivative_correct E _ P d I hI (clamp α β x) hm).2.2

/-- Versão contratual de I.6.4 para `f ∈ C²(K)` e sua extensão quadrática.
Reúne o término e a correção já provados na base, sem restringir as raízes a K.
É a parte geral do enunciado LaTeX; o teorema seguinte trata o oráculo intervalar. -/
theorem refinement_contract_external {f : ℝ → ℝ} {α β : ℝ}
    (hαβ : α < β) (hf : ContDiffOn ℝ 2 f (Icc α β))
    (M : ℕ × ℤ → ℝ) {Mstar εI εR h0 : ℝ}
    (hM : ∀ J, (∀ x ∈ cC J, |deriv (deriv (extF f α β)) x| ≤ M J) ∧ M J ≤ Mstar)
    (hεI : 0 < εI) (hεR : 0 < εR) (roots : List (ℕ × ℤ))
    (hroots : roots.Pairwise DisjInt) (hcov : Icc α β ⊆ ⋃ J ∈ roots, cC J)
    (hh0 : ∀ J ∈ roots, mesh J.1 ≤ h0) :
    let L := refineAll M εI roots (rStar h0 Mstar εI)
    ((∀ s, refineAll M εI roots (rStar h0 Mstar εI + s) = L) ∧
      (∀ J ∈ L, cert M J ≤ εI) ∧
      (∀ J ∈ L, ∃ J0 ∈ roots, J0.1 ≤ J.1 ∧
        J.1 ≤ J0.1 + rStar h0 Mstar εI ∧ cC J ⊆ cC J0) ∧
      L.length ≤ roots.length * 2 ^ rStar h0 Mstar εI) ∧
    (∃ v : ℝ → ℚ, (∀ J ∈ L,
        |(v (cL J) : ℝ) - extF f α β (cL J)| < εR ∧
        |(v (cR J) : ℝ) - extF f α β (cR J)| < εR) ∧
      ∀ J ∈ L, v (cL J) ≠ v (cR J)) ∧
    ∀ v : ℝ → ℚ, (∀ J ∈ L,
        |(v (cL J) : ℝ) - extF f α β (cL J)| < εR ∧
        |(v (cR J) : ℝ) - extF f α β (cR J)| < εR) →
      (∀ J ∈ L, v (cL J) ≠ v (cR J)) →
      IsAssembly α β (cellInterp L.toFinset (fun t => (v t : ℝ))) ∧
      (∀ J ∈ L, ∃! n, gK n = J.1 ∧ gM n = J.2 ∧
        ∀ x, atomLine n x = lin J (fun t => (v t : ℝ)) x) ∧
      supNormOn (Icc α β)
        (fun x => f x - cellInterp L.toFinset (fun t => (v t : ℝ)) x) ≤ εI + εR := by
  dsimp only
  exact ⟨refine_terminates M (fun J => (hM J).2) hεI roots hh0,
    refine_correct hαβ hf M hM hεI hεR roots hroots hcov hh0⟩

/-- I.6.3–I.6.4 para uma cobertura diádica externa arbitrária.
O contrato de `Mstar` é o limite superior dos certificados bem-sucedidos.
Nenhuma hipótese de contenção das raízes em `[α,β]` é usada.
A saída inclui certificados, cotas de profundidade e folhas, existência de
valores nodais compartilhados, endereços únicos e a cota `εI + εR`. -/
theorem certified_refinement_external {E : Expr} {p P d : ℕ}
    {α β εI εR h0 Mstar : ℝ} (hαβ : α < β) (hεI : 0 < εI) (hεR : 0 < εR)
    {roots : List (ℕ × ℤ)} (hroots : roots.Pairwise DisjInt)
    (hcov : Icc α β ⊆ ⋃ J ∈ roots, cC J)
    (hh0 : ∀ J ∈ roots, mesh J.1 ≤ h0)
    (hMstar : ∀ J I, bsdProjected E α β p P d J = some I → (Mint I : ℝ) ≤ Mstar) :
    (certRefineProjected E α β p P d εI roots (rStar h0 Mstar εI) = none ↔
      ∃ J ∈ queriedAll (Mprojected E α β p P d) εI roots (rStar h0 Mstar εI),
        bsdProjected E α β p P d J = none) ∧
    ∀ L, certRefineProjected E α β p P d εI roots (rStar h0 Mstar εI) = some L →
      L = refineAll (Mprojected E α β p P d) εI roots (rStar h0 Mstar εI) ∧
      ContDiffOn ℝ 2 E.eval (Icc α β) ∧
      (∀ J ∈ L, cert (Mprojected E α β p P d) J ≤ εI) ∧
      (∀ J ∈ L, ∃ J0 ∈ roots, J0.1 ≤ J.1 ∧
        J.1 ≤ J0.1 + rStar h0 Mstar εI ∧ cC J ⊆ cC J0) ∧
      L.length ≤ roots.length * 2 ^ rStar h0 Mstar εI ∧
      (∃ v : ℝ → ℚ, (∀ J ∈ L,
        |(v (cL J) : ℝ) - extF E.eval α β (cL J)| < εR ∧
        |(v (cR J) : ℝ) - extF E.eval α β (cR J)| < εR) ∧
        ∀ J ∈ L, v (cL J) ≠ v (cR J)) ∧
      ∀ v : ℝ → ℚ, (∀ J ∈ L,
        |(v (cL J) : ℝ) - extF E.eval α β (cL J)| < εR ∧
        |(v (cR J) : ℝ) - extF E.eval α β (cR J)| < εR) →
        (∀ J ∈ L, v (cL J) ≠ v (cR J)) →
        IsAssembly α β (cellInterp L.toFinset (fun t => (v t : ℝ))) ∧
        (∀ J ∈ L, ∃! n, gK n = J.1 ∧ gM n = J.2 ∧
          ∀ x, atomLine n x = lin J (fun t => (v t : ℝ)) x) ∧
        supNormOn (Icc α β)
          (fun x => E.eval x - cellInterp L.toFinset (fun t => (v t : ℝ)) x) ≤ εI + εR := by
  classical
  set r := rStar h0 Mstar εI
  set Mc := Mprojected E α β p P d
  constructor
  · unfold certRefineProjected
    split_ifs with h
    · simp only [reduceCtorEq, false_iff, not_exists, not_and]
      intro J hJ hn
      have := h J hJ
      rw [hn] at this
      simp at this
    · simp only [true_iff]
      push_neg at h
      obtain ⟨J, hJ, hn⟩ := h
      exact ⟨J, hJ, Option.not_isSome_iff_eq_none.mp hn⟩
  intro L hL
  unfold certRefineProjected at hL
  split_ifs at hL with hall
  simp only [Option.some.injEq] at hL
  subst hL
  have hq : ∀ J ∈ queriedAll Mc εI roots r,
      ∃ I, bsdProjected E α β p P d J = some I := by
    intro J hJ
    exact Option.isSome_iff_exists.mp (hall J hJ)
  have hroot : ∀ R ∈ roots, R ∈ queriedAll Mc εI roots r := fun R hR =>
    List.mem_flatMap.mpr ⟨R, hR, self_mem_queried r R⟩
  have hpt : ∀ x ∈ Icc α β, ∃ I, E.WD x ∧
      |deriv (deriv E.eval) x| ≤ (Mint I : ℝ) ∧ (Mint I : ℝ) ≤ Mstar := by
    intro x hx
    obtain ⟨R, hR, hxR⟩ := mem_iUnion₂.mp (hcov hx)
    obtain ⟨I, hI⟩ := hq R (hroot R hR)
    have hm := clamp_mem_projectedBox (α := α) (β := β) p hxR
    rw [clamp_of_mem hx] at hm
    exact ⟨I, (bsdAux_sound P E d _ I hI x hm).1,
      (boundSecondDerivative_correct E _ P d I hI x hm).2.2, hMstar R I hI⟩
  have hf : ContDiffOn ℝ 2 E.eval (Icc α β) := fun x hx => by
    obtain ⟨I, hw, -⟩ := hpt x hx
    exact (Expr.contDiffAt_eval E hw).contDiffWithinAt
  have hnorm : normD2 E.eval α β ≤ Mstar := by
    refine supNormOn_le ⟨α, le_rfl, hαβ.le⟩ fun x hx => ?_
    obtain ⟨I, hw, h1, h2⟩ := hpt x hx
    rw [d2_eq_eval2 hαβ hx hw]
    exact h1.trans h2
  have hglob : ∀ x, |deriv (deriv (extF E.eval α β)) x| ≤ Mstar := fun x => by
    rw [deriv2_extF hαβ hf]
    exact (abs_extF2_le hαβ hf x).trans hnorm
  let M' : ℕ × ℤ → ℝ := fun J =>
    match bsdProjected E α β p P d J with
    | some I => (Mint I : ℝ)
    | none => Mstar
  have hM' : ∀ J,
      (∀ x ∈ cC J, |deriv (deriv (extF E.eval α β)) x| ≤ M' J) ∧ M' J ≤ Mstar := by
    intro J
    cases hb : bsdProjected E α β p P d J with
    | none => simp only [M', hb]; exact ⟨fun x _ => hglob x, le_rfl⟩
    | some I =>
      simp only [M', hb]
      exact ⟨fun x hx => projected_certificate_sound hαβ hf hb hx, hMstar J I hb⟩
  have hagree : ∀ J ∈ queriedAll Mc εI roots r, Mc J = M' J := by
    intro J hJ
    obtain ⟨I, hI⟩ := hq J hJ
    simp only [Mc, Mprojected, M', hI]
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

/-- A raiz `[0,1]` cobre `[1/3,2/3]`, embora não esteja contida nele. -/
theorem thirds_cover : Icc (1 / 3 : ℝ) (2 / 3) ⊆ ⋃ J ∈ ([(0, 0)] : List (ℕ × ℤ)), cC J := by
  intro x hx
  refine mem_iUnion₂.mpr ⟨(0, 0), by simp, ?_⟩
  have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  simpa [cC, cell, cellL, cellR] using hx01

/-- A hipótese antiga de contenção exclui a raiz válida do exemplo. -/
theorem thirds_root_not_contained : ¬ cC (0, 0) ⊆ Icc (1 / 3 : ℝ) (2 / 3) := by
  intro h
  have hz : (0 : ℝ) ∈ cC (0, 0) := by norm_num [cC, cell, cellL, cellR]
  have := h hz
  norm_num at this

/-- Instância de I.6.4 em `[1/3,2/3]`, a partir da raiz externa `[0,1]`.
O sucesso do oráculo e o limite dos certificados fornecem uma montagem
com o erro declarado, sem qualquer hipótese `hsub`. -/
theorem thirds_success {E : Expr} {p P d : ℕ} {εI εR Mstar : ℝ}
    (hεI : 0 < εI) (hεR : 0 < εR)
    (hMstar : ∀ J I, bsdProjected E (1 / 3) (2 / 3) p P d J = some I →
      (Mint I : ℝ) ≤ Mstar) {L : List (ℕ × ℤ)}
    (hL : certRefineProjected E (1 / 3) (2 / 3) p P d εI [(0, 0)]
      (rStar 1 Mstar εI) = some L) :
    ∃ g, IsAssembly (1 / 3) (2 / 3) g ∧
      supNormOn (Icc (1 / 3 : ℝ) (2 / 3)) (fun x => E.eval x - g x) ≤ εI + εR := by
  have hw : ∀ J ∈ ([(0, 0)] : List (ℕ × ℤ)), mesh J.1 ≤ (1 : ℝ) := by
    intro J hJ
    simp only [List.mem_singleton] at hJ
    subst J
    norm_num [mesh]
  have hc := certified_refinement_external (by norm_num : (1 / 3 : ℝ) < 2 / 3)
    hεI hεR (by simp : ([(0, 0)] : List (ℕ × ℤ)).Pairwise DisjInt)
    thirds_cover hw hMstar
  obtain ⟨_, _, _, _, _, hv, hcorr⟩ := hc.2 L hL
  obtain ⟨v, hv, hne⟩ := hv
  obtain ⟨hg, _, herr⟩ := hcorr v hv hne
  exact ⟨cellInterp L.toFinset (fun t => (v t : ℝ)), hg, herr⟩

end PendenciasParte1.CoberturaExterna

#print axioms PendenciasParte1.CoberturaExterna.projected_certificate_sound
#print axioms PendenciasParte1.CoberturaExterna.refinement_contract_external
#print axioms PendenciasParte1.CoberturaExterna.certified_refinement_external
#print axioms PendenciasParte1.CoberturaExterna.thirds_success

