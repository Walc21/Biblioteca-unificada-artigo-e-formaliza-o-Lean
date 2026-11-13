# Status da formalização (Lean 4 / Mathlib)

Tudo abaixo compila sem `sorry` e usa só os axiomas padrão (`propext`, `Classical.choice`, `Quot.sound`).

## Dependências (seções 2–3) — construídas do zero
- `Lib/Indexing.lean`: pareamento de Cantor (bijeção, inversa com `Nat.sqrt`, cota), `Z`, altura, `|ℚ_H| ≤ 3H²`,
  `|ℚ_H| ≥ H²/4` (prova elementar, sem Mertens), enumerações por altura `Q`, `Q*` e postos `< 3H²`.
- `Lib/Library.lean`: átomos `(k,m,y₀,s)`, endereço `Γ⁻¹` (bijeção), interface global `Γ`, Lema 3.4, Teorema 3.5 (injetividade de `Γ`), cascas `𝓛_H` com cardinalidade exata.
- `Lib/Assembly.lean`: Definição 4.1 (`Asm`), `𝒜_{N,H}` (Def. 7.13), ReLU, distância uniforme.
- `Lib/Calculus.lean`: cota de Taylor de 1ª ordem e erro de interpolação `M(x-p)(q-x)/2`.

## Alvos provados
- Teorema 4.3 (ambas as direções), Proposição 4.4, Proposição 4.5.
- Teorema 7.1, Lema 7.2, Proposição 7.3, Teorema 7.4, Definição 7.6 + Teorema 7.7.
- Computabilidade de `Γ♯` nos dois sentidos: `Sec7/SharpComputable.lean` (`GammaSharp_computable`; funções Lean executáveis iguais a `Γ♯`/`n♯` e mutuamente inversas — não o predicado `Computable` do Mathlib).
- Lema 7.11, Definição 7.13, Proposição 7.14, classe `𝓕_{R,M}`, Lema 7.15.
- Teorema 7.9: `Sec7/Serialization.lean` (`serialization_sharp`, `serialization_gamma`); códigos em `Sec7/Bits.lean`.
- Teorema 7.12: `Sec7/Formats.lean` (`formats_comparison`, `formats_length_bounds`, `formats_family`).
- Teorema 7.16: `Sec7/Simultaneous.lean` (`simultaneous_control`); interpolantes em `Sec7/Interp.lean`, cadeias em `Sec7/Chain.lean`.
- Corolário 7.17: `Sec7/Precision.lean` (`precision_height`; ordens `O(·)` para `0 < ε ≤ 1`).
- Teorema 7.18: `Sec7/Entropy.lean` (`entropy_codebook`); cota inferior em `Sec7/EntropyLower.lean`, codebook em `Sec7/EntropyUpper.lean`.
- Definição 7.19, Proposição 7.20, Proposição 7.21.
- Definição 7.22, Teorema 7.23, Proposição 7.24: `Sec7/Catalogs.lean` (`Cat`, `catalog_finite_canonical`, `catalog_truncation`).

## Ainda não formalizados
Nenhum dos alvos listados acima ficou pendente.

## Observações sobre o texto
- Nenhum erro matemático encontrado nos resultados formalizados até agora.
- Ajuste de leitura: em (24) aparece `g(t₀)`, mas `t₀` pode estar fora de `K`; formalizamos como `ℓ₀(t₀)` (valor da primeira peça).
- O limite inferior de `|ℚ_H|` vale com `c₁ = 1/4` para todo `H ≥ 1` por contagem elementar; não é preciso usar Mertens.
