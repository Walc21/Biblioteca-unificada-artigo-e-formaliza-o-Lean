# Integração da normalização com a biblioteca

Integração compilada e auditada em 22/10/2026, com Lean/Mathlib 4.28.0.
As nove fontes recebidas da Parte I permanecem iguais às originais.
O projeto principal importa essas fontes pelo caminho `entradas/parte_1`;
o Artigo 2 continua com seu ambiente independente.

## Resultados novos

| Módulo em `Unified/SemanticBridge/` | Identificação demonstrada |
| --- | --- |
| `NormalizationAtoms.lean` | Equivalência concreta dos átomos; suporte, interior, reta, altura e cardinalidade das famílias |
| `NormalizationContracts.lean` | Transporte dos contratos; normalização sem aumentar recursos; classes locais e fortes iguais para α < β; erro global e condições de altura |
| `NormalizationEnumerations.lean` | Pareamentos, postos e enumerações; igualdade dos átomos para cada endereço das Fases 2 e 3 |
| `NormalizationClasses.lean` | Classes originais `Dyadic2.Asm`, `Fase3.IsAssembly` e `Dyadic.Lib.Asm`; restrição entre os tipos de função |
| `NormalizationErrors.lean` | Distância tipada, classes com os mesmos N e H e igualdade de `Montagens.Eloc`/`Econ` com `Dyadic.Lib.jointError` |
| `NormalizationReLU.lean` | Operador de extensão na classe efetiva da Fase 2; coincidência no domínio, pertencimento à classe consolidada e independência da testemunha |

São sete definições e 67 teoremas públicos novos. As declarações originais
não foram reescritas. A identificação das enumerações foi provada pelas
fórmulas dos postos e pelas inversas, sem inferir igualdade de índices a
partir apenas da sobrejetividade.

Os resultados de normalização usam intervalo não degenerado, α < β.
As classes com orçamento conservam os mesmos N e H, inclusive quando são
vazias. Os erros são comparados em ENNReal, mantendo o ínfimo vazio igual
a +∞. A função global prescrita não é substituída na normalização.

## Verificação

- `lake build SemanticAudit`: aprovado, 8.089 tarefas do grafo completo.
- `./executar.sh`: aprovado; 2.755 declarações e 2.196 teoremas próprios da
  biblioteca e suas pontes, sem axiomas fora da lista.
- `AuditoriaIntegracao.lean`: 3.265 declarações e 2.544 teoremas, incluindo
  também os módulos importados da Parte I e o agregador; sem axiomas fora da lista.
- Conferência pelo compilador de 191 nomes citados no mapa da base e da Parte I.
- Validação isolada integral repetida: nove módulos da Parte I e 31 do Artigo 2.

As únicas dependências axiomáticas encontradas foram `propext`,
`Classical.choice` e `Quot.sound`. As contagens da auditoria incluem
declarações auxiliares geradas pelo Lean e não devem ser somadas às dos
pacotes, pois há sobreposição de fontes importadas.

Registros: `evidencias/integracao_normalizacao_2026-10-22/resultado.json` e
`evidencias/validacoes/2026-10-22_19-20-19_L5Io81/`.

## Limites preservados no mapa

A integração encerra as ligações de tipos e de contratos da normalização.
Não formaliza os quatro teoremas do complemento nem os 19 resultados
matemáticos do Artigo 3. Também não transforma a compilação do Artigo 2
em prova automática de correspondência integral com seu TeX.

O enunciado antigo da equivalência ReLU ainda escreve g(t₀) em um contexto
em que t₀ pode estar fora de K. Essa diferença textual continua sinalizada;
o operador normalizado agora integrado tem a restrição ao domínio certificada.

## Nota sobre os registros citados

Os registros em `evidencias/` e o script `executar.sh` pertencem ao pacote de trabalho em que a
integração foi feita e não estão neste repositório. Aqui permanecem os módulos
`Unified/SemanticBridge/Normalization*.lean` e as auditorias `SemanticAudit.lean` e
`AuditoriaIntegracao.lean`, em `lean4/ambientes/base_integrada/` (o alvo `SemanticAudit` está no `lakefile.toml`).
