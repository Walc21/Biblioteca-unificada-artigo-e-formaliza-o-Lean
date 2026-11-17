# Verificação numérica

Seis programas em Python, listados na tabela abaixo, acompanham o artigo e são executados por `reproduzir_tudo.py`. Eles **não fazem parte das demonstrações**: nenhum
teorema, lema ou proposição do volume depende deles. Registram verificações de **instâncias finitas** em
aritmética exata (`fractions.Fraction`) e geram tabelas e figuras. A prova formal está em [`lean4/`](../lean4).

| Programa | Onde aparece no artigo | Resultados registrados |
|---|---|---|
| `reproduzir_curvas.py` | Partes I e III: indexação, complexidade de endereços, catálogos finitos, equivalência ReLU, aritmética intervalar, formatos de codificação (4096 montagens), tabelas do refinamento adaptativo e figuras da Parte I | `resultados_curvas.json` |
| `seletor_dinamico_exato.py` | Parte III, «Validação computacional exata» (tabelas de comparação e de auditoria e figuras do estado de fronteira e da comparação de seletores) | `resultados.json` |
| `constante_diadica.py` | Parte III, constante quadrática, fases e envelope $C^2$ (figuras da constante, das fases e do envelope) | `resultados_constante_diadica.json` |
| `espacos_aproximacao.py` | Parte IV, auditoria racional das alturas (tabela de alturas e figura das agendas) | `resultados_espacos_aproximacao.json` |
| `reversibilidade_regularizada.py` | Parte IV, «Validação executável» (2952 idas e voltas, 84 redes quantizadas, 1260 instâncias) | `resultados_reversibilidade.json` |
| `restricoes_rede.py` | Parte IV, figura de restrições de rede | `resultados_restricoes_rede.json` |

## Verificações complementares (fora de `reproduzir_tudo.py`)

Dois programas testam a lei de fase da Parte III (III.12.5–III.12.9). **Não são verificadores exatos no mesmo
sentido** dos seis acima e não sustentam nenhuma prova; ficam fora de `reproduzir_tudo.py` e não têm `.json`
registrado.

| Programa | O que faz | Aritmética |
|---|---|---|
| `lei_fase_experimento.py` | Compara $\sqrt\varepsilon\,n_f(\varepsilon)$ com $\Psi_f$ e o intervalo de $N^2E_N$ com $[m_f^2,M_f^2]$ para nove funções $C^2$, incluindo zeros e mudança de sinal de $f''$, uma função afim em um intervalo e um patamar | ponto flutuante (`float`) |
| `lei_fase_exata.py` | Mesma comparação para $e^x$, $\ln(1+x)$, $x^3+x^2$ e um patamar $C^2$, com 40 dígitos e $\Psi_f$ em forma fechada; e quadráticas por partes com a árvore de limiar em `Fraction`, sem tolerância | `mpmath` (40 dígitos) e `Fraction` |

```bash
python3 verificacao/lei_fase_experimento.py 6000
python3 verificacao/lei_fase_exata.py              # precisao, atomo e racional; aceita um subcomando e Nmax
```

O segundo exige `mpmath` (já em `requirements.txt`) e leva cerca de 40 s.

Os `.json` são as saídas registradas na edição do artigo. Nos diagnósticos logarítmicos auxiliares há ponto
flutuante, e por isso não se exige identidade byte a byte desses campos entre plataformas.

## Como executar

```bash
python3 -m pip install -r verificacao/requirements.txt
python3 verificacao/reproduzir_tudo.py --output-root /tmp/biblioteca-verificacao
```

Execute os comandos acima na raiz do repositório. O segundo comando executa os seis programas,
com `assert` habilitado e backend gráfico `Agg`, cada um em uma subpasta própria. Interrompe no primeiro
erro e registra os códigos de saída, os caminhos dos resultados e os logs em `resumo_execucao.json`.
O estado `ok` indica que os seis processos terminaram sem erro e produziram JSON válido; os testes
de cada programa verificam instâncias finitas, com os escopos descritos na tabela.

Para executar um programa isolado:

```bash
python3 verificacao/constante_diadica.py --output-root /tmp/constante-diadica
```

Todos os programas criam os diretórios necessários dentro de `--output-root`, que pode ser uma pasta
nova. As tabelas TeX ficam em `artigo/secoes/`; cinco programas gravam resultados e figuras em
`reproducibility/selecao/`. O `reproduzir_curvas.py` grava `resultados.json`, `figures/` e
`artigo/secoes/` diretamente sob sua pasta de saída. Os nomes `artigo/secoes/` identificam as tabelas
geradas e não pressupõem uma pasta existente nas fontes do manuscrito. A execução completa mantém
saídas separadas para evitar colisões de nomes. No `seletor_dinamico_exato.py`, o padrão sem a opção é a
raiz do repositório; prefira sempre fornecer uma pasta de trabalho.

O registro de `reproduzir_curvas.py` foi versionado como `resultados_curvas.json`, para distingui-lo
do registro do seletor. Os resultados da edição original foram gerados com Python 3.12. Nos programas
que usam diagnósticos em ponto flutuante, diferenças nesses campos não implicam alteração das
igualdades racionais verificadas. Não execute os verificadores individuais com `python -O`, pois essa
opção desativa seus `assert`.
