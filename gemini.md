# Instruções operacionais — formalização da biblioteca

Estas instruções valem para Codex e Google Antigravity/Gemini. `gemini.md` contém a
mesma orientação. O usuário autorizou o agente em execução a desenvolver todas as
frentes restantes, integrar provas, atualizar os arquivos centrais e executar a
compilação completa. Não há divisão exclusiva por agente nem processo, sessão,
mensagem ou entrega futura garantida: trabalhe com os arquivos existentes.

## Objetivo e estado inicial

Formalize fielmente os resultados restantes, integre contribuições concluídas,
atualize mapa, índices, relatório e PDF, e execute o gate global com axiomas.
Confira o estado efetivo com `python3 -I -B compilar_pendencias/status_pendencias.py`.
Na última conferência: 151 ambientes, 140 formalizáveis, 36 provas Lean, uma prova
textual sincronizada, 348 associações e cinco casos sem fechamento. IV.5.2 e IV.5.9
já foram integrados; seus arquivos e evidências são base de trabalho, não pendências.
As 97 correspondências herdadas não são 97 novas provas semanticamente auditadas.

- III.9.1: completar implementação densa com memoização real, contagem de tempo e
  memória, reconstrução e correspondência com `Cvar`. O rascunho existente
  `III9_1.lean` (rascunho enviado à lixeira do sistema em 13/11/2026; recuperável de lá) contém auxiliares parciais; inspecione-o e use-o
  quando útil, sem tratá-lo como prova completa.
- III.9.3: formalizar custos em bits, operações e normalização racionais, fluxos e
  desempate, e transportar as cotas de III.9.1.
- IV.5.5: formalizar a reversão aproximada quantizada, colisões, perturbação não
  plana e cotas de erro, folhas e altura. A prova textual usa reversão exata e uma
  estimativa própria; use apenas a cota corrigida de IV.5.4, nunca a impressa antiga.
- IV.5.6: formalizar regiões afins máximas de redes ReLU e aplicar IV.5.5.
- IV.5.4: FECHADO com o enunciado inverso corrigido (a cota impressa era falsa para
  R(x)=x, M=0, D=0, W=1). O texto atual traz
  log₂ H_can ≤ 5[(M+1)log₂(2W)+D+log₂(M+1)]; provas em
  `Pendencias/AlturaInversa.lean`, `FormaAncorada.lean` e `CodigoAncorado.lean`.
  O enunciado original e o contraexemplo ficam como evidência em `verificacao/IV_5_4/`
  e `verificacao/lean/ContraexemploAltura.lean`. IV.5.5 pode usar a versão corrigida.

## Regras de prova e desenvolvimento

Use a skill Lean 4 se estiver disponível. Leia cada enunciado e sua demonstração no
TeX atual pelo rótulo `map:...`; compare hipóteses, domínio e todas as conclusões.
Reutilize os módulos existentes e os trabalhos anteriores de ambos os agentes.
Desenvolva arquivos incompletos fora dos globs de `Pendencias/`, por exemplo em
`colaboracao/`; teste-os com `lake env lean` e caminho absoluto. Depois de prontos,
o próprio agente pode integrá-los em `Pendencias/` ou `PendenciasParte1/`, atualizar
imports, README, auditorias, mapas e registros, e rodar os builds globais.

Provas entregues não podem usar `sorry`, `admit`, novo `axiom`, `native_decide` ou
`@[implemented_by]`. Audite declarações com `#print axioms`; aceite apenas
`propext`, `Classical.choice` e `Quot.sound`. Definições novas exigem docstring com
correspondência ao TeX e justificativa de equivalência. Não enfraqueça enunciados,
não acrescente hipóteses ausentes nem promova lemas parciais como prova completa.
Registre bloqueios concretos e siga em trabalhos independentes. Uma prova Lean só
fecha um item após compilação, auditoria de axiomas e revisão de fidelidade ao TeX.

## Ambiente e integração

Lean e Mathlib estão fixados em 4.28.0; há `.lake` nos três ambientes. Não apague
caches ou logs e não baixe caches volumosos por rotina. A raiz não tem toolchain:

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd '/home/victor/BIBLIOTECA FINAL FORMALIZADA ARTIGO/lean4/ambientes/artigo_2'
lake --version
printf '%s\n' 'import Pendencias.Inversa' | lake env lean --stdin
```

Mantenha `fontes_originais/`, `historico/` e `pendencias_restantes/contexto/` como
fontes históricas. Não edite figuras ou PDF à mão; regenere derivados pelos scripts.
Não invente referências. Para incorporar novos fechamentos, atualize
`mapas/formalizacoes_pendencias.json`, preserve III.12.3 como prova textual, e faça
backup antes de reconstruir. A reconstrução existente sobrescreve derivados e
redefine o lakefile de `base_integrada`; depois restaure:

```toml
[[lean_lib]]
name = "PendenciasParte1"
globs = ["PendenciasParte1", "PendenciasParte1.+"]
```

Faça backup verificável antes de `python3 -I -B scripts/reconstruir.py` a partir
da raiz (não sobrescreva um backup existente):

```bash
tar --exclude=.lake --exclude=./compilar_pendencias/logs --exclude=./.git --exclude=./.agents --exclude=./.codex --exclude=./.aws -czf /tmp/biblioteca_backup_$(date +%Y%m%d-%H%M%S).tar.gz .
```

Depois da reconstrução, restaure o bloco acima; ative os ambientes TeX e Python existentes em
`/home/victor/Projetos/Arquivos_Extraidos_2026-11-13/tex-env.sh` e
`/home/victor/Projetos/Arquivos_Extraidos_2026-11-13/.venv/bin/activate`; rode
`pdflatex` e `latexmk -pdf` com `-interaction=nonstopmode -halt-on-error` em `tex/`.
Exporte figuras só se mudaram. Rode `python3 -I -B scripts/preencher_linha_lean.py .`,
`python3 -I -B scripts/verificar_entrega.py` e `python3 -I -B scripts/finalizar.py`
nessa ordem; finalização depois da última compilação PDF. O finalizador acrescenta
notas aos README gerados: reconstrua antes de repeti-lo. Confira o texto editorial:
o PDF anterior ainda registra seis casos sem fechamento, enquanto o mapa registra
cinco; sincronize esse dado com o estado real sem alterar enunciados matemáticos.

## Gate completo e entrega

Após integrar as formalizações possíveis, execute o gate completo, mesmo que seja
lento, aguardando o término real e preservando os logs:

```bash
cd '/home/victor/BIBLIOTECA FINAL FORMALIZADA ARTIGO'
export PATH="$HOME/.elan/bin:$PATH"
./compilar_pendencias/compilar_tudo.sh --axiomas
```

Ele abrange `lake build Pendencias`, `lake build PendenciasParte1` e a validação
`ValidationAll` no terceiro ambiente, além das auditorias previstas. Antes de rodá-lo,
confirme que cada ambiente contém `.lake/packages/mathlib`: o script tenta baixar
cache automaticamente se faltar. Diagnostique a ausência antes de iniciar downloads.

**Confira as auditorias separadamente:** o script atual não garante falha quando
`lake env lean` da auditoria retorna erro e pode apresentar apenas aviso se não
houver declarações. Execute `lake env lean AuditoriaPendencias.lean` em `artigo_2`,
`lake env lean AuditoriaPendenciasParte1.lean` em `base_integrada`, e
`lake env lean AuditoriaPacote.lean` em `parte_1`. Registre o código de saída de
cada comando, confirme que as declarações esperadas apareceram e examine todos os
axiomas, inclusive listas quebradas em várias linhas; aceite somente os permitidos.
Um resumo verde do script não substitui essas verificações.

Verifique os três resultados; registre o que foi recompilado e o que foi reutilizado
do cache. Não apresente um log antigo como nova execução. Depois,
execute `python3 -I -B scripts/verificar_entrega.py` e, com o ambiente PyMuPDF
ativado, `python3 -I -B verificacao/auditar_pacote.py final`; exija `erros: []`.
Confira cópias idênticas do PDF, páginas, sumário, referências, fontes e espelhos.
Atualize `STATUS_AUTOMATICO.md` e `LOG_TRABALHO.md` com comandos, resultados e
bloqueios, distinguindo provas Lean, provas textuais e correspondências herdadas.
Por último, gere e confira o manifesto:

```bash
find . -type f ! -name SHA256SUMS.txt ! -path './compilar_pendencias/logs/*' ! -path '*/.lake/*' | sort | sed 's#^\./##' | xargs -d '\n' sha256sum > SHA256SUMS.txt
sha256sum -c SHA256SUMS.txt --quiet
```

Se um item continuar bloqueado, descreva precisamente a causa e o trabalho feito;
não o declare provado. Peça decisão ao usuário quando a solução exigir alterar um
enunciado matemático, Não espere processos inexistentes e não
confunda edição de instruções com uma nova compilação ou prova.
