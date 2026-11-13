# Compilação e validação das pendências

Codex e Antigravity estão autorizados a integrar provas prontas e executar todos os
builds e auditorias. As instruções consolidadas e o fluxo de reconstrução estão em
[AGENTS.md](../AGENTS.md) e [gemini.md](../gemini.md).

Na raiz, consulte o estado e execute o gate completo, aguardando sua conclusão:

```bash
export PATH="$HOME/.elan/bin:$PATH"
./compilar_pendencias/compilar_tudo.sh --so-status
./compilar_pendencias/compilar_tudo.sh --axiomas
```

O gate compila `Pendencias`, `PendenciasParte1` e `ValidationAll`, e audita axiomas.
Logs ficam em `compilar_pendencias/logs/<data-hora>/`. A descoberta de declarações
não substitui revisão de fidelidade; a cota impressa antiga de IV.5.4 é falsa; vale a versão corrigida.
Não baixe caches volumosos por rotina nem execute geradores históricos.
