# Imagesnippets Materialize Ops

The `imagesnippets` Stage 2 materializer now supports:

- resume from existing `source-info.ttl` / `data.hdt`
- incremental `materialize-progress.txt`
- append-only `materialize-errors.log`
- TOC rebuild from existing on-disk state

## Important operational note

Detached background jobs launched from the Codex tool environment may be reaped
when the tool session exits, even if started via `nohup`.

For a long-running unattended pass, run the launcher from a normal user shell:

```bash
cd /home/danbri/working/sandbox/foaf25/codex/factoidal
tools/run_imagesnippets_materialize_resume.sh
```

## Logs

Tail:

```bash
tail -f /mnt/t/IS_Corpus_v2/materialize-run.log
tail -f /mnt/t/IS_Corpus_v2/materialize-progress.txt
tail -f /mnt/t/IS_Corpus_v2/materialize-errors.log
```

## Quick counts

```bash
find /mnt/t/IS_Corpus_v2 -maxdepth 3 -name data.hdt | wc -l
find /mnt/t/IS_Corpus_v2 -maxdepth 3 -name source-info.ttl | wc -l
```
