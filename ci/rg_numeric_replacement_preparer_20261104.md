# Reproduce the frozen numeric replacement preparation

This local preparer reads the complete actual API capture from 3 November 2026,
23:37 UTC, and five separately authenticated successful repairs. It does not
contact GitHub, dispatch a workflow, or alter proof sources. All 349 original
batch-plan hashes, the historical head plan, the original run descriptor and
the registered reference matrix are checked against the existing repository
files. The evidence directory contains actual metadata and authentication
reports; it does not duplicate those existing proof plans.

The captured coverage is **180/349** distinct complete batch origins:
52 master jobs, 123 reference-recovery jobs and five authenticated repairs.
There are 169 batches without a successful complete origin. Numeric166 has a
concrete running remainder job, but no successful origin is registered for it.
The master plan and its optional later `final` job never count as numeric
coverage. The whole `degreeOneLarge` family remains open.

Run the reproducible checks from the repository root:

```sh
python -B ci/rg_check_numeric_replacement_preparer.py
```

The checks use the frozen actual inputs and rejection controls. They do not
construct a synthetic full-coverage success. To regenerate the pending report
and exercise the hard gate against premature contract creation:

```sh
python -B ci/rg_prepare_numeric_replacements.py \
  --checkout . \
  --evidence-root . \
  --evidence ci/rg_numeric_replacement_evidence_20261104/index.json \
  --evidence-sha256 39c2cceb645117e98f530e2c68ef9cdec9005d1074379de0cbf350e43d17bc6e \
  --report ci/rg_numeric_replacement_preparer_20261104_pending.json \
  --seal /tmp/rg_numeric_replacements_must_remain_absent.json
```

For these inputs, exit status **2** is expected and no contract is written.
The report separately lists 96 existing original jobs whose required failure
conclusion is still pending and 27 permitted Wave2 original-job lookups. The
latter use only the established 90-case lookup rule. A later prepared contract
may retain those allowed lookups; the final collector must resolve each to one
actual failed or timed-out original job before accepting its replacement.
Contract preparation never replaces complete archive authentication or the
final kernel receipt.

Fresh metadata needs a newly frozen evidence index. A newly successful repair
also needs its real fixed run, job, head, artifact and authenticated report
registered explicitly. A running job, plan job or partial archive cannot be
promoted to successful coverage by this program.
