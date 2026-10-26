# Exact spectral-chromatic counterexample certificate

This package proves exactly the original submitted negative declaration `AouchicheHansenStevanovic.SpectralChromatic.table1_upper` in PR7386. It uses the actual Mathlib graphs T(5,2) and T(5,3), their actual adjacency matrices and algebra spectra, proper colorings, cliques, connectivity and the natural ceiling of sqrt(5). The resulting objective values are sqrt(6)-2 and sqrt(5)-2. The corrected universal optimizer and equality cases are not proved here.

## Reproduce

Use the committed lean-toolchain and lake-manifest.json (Lean4.33.1; Mathlib0df444a360eaa60ab8c11dca51a86af692955474), then run `bash Proofs/SpectralChromatic/check.sh`. The original three admitted statements are retained as placeholders; they are not dependencies of the full proof. Both proof modules compile with warningAsError=true, autoImplicit=false and relaxedAutoImplicit=false.

## Exact source and verification scope

The statement module on this certificate branch is a standalone import overlay of upstream PR head e85cf5c47e914f4b140c8b029bc9878b62dbae30. The only differences are replacing the umbrella FormalConjecturesUtil import with the explicitly listed pinned Mathlib imports and removing three category/AMS attributes. All other source characters, including every mathematical definition, namespace, hypothesis and complete target type, are identical. OriginalSource.txt preserves the original source. verify_source_overlay.py checks these exact transformations. The upstream PR retains its original imports and metadata.

local-success-receipt.json records the observed local checks. The full theorem has exactly propext, Classical.choice and Quot.sound. ExactAudit proves type equality in this replayable overlay environment, rejects an unrelated proposition and shows sorryAx in the original admitted declaration as a negative control. No native_decide or custom axiom is used.

The additional canonical-original-import run40323167258 is still queued, as recorded in the receipt. It must not be described as passed. This standalone kernel certificate and its source comparison are separate evidence from that queued CI, the upstream full-project build, independent mathematical review and historical novelty.

Source: the order-five comparison on page6 of Gebendorfer's 7August2026 manuscript, in the archive linked by the original statement. The original printed-table source-access limitation is retained.
