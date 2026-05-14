# Observed Baseline Raw Artifact

This directory freezes observed validation evidence for comparison only.
The `logs/` tree can be multi-gigabyte raw evidence and is intentionally
kept out of ordinary Git commits by the repository ignore policy.

Commit the metadata files in this directory, including `artifact_manifest.json`,
`file_hashes.json`, recovered manifests, and `workspace_state/` provenance.
Preserve or publish `logs/` as an external artifact or Git LFS object when
independent replay of the exact raw evidence is required.
