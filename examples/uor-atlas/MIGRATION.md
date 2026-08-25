# Atlas migration provenance

The one-time Atlas migration closed at repository commit
`f972285fab4564c1a4231fe3d6efdb776b5becc7`. At that checkpoint the
independently authored Lean implementation had Git tree
`71fc050796816009ea665ceb87d6687967947906`: 71 files, including 68 Lean
files. The native source tree had Git tree
`79c321296059eaa4142fcbf3e98965f7f5866e61` and contained 66 source modules.

The exhaustive `conformance_vr_19` comparison at that commit built the pinned
Lean implementation, exported every semantic module afresh, and compared the
result with `examples/uor-atlas/src` byte for byte. It passed in 1,019.88
seconds. The conversion accounted for 5,577 source declaration records: 5,519
native environment declarations and 58 private source-compiler implementation
records retained only as hashed provenance.

GitHub Actions run `32799526580`, job `97657516155`, then verified the native
graph under `leanprover/lean4:v4.32.1`. Lean elaboration, same-kernel
`leanchecker` replay, and the exact axiom audit all succeeded, producing
attestation `17b300947fd43f09ac29336dff8bd61ba984e737f3bfa74c0b22dd3a2296259c`.
Artifact `9549590620` had SHA-256
`db98c5d6f6ad2ecdb6f92da9f8d65fb306bcf14ddcb24356882ce94ac083f5d1`
and contained 267 normalized verification records. The axiom output contains
5,519 declaration records in 5,521 physical lines because one declaration is
wrapped across continuation lines; the failed job conclusion came only from a
shell assertion that counted physical lines as declarations.

The native checkpoint identities were:

- build ID `b613e6e5ce11924d546d51701419c55d69e66fb71ae8c7379d3dea390b4d4bdd`;
- source ID `1e378f46301f062082f2cdd0c22bcea7fdf43bd88a364b4cdc251499f638241c`;
- semantic ID `81ff612be4fa60f29943cb909f939621a264c89b495b4df9f1ba7d2de6bfb79f`;
- compiler-semantics ID `1f42a353eb56ba7b72d8f6850c541940facc35033582a71bd09c2717fdde6601`.

With that equivalence established, the migration oracle and its exporter were
removed. They are historical inputs recoverable from the checkpoint commit,
not release inputs. `VR-19` now enforces the permanent condition: the native
source is rooted, every source module has exactly one generated Lean module,
public imports remain inside `Init` and that graph, `Lean` is the sole private
backend-support import, and no independently authored Atlas Lean implementation
exists in the release tree.
