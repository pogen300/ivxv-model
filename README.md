# ivxv-model
Models IVXV Specification in TLA+

## How to run
- Use VSCode TLA+ extension
- Translate Pluscal to TLA+: Open a .tla file -> Open command palette -> `TLA+: Parse Module`
- Check model with TLC: Open the corresponding .cfg file -> Open command palette -> `TLA+: Check model with TLC`

## Modules
The IVXV protocol is divided into the following modules:

| Module | Purpose |
| --- | --- |
| `IVXVPrimitive.tla` | Symbolic crypto primitives, e.g., hash, cert, threshold settings |
| `IVXVData.tla` | Data structures |
| `IVXVHelper.tla` | Helper functions |
| `IVXVConfig.tla` | Secrets and election config used by the model. |
| `IVXVChannel.tla` | Communication channels between participants |
| `SetupPhase.tla` | Setup phase |
| `VotingPhase.tla` | Voting phase |
| `TallyPhase.tla` | Tally and audit phases |

## Model
### Version
This model is based on the following repositories and commits:

- [`ivxv`](https://github.com/valimised/ivxv/tree/2785872f84dffb56bbecc41b096a7ee0f2876e64) (`2785872`): core IVXV infrastructure, including server-side code for CS and PA, and application code for KA and AA. This repository also contains demo election configurations, logs, and official documentation used to infer protocol participants, security properties, and workflows that are not fully specified in the publicly accessible implementation.
- [`ivotingverification`](https://github.com/valimised/ivotingverification/tree/53ea2d4e28863c1be722214ee0469a6d94c7f315) (`53ea2d4`): Android VVD source code for self-verification.
- [`ios-ivotingverification`](https://github.com/valimised/ios-ivotingverification/tree/4230518d9f659aea056f17f95261173d68356f25) (`4230518`): iOS VVD source code.
- [`ivxv-mixnet-adapter`](https://github.com/valimised/ivxv-mixnet-adapter/commit/d40a9f3bfc1ecc8b6924e054a1c83a4d84164d2c) (`d40a9f3`): wrapper code for Verificatum mixers, including conversion from IVXV ballots to Verificatum group elements.

### Overview
See `doc/scope.md` for the model scope and the mapping between model modules and the IVXV specification. The current model is split into 3 phases:
- setup
- voting
- tally and audit

Each phase is modelled as a TLA+ specification with its own inputs, outputs, and invariants. Ideally (in an end-to-end model), a later phase should consume data produced by earlier phases rather than directly re-reading model constants, especially if these data have been exchanged in a previous phase. For example, voting phase participants should use the public election configuration shared by EA during setup, and tally phase should consume the ballot and registration exports established during voting phase.

The current model aims to approximate this end-to-end behaviour via `IVXVConfig.tla`, which contains expected phase outputs used to bridge different phases. For example, `StageTTL, VerifyWindow, VoterList` are defined in `IVXVConfig.tla`. In `SetupPhase.tla`, EA process directly reads them to create a `CSConfig` to share with the CS process. Invariants in `SetupPhase.tla` checks that the config owned by CS after the phase completes matches `ExpectedCSConfig` (defined in `IVXVConfig.tla` as the phase output). Then, in `VotingPhase.tla`, CS process is initialized with `ExpectedCSConfig` instead of using a separate input that isn't bind to the previous phase.
