# ivxv-model
Models IVXV Specification in TLA+

## How to run
- Use VSCode TLA+ extension
- Translate Pluscal to TLA+: Open command palette -> TLA+: Parse Module
- Check model with TLC: TLA+: Check model...

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
See `doc/scope.md` for the model scope and the mapping between model modules and the IVXV specification. The current model is split into 3 phases:
- setup
- voting
- tally and audit

Each phase is modelled as a TLA+ specification with its own inputs, outputs, and invariants. Ideally (in an end-to-end model), a later phase should consume data produced by earlier phases rather than directly re-reading model constants, especially if these data have been exchanged in a previous phase. For example, voting phase participants should use the public election configuration shared by EA during setup, and tally phase should consume the ballot and registration exports established during voting phase.

The current model aims to approximate this end-to-end behaviour via `IVXVConfig.tla`, which contains expected phase outputs used to bridge different phases. For example, `StageTTL, VerifyWindow, VoterList` are defined in `IVXVConfig.tla`. In `SetupPhase.tla`, EA process directly reads them to create a `CSConfig` to share with the CS process. Invariants in `SetupPhase.tla` checks that the config owned by CS after the phase completes matches `ExpectedCSConfig` (defined in `IVXVConfig.tla` as the phase output). Then, in `VotingPhase.tla`, CS process is initialized with `ExpectedCSConfig` instead of using a separate input that isn't bind to the previous phase. 

The main limitation right now is that `VotingPhase.tla` only supports one vote, similar to the sequence diagrams in our specification. while `TallyPhase.tla` needs to consume data store that contains multiple ballots/entries (`ExpectedCSExport, ExpectedRegExport`)...