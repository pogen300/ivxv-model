# Model Scope

This document describes the scope of the TLA+/PlusCal model and maps names from the reconstructed IVXV protocol specification to names used in the model.

The model is split into three phase modules: `SetupPhase.tla`, `VotingPhase.tla`, and `TallyPhase.tla`. The phase modules are connected through scenario constants in `IVXVConfig.tla`; invariants check that each phase's produced artefacts match the corresponding expected inputs of later phases.

## Scope Summary

### Modelled

Protocol phases are modelled at the protocol-data-flow level:
- Setup: EA, CS, KA, KH, VCD, VVD, and PA message flow.
- Voting: Voter, VCD, CS, IDP/Provider, Sign, Reg, and VVD message flow.
- Tally: EA, PA, Mixer, KH, and KA processing flow.
- Audit: AA checks are represented as invariants over produced artefacts.

We model symbolic cryptographic binding between signatures, certificates, encrypted votes, TSP responses, OCSP responses, and audit artefacts.

### Abstracted
- file-level details: only models necessary fields of BDOC
- inter-phase export/import conversion
- ciphertext semantics: symbolic
- primitives: some primitives, e.g. threshold decryption, are more abstracted than the rest
- TSP/OCSP responses: modelled symbolically, only fields needed for binding and ordering are represented
- PA and AA logs: modelled at the granularity needed for current invariants

### Omitted
- encoding/serialization, e.g. DER to ASN.1 conversion
- file structure checks, e.g. on BDOC
- some `CheckBallotResult` cases for low-level parsing or malformed-input paths
- CA chain validation
- mixnet operation
- exact data-channel security

## Primitives

| Name in IVXV | Name in model | Note |
|---|---|---|
| Secure primitives | `Hash`, `Sign`, `Verify`, `PubKey`, `AEADEnc`, `AEADDec` | Symbolic, perfect primitives. No concrete encoding, randomness distribution, or digest algorithm variants. |
| X.509 certificate issuing and verification | `Cert`, `X509Cert`, `IssueX509Cert`, `VerifyX509Cert`, `VerifyTrustedX509Cert`, `CertPK` | Models issuer relation and certificate signature. Full PKIX chain validation is abstracted. |
| ElGamal encryption | `EGEnc`, `EGDec`, `EGCheckRandomness`, `IsValidEGCiphertext` | Symbolic encryption with explicit randomness for VVD verification. No ModP arithmetic or ASN.1 parsing. |
| Decryption proof | `DecryptionProof`, `VerifyDecryptionProof` | Symbolic proof object tying ciphertext to plaintext and witness. |
| Threshold key generation and recovery | `ThresholdParams`, `ThresholdShare`, `ThresholdShareStore`, `RecoverThresholdKey` | Models threshold count and distinct key-holder identities. Share arithmetic is abstracted. |
| Shoup threshold RSA signing | `ShoupSign` | Idealised as threshold recovery plus signature. Recombination arithmetic is not modelled. |
| Verificatum shuffle | `IdealMix` | Treated as an ideal black box in the baseline model. |
| Store operations | `StoreLookup`, `StorePut`, `StoreDelete` | Abstract map helpers used for participant stores. |
| List/map/set helper operations | TLA+ sets/functions and helper definitions | Duplicate-sensitive list semantics are only modelled where needed, e.g. indexed Reg export and recurrent response handling. |

## Data Structures

| Name in IVXV | Name in model | Note |
|---|---|---|
| `BDOC` | `BDOC(ct, signerCert, sig, tbs)` | Collapses ballot file list and XAdES signature list to one ciphertext, one signer certificate, one signature, and signed data. |
| `BallotFile` | | Abstracted into `BDOC.ct`. Filename and multi-ballot structure are not represented. |
| `XAdESSignature` | | Abstracted into `BDOC.sig` and `BDOC.signerCert`. Signed-properties details are not represented. |
| `X509Certificate` | `Cert`, `X509Cert` | Keeps public key, personal identifier, issuer certificate, and certificate signature. Common name and serial-number fields are omitted. |
| `StorageDB` | `csSessionStore`, `csBallotStore`, `regStore`, `regOcspStore` | Split into participant-local stores rather than one global database. |
| `SessionData` | `SessionData`, `SessionCtx` | Models session phase, expiry, token, identity, and pending voting context. |
| `VoterProfile` | `VoterRef` | Contains voter identifier and phone number for the modelled Mobile-ID-style flow. |
| `AuthToken` | `AEADEnc` output from `CreateAuthToken` | Token carries auth-derived certificate and issued vote identifier symbolically. |
| `DataToken` | | Not modelled separately. Current baseline does not model exact GetCert data-token binding. |
| `RegisteredBallot` | `RegisteredBallot` | CS-side registered ballot containing vote id, voter id, submitted time, registration time, BDOC, TSP/OCSP responses, verification count, and test-vote flag. |
| `CSConfig` | `CSConfig` | CS-specific election config, TTL, verification window/count, TSP slack, and voter list. |
| App configs (`VVDConfig`, `PAConfig`, `KAConfig`, `AAConfig`, `MixerConfig`) | `PublicElectionConfig` | Model shares a common public config across non-CS participants. App-specific flags are omitted unless used by invariants. |
| `CandidateList` | `CandidateList` constant / `choices` field | Simplified to one global choice set. District-specific candidate maps are omitted. |
| `Candidate` | choice strings | Candidates are modelled as strings such as `"Alice"` and `"Bob"`. |
| `Voter` | `Voter` | Keeps voter id, district, and parish. Name and other metadata are omitted. |
| `VoterList` | `VoterList` | Map from voter id to `Voter`. |
| `SmartCardData` | `SmartCardData` | Contains key-holder id plus decryption and signing shares. |
| `ElGamalParameters` | `EGParams` / `ThresholdParams` | Concrete `p,q,g` group parameters are abstracted. |
| `CheckBallotResult` | error constants in `IVXVData.tla` | Models errors needed by the baseline PA path. Some low-level file/profile errors remain abstracted. |
| `Ballot` | `Ballot` | Normalised PA ballot with id, time, voter, and map from question to ciphertext. |
| `BallotRef` | `voterId`, `ballotId` fields in `PAErrorLogEntry` | Wrapper is omitted; fields are stored directly in log entries. |
| `BallotFileRecord` | `RegisteredBallot` in CS export | Export record is represented by the registered ballot stored by CS. |
| `BallotResponse` | `BallotResponse` | Contains the normalised `Ballot` and associated TSP response. It no longer carries reconstructed request data. |
| `RegLogEntry` | `RegLogEntry` | Request-only TSP entry. In the model this is an identity wrapper around `TSPReq`. |
| `TSPReq` | `TSPReq` | Contains symbolic message imprint `m` and nonce/signature `n`. Digest algorithm identifiers are omitted. |
| `TSPResponse` | `TSPRes` | Contains symbolic message imprint, nonce/signature, time, responder certificate, and responder signature. |
| `MessageImprint` | | Abstracted as the raw `m` field. Needed only for algorithm-mismatch attack extensions. |
| `TSPNonce` | | Abstracted as the raw `n` field. Needed only for algorithm-mismatch attack extensions. |
| `OCSPReq` / `OCSPCertID` | `OCSPReq` | Request is keyed by signer certificate directly. CertID construction is omitted. |
| `OCSPResponse` | `OCSPRes` | Contains request, status, time, responder certificate, and responder signature. |
| `CheckedBallotbox` | set of `VoterBallot` | Model uses sets rather than nested maps. |
| `VoterBallot` | `VoterBallot` | Contains voter id, set of ballots, and revocation flag. |
| `FilteredBallotbox` | set of `Ballot` | Contains the latest non-revoked ballots after PA filtering. |
| `AnonBallotbox` | set of `AnonVote` | Keeps district, parish, question, and ciphertext; nested IVXV map/list shape is abstracted. |
| `BTElement` | | Not modelled; ByteTree conversion is outside the baseline scope. |
| `ShuffleProof` | `ShuffleProof` | Minimal proof record with public key, input, and output. Verificatum internals are omitted. |
| `DecryptedVote` | `DecryptedVote` | Contains district, parish, question, ciphertext, and decryption proof/plaintext binding. |
| `DecryptionProof` | `DecryptionProof` | Symbolic proof object. |
| `PlainBallotbox` | set of `PlainVote` | Nested question-indexed plaintext ballotbox is abstracted to a set. |
| `Tally` | set of `TallyRow` | Counts choices per district/parish/question tuple. |
| `ElectionResult` | `ElectionResult` | Contains tally, plaintext ballotbox, valid proofs, invalid votes, and threshold signatures. Single-question abstraction. |
| `PALogEntry` | `PALogEntry` | Per-ciphertext log with time, hash, and voter id. |
| `PAErrorLogEntry` | `PAErrorLogEntry` | Error log with voter id, ballot id, and error code. |
| `RawBallotEntry` | `RawBallotEntry` | Audit helper record with ballot id, voter id, and ciphertext. |
| `ASN1Node` | | Not modelled. ASN.1 parsing is outside the symbolic abstraction. |

## Algorithms And Helpers

### Setup

| Name in IVXV | Name in model | Note |
|---|---|---|
| `TrustConfig` | `ExpectedPublicConfig`, trusted certificate constants | Trust-root container is folded into expected public configuration. |
| `KeyAppInit` | `KA_KeyAppInit` | PlusCal process step in `SetupPhase.tla`. |
| `GenerateKeyShares` | `GenerateKeyShares` | Symbolic threshold decryption-share generation. |
| `GenerateSignKeyShares` | `GenerateSignKeyShares` | Symbolic threshold signing-share generation. |
| `ShoupSign` | `ShoupSign` | Idealised threshold signing primitive. |
| Setup config distribution | `EA_ShareConfig`, `*_RecvPublicConfig`, `CS_RecvCSConfig` | Models data flow of generated keys/configs to participants. |

### Voting: SendBallot

| Name in IVXV | Name in model | Note |
|---|---|---|
| `CreateSession` | auth branch of `VerifyAndUpdateSession` | Session creation is folded into the common session helper. |
| `AuthenticateSession` | `CS_RecvAuthStatusRes` | Models provider-returned certificate/signature and auth-token minting. |
| `VerifyAndUpdateSession` | `VerifyAndUpdateSession`, `CanAdvance` | Models session phase progression, expiry, and token equality at current abstraction. |
| `NeedAuth` | inline in `VerifyAndUpdateSession` | Not a separate helper. |
| `NeedDataToken` | | Not modelled; data token omitted. |
| `SelectTTL` | `cfg.stageTTL` | Uses one stage TTL value rather than per-step TTLs. |
| `VoterChoices` | `CS_RecvChoicesReq` | Returns the configured choice set. District-specific choice-list lookup is abstracted. |
| `CreateAuthToken` | `CreateAuthToken` | Symbolic AEAD token over auth certificate and vote id. |
| `OpenAuthToken` | `OpenAuthToken` | Symbolic AEAD opening. The OB-12 implementation bug is not modelled. |
| `CreateDataToken` / `OpenDataToken` | | Not modelled separately. |
| `CreateBDOC` | `UnsignedBDOC`, `SignedBDOC`, VCD process steps | Closed-source VCD construction is inferred and modelled minimally. |
| `EncryptChoices` | `EGEnc` in `VCD_RecvChoice` | One selected choice encrypted under the election public key. |

### Voting: ConfirmBallot

| Name in IVXV | Name in model | Note |
|---|---|---|
| `VerifyBallot` | `CS_RecvVoteReq` | Inline checks for session/auth identity, signer identity, voter eligibility, signature, and ciphertext validity. |
| `VerifyBDOC` | `VerifyTrustedX509Cert`, `Verify` | Symbolic certificate and signature checks. BDOC file/reference checks are omitted. |
| `IsValidCiphertextCS` | `IsValidEGCiphertext` | Symbolic ciphertext check. Participant-specific parsing differences are omitted. |
| `RegisterBallot` | `CS_RecvVoteReq`, `CS_SendTSPReq`, `CS_SendOCSPReq` | Constructs and sends symbolic TSP/OCSP requests. |
| `VerifyRegistration` | `CS_RecvTSPRes`, `CS_RecvOCSPRes` | Verifies TSP/OCSP responses and completes registration. |
| `VerifyTSPCS` | `VerifyTSPCS` | Checks response request fields, responder certificate, nonce signature, timestamp slack, and response signature. Algorithm identifiers are omitted. |
| `VerifyOCSPCS` | `VerifyOCSPCS` | Checks OCSP request equality, good status, responder certificate, and response signature. |
| `StoreRegisteredBallot` | `CS_RecvOCSPRes` | Stores a `RegisteredBallot` only after qualification succeeds. |

### Voting: VerifyCast

| Name in IVXV | Name in model | Note |
|---|---|---|
| `VerifyRequestedVote` | `CS_RecvVerifyReq` | Models lookup by vote id, verification window/count, latest-only logic, and verification counter update. |
| `GetVerificationStats` | inline in `CS_RecvVerifyReq` | Not a separate helper. |
| `LatestRegisteredBallot` | `LatestRegisteredBallot` | Chooses latest registered ballot by registration time and vote-id tie-break. |
| `GetVerification` | `CS_RecvVerifyReq` | Returns the stored BDOC and qualification responses if verification is allowed. |
| `ValidateBallot` | `ValidateBallot`, `VVD_RecvVerifyRes` | Checks BDOC, TSP, and OCSP before displaying signer identity. |
| `VerifyTSPVVD` | `VerifyTSPVVD` | Symbolic TSP verification. Algorithm mismatch behaviour is not expressible in the baseline model. |
| `VerifyOCSPVVD` | `VerifyOCSPVVD` | Symbolic OCSP verification. |
| signer identity display | `VVD_RecvVerifyRes`, `Voter_ApproveDecrypt` | Models pre-decryption display of signer identity and voter approval. |
| `DecryptVotes` | `RecoverChoiceByRand`, `VVD_RecvDecryptApproval` | Recovers the choice by checking VCD-supplied randomness against the ciphertext. |
| `IsValidCiphertextVVD` | `IsValidEGCiphertext`, `EGCheckRandomness` | Symbolic check only. |
| `DecodeModPElement` | | Omitted; plaintext is a symbolic choice string. |
| `ExportBallots` | `CSExportOfStore`, `ExpectedVotingExport`, `EA_ExportVotingData` | Export represented by expected phase output and tally input. |

### Tally: PA

| Name in IVXV | Name in model | Note |
|---|---|---|
| `CheckTool` | `PA_CheckTool`, `CheckTool_BuildCheckedBB`, log helpers | Models ballot parsing, Reg consistency, and PA logs at symbolic level. |
| `LoadBallotFileRecord` | `LoadBallotFileRecord` | Parses CS export and removes recurrent responses by TSP message imprint. |
| `LoadRegData` | `LoadRegData` | Parses request-only Reg export and detects duplicate request imprints. |
| `CheckCollectorRegConsistency` | `CheckCSRegConsistency`, `CheckRegCSConsistency` | Matches CS TSP response imprints against Reg request imprints. |
| `CreateBallotResponse` | `CreateBallotResponse`, `CreateBallotResponseErr` | Builds normalised PA ballot response after symbolic validation. |
| `GetTrustedBDOC` | part of `CreateBallotResponseErr` | Not split into a separate helper. |
| `VerifyTSPPA` | part of `CreateBallotResponseErr` | Checks TSP response and nonce signature symbolically. |
| `CreateBallot` | `CreateBallotResponse` | Creates a normalised `Ballot`. Filename-to-question parsing is abstracted. |
| `CreatePALogEntry` | `CreatePALogEntry` | Hashes ciphertext for PA logs. |
| `CreatePAErrorLogEntry` | `CreatePAErrorLogEntry` | Creates error-log entries. |
| `FilterBallotbox` | `PA_FilterBallotbox`, `KeptBallots`, `LatestBallot` | Keeps each voter's latest non-revoked ballot. |
| `IsValidCiphertextPA` | | Omitted from `KeptBallots`; ciphertext validation is symbolic and assumed consistent. |
| `AnonymizeBallotbox` | `PA_AnonymizeBallotbox`, `AnonTool_AnonymizeBB` | Removes voter attribution and keeps district/parish/question/ciphertext tuple. |

### Tally: Mixer And KA

| Name in IVXV | Name in model | Note |
|---|---|---|
| `BallotboxAsBT` | | Omitted; ByteTree conversion is outside the baseline scope. |
| `BTAsBallotbox` | | Omitted. |
| `PublicKeyAsBT` | | Omitted. |
| `Mix` / `MixerTool` | `Mixer_Mix`, `IdealMix`, `ShuffleProof` | Mixnet is treated as an ideal black box. |
| `DecryptAndTally` | `KA_DecryptAndTally` | Recovers key, decrypts mixed ballotbox, computes result, and signs outputs. |
| `RecoverDecryption` | `Tally_RecoverElectionSK`, `RecoverThresholdKey` | Symbolic threshold recovery. |
| `DecryptBallotbox` | `Tally_DecryptBB` | Symbolic decryption plus proof generation. |
| `ComputeElectionResult` | `Tally_ComputeElectionResult`, `BuildTally`, `BuildPlainBB` | Counts valid symbolic plaintext choices. |
| `IsValidChoice` | `ValidDecVotes`, `InvalidDecVotes` | Validity is membership in the configured global choice set. |

### Audit

| Name in IVXV | Name in model | Note |
|---|---|---|
| `VerifyAuditInput` | `Inv_AA_VerifyAuditInput` | Modelled as an invariant over final artefacts. |
| `ConvertTool` | | ByteTree conversion omitted. |
| `MixerTool` | `ShuffleProof`, `IdealMix` | Shuffle verification is abstracted. |
| `DecryptTool` | `Inv_AA_DecryptTool`, proof helpers | Checks symbolic decryption proof consistency, valid/invalid partition, and tally consistency. |
| `VerifyPlaintexts` | `VerifyPlaintexts` | Checks symbolic proof validity and plaintext validity classification. |
| `VerifyValidConsistency` | `VerifyValidConsistency` | Checks valid plaintext/proof consistency. |
| `VerifyTally` | `VerifyTally` | Recomputes tally from plaintext ballotbox. |
| `IntegrityTool` | `Inv_AA_IntegrityTool`, log consistency helpers | Checks PA input/output/log consistency at flat set/hash level. |
| `SumValidInvalid` | `CSExportMatchesPALogs`, `AcceptedRawEntries`, `ErrorRawEntries` | Inlined into audit consistency helpers. |

## Checked Properties

| Config | Checked properties |
|---|---|
| `SetupPhase.cfg` | EA config built from expected inputs; configs delivered to participants; threshold shares recover election/signing keys; termination. |
| `VotingPhase.cfg` | VVD accepts only the latest registered ballot retained by CS; verified ballots remain evidenced by CS or Reg unless both drop evidence; honest CS and Reg exports match the scenario; termination. |
| `TallyPhase.cfg` | Audit input consistency; DecryptTool consistency; IntegrityTool consistency; honest EA input relay; PA keeps latest non-revoked ballots; voter-specific tally/revocation expectations; Alice wins in the concrete scenario. |
