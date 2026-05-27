# Model Scope
## 0. Scope summary
### Omitted
- encoding/serialization, e.g. DER to ASN.1 conversion
- file stucture checks, e.g., on BDOC
- CA chain validation
- mixnet operation
- exact data-channel security

### Partially modelled
- file-level details: models necessary fields of BDOC
- inter-phase export/import conversion
- ciphertext semantics: symbolic
- primitives: some primitives, e.g., threshold decryption, is more abstracted than the rest
- TSP/OCSP responses: modelled symbolically, only fields needed for binding and ordering are represented
- PA and AA logs: modelled at the granularity needed for current invariants

### Assumptions
- setup phase is honest
- all data structure are well-formed: necessary fields are either present or left empty.
- 1 election question
- ciphertext validation (IsValidCiphertext) for CS, VVD, PA are consistent and sufficient
- primitives are secure
- threshold key generation and Shoup signing are idealised unless a setup-phase property explicitly depends on share indexing or threshold failure

## 1. Primitives
- [x] 65 Secure Primitives

## 2. Data Struct
### Modelled

- [x] 69 BDOC - Modelled as `[ct, cert, sig, tbs]`
- [x] 71 X509Certificate 116 - cert is modelled abstractly with `Cert()` and `CertPK()`.
- [x] 72 StorageDB - modelled as `csBallotStore, csSessionStore`
- [x] 73 AuthenticateSession
- [x] 74 GetValidSession - `StoreLookup`
- [x] 75 SessionData
- [x] 78 RegisteredBallot
- [x] 79 LatestRegisteredBallot - `LatestRegisteredBallot`
- [x] 81 SmartCardData
- [x] 82 CheckBallotResult
- [x] 83 Ballot
- [x] 84 Voter - model currently uses `voterId`; paper now uses `id`. This is a naming difference unless field-level consistency is being checked.
- [x] 85 VoterList - modelled in TallyPhase as Voter elements keyed by voterId
- [x] 86 DecryptedVote
- [x] 87 VoterBallot
- [x] 88 CheckedBallotbox - modelled as the set of `VoterBallot` (see `CheckTool_BuildCheckedBB`)
- [x] 89 AnonBallotbox - modelled as the set of `AnonVote` (see `AnonTool_AnonymizeBB`)
- [x] 91 BallotFileRecord - modelled as export from `RegisteredBallot`
- [x] 92 BallotResponse
- [x] 93 DecryptionProof
- [x] 94 PALogEntry - modelled as per-ciphertext log entries with `t`, `h`, and `voterId`.
- [x] 95 PAErrorLogEntry - modelled with `voterId`, `ballotId`, and `err`.
- [x] 96 OCSPResponse
- [x] 97 TSPResponse - modelled as `m,n,t,cert,sig`
- [x] 98 Tally - modelled as `ElectionResult.tally`.
- [x] 99 PlainBallotbox - modelled as `ElectionResult.plain`.
- [x] 101 ElectionResult
- [x] RawBallotEntry

### Pending Alignment With Current Spec
- [ ] BallotRef.id_ballot - rename/alias old `id_vote`/ballot id usage consistently.

### Not Modelled
- [ ] XAdESSignature - model signature as sig bytes
- [ ] CandidateList - no data struct needed when we model Candidate as str
- [ ] Candidate - Simplified to a hardcoded string
- [ ] BTElement
- [ ] ElGamalParameters - group parameters are abstracted by the symbolic EG constructor.
- [ ] ASN1Node
- [ ] ShuffleProof
- [ ] MessageImprint - data structure relevant to IV-V3, not modelled as its too low level for this model.
- [ ] TSPNonce - data structure relevant to IV-V3, not modelled as its too low level for this model.

## 3. Functions

### Setup
- [x] `KeyAppInit`
- [x] `GenerateKeyShares`
- [x] `GenerateSignKeyShares` - idealised
- [x] `ShoupSign` - idealised

### Voting
#### Send Ballot
- [x] `CreateSession` - merged into VerifyAndUpdateSessionStatus
- [x] `AuthenticateSession` - see `CS_RecvAuthStatusRes`
- [x] `VerifyAndUpdateSessionStatus`
- [x] `VoterChoices` - see `CS_RecvChoicesReq`
- [x] `CreateBDOC` - modelled by `UnsignedVoteBDOC` and later `SignedBDOC`
- [x] `CreateAuthToken`
    - [x] auth-derived session identity update
#### Confirm Ballot
- [x] `OpenAuthToken`
- [x] `VerifyBallot` - modelled inline in `CS_RecvVoteReq`
    - [ ] `VerifyBDOC`
    - [ ] `IsValidCiphertextCS`
- [x] `RegisterBallot` - see `CS_RecvVoteReq`
- [x] `VerifyRegistration` - modelled by `VerifyTSPCS` and `VerifyOCSPCS`
    - [x] `VerifyTSPCS`
    - [x] `VerifyOCSPCS`
- [x] `StoreRegisteredBallot` - see `CS_RecvOCSPRes`
#### Verify Ballot
- [x] `VerifyRequestedVote` - see `CS_RecvVerifyReq`
    - [ ] `GetVerificationStats`
    - [x] `GetVerification` - see `CS_RecvVerifyReq`
- [x] `LatestRegisteredBallot` - `LatestRegisteredBallot`
- [x] `ValidateBallot`
    - [x] `VerifyTSPVVD`
    - [x] `VerifyOCSPVVD`
- [x] pre-decryption signer identity display and voter approval - see `VVD_RecvVerifyRes` and `Voter_ApproveDecrypt`
- [x] `DecryptVotes` - `RecoverChoiceByRand`
  - [ ] `IsValidCiphertextVVD`
  - [ ] `DecodeModPElement`
- [x] `ExportBallots` - `EA_ExportVotingData`

### Tally

#### PA
- [x] `CheckTool`
    - [x] `LoadBallotFileRecord`.
        - [x] `CreateBallotResponse`
            - [ ] `GetTrustedBDOC`
            - [x] `VerifyTSPPA`
            - [x] `CreateBallot`
    - [x] `LoadRegData`
    - [x] `CheckCollectorRegConsistency`
- [x] `CreatePALogEntry`
- [x] `CreatePAErrorLogEntry`
- [x] `FilterBallotbox`
    - [ ] `IsValidCiphertextPA`
- [x] `AnonymizeBallotbox`

#### Mixer
Skipped
- [ ] `BallotboxAsBT`
- [ ] `BTAsBallotbox`
- [ ] `PublicKeyAsBT`

#### Decrypt
- [x] `DecryptAndTally`
    - [x] `RecoverDecryption` - `Tally_RecoverElectionSK`
    - [x] `DecryptBallotbox` - `Tally_DecryptBB`
    - [x] `ComputeElectionResult` - `Tally_ComputeElectionResult`
        - [x] `IsValidChoice` - `ValidDecVotes`

### Audit
- [x] `VerifyAuditInput` - see `Inv_AA_VerifyAuditInput`
- [ ] `ConvertTool`
- [ ] `MixerTool`
- [x] `DecryptTool` - see `Inv_AA_DecryptTool`
    - [x] `VerifyPlaintexts` - inline
    - [x] `VerifyValidConsistency` - inline
    - [x] `VerifyTally` - inline
- [x] `IntegrityTool` -  see `Inv_AA_IntegrityTool`
- [x] `SumValidInvalid` - currently inlined in `CSExportMatchesPALogs`
