# Model Scope
## 0. Scope summary
### Omitted
- encoding/serialization, e.g. DER to ASN.1 conversion
- file stucture checks, e.g., on BDOC
- CA chain validation
- mixnet operation

### Partially modelled
- file-level details: models necessary fields of BDOC
- inter-phase export/import conversion
- ciphertext semantics: symbolic
- primitives: some primitives, e.g., threshold decryption, is more abstracted than the rest

### Assumptions
- setup phase is honest
- all data structure are well-formed: necessary fields are either present or left empty.
- 1 election question
- ciphertext validation (IsValidCiphertext) for CS, VVD, PA are consistent and sufficient
- primitives are secure

## 1. Primitives
- [x] 65 Secure Primitives - TBD

## 2. Data Struct
### Modelled

- [x] 69 BDOC - Modelled as `[ct, cert, sig, tbs]`
- [x] 71 X509Certificate 116 - cert is modelled abstractly with `Cert()` and `CertPK()`.
- [x] 72 StorageDB - modelled as `csBallotStore, csSessionStore, csLatest`
- [x] 73 AuthenticateSession
- [x] 74 GetValidSession - `StoreLookup`
- [x] 75 SessionData
- [x] 78 StoredVote - modelled StoredVote has extra tsp/ocsp fields (in spec, they are stored separately in storageDB). This is to abstract the conversion between CS storage format to BallotFileRecord (CS export)
- [x] 79 LatestVote
- [x] 81 SmartCardData
- [x] 82 CheckBallotResult
- [x] 83 Ballot
- [x] 84 Voter
- [x] 85 VoterList - modelled in TallyPhase as Voter elements keyed by voterId
- [x] 86 DecryptedVote
- [x] 87 VoterBallot
- [x] 88 CheckedBallotbox - modelled as the set of `VoterBallot` (see `CheckTool_BuildCheckedBB`)
- [x] 89 AnonBallotbox - modelled as the set of `AnonVote` (see `AnonTool_AnonymizeBB`)
- [x] 91 BallotFileRecord: modelled as  `StoredVote`
- [x] 92 BallotResponse
- [x] 93 DecryptionProof
- [x] 94 PALogEntry
- [x] 95 PAErrorLogEntry
- [x] 96 OCSPResponse
- [x] 97 TSPResponse
- [x] 98 Tally - modelled as `ElectionResult.tally`.
- [x] 99 PlainBallotbox - modelled as `ElectionResult.plain`.
- [x] 101 ElectionResult

### Not Modelled
- [ ] 70 XAdESSignature - model signature as sig bytes
- [ ] 76 CandidateList - no data struct needed when we model Candidate as str
- [ ] 77 Candidate - Simplified to a hardcoded string
- [ ] 90 BTElement
- [ ] 80 ElGamalParameters 120 - group parameters are abstracted by the symbolic EG constructor.
- [ ] 100 ASN1Node
- [ ] 102 ShuffleProof

## 3. Functions

### Setup
- [x] `KeyAppInit`
- [x] `GenerateKeyShares`
- [x] `GenerateSignKeyShares`
- [x] `ShoupSign` - modelled as ideal threshold signing over a valid record-based share set.

### Voting
#### Send Ballot
- [x] `CreateSession` - merged into VerifyAndUpdateSessionStatus
- [x] `AuthenticateSession` - see `CS_RecvAuthStatusRes`
- [x] `VerifyAndUpdateSessionStatus`
- [x] `VoterChoices` - see `CS_RecvChoicesReq`
- [x] `CreateBDOC` - modelled by `UnsignedVoteBDOC` and later `SignedBDOC`
- [x] `CreateAuthToken`
#### Confirm Ballot
- [x] `OpenAuthToken`
- [x] `VerifyBallot` - modelled inline in `CS_RecvVoteReq`
    - [ ] `VerifyBDOC`
    - [ ] `IsValidCiphertextCS`
- [x] `StoreBallot` - modelled inline as CS writing ballot into `csBallotStore`
- [x] `VerifyRegistration` - modelled by `VerifyTSPCS` and `VerifyTSPCS`
    - [x] `VerifyTSPCS`
    - [x] `VerifyOCSPCS`
#### Verify Ballot
- [x] `VerifyRequestedVote` - see `CS_RecvVerifyReq`
    - [ ] `GetVerificationStats`
    - [x] `GetVerification` - see `CS_RecvVerifyReq`
- [x] `ValidateBallot`
    - [x] `VerifyTSPVVD`
    - [x] `VerifyOCSPVVD`
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
    - [x] `SumValidInvalid` - inlined in `CSExportMatchesPALogs`
