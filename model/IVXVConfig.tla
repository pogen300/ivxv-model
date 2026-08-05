------------------------------ MODULE IVXVConfig ------------------------------
EXTENDS Integers, IVXVPrimitive, IVXVHelper

\* Model secrets
ElectionSK == "electionSK"
ElectionSignSK == "electionSignSK"
TSPClientSK == "tspClientSK"
TSPRegSK == "tspRegSK"
OCSPSK == "ocspSK"
RootCASK == "rootCASk"
SignSKStore ==
  "37200007" :> "simSK1"
  @@ "37200008" :> "simSK2"
  @@ "37200009" :> "simSK3"

\* Model params
MAXFRESH == 10
ModelVids == 1000..(999 + MAXFRESH)

ElectionPK == PubKey(ElectionSK)
ElectionSignPK == PubKey(ElectionSignSK)
TSPClientPK == PubKey(TSPClientSK)

\* owned by EA before election start
RootCACert == Cert(PubKey(RootCASK))
TSPRegCert == Cert(PubKey(TSPRegSK))
OCSPCert == Cert(PubKey(OCSPSK))
StageTTL == 3
VerifyWindow == 30
VerifyCountLimit == 3
TSPPastSlack == 60
TSPFutureSlack == 2
Threshold == 2
ThresholdN == 3
KeyHolderIds == {13, 14, 15}
CandidateList == {"Alice", "Bob"}
ElectionId == "E1"
Question1 == "Q1"
TimeElectionStart == 0
VoterList ==
  "voter1" :> Voter("voter1", "D1", "P1")
  @@ "voter2" :> Voter("voter2", "D2", "P2")
  @@ "voter3" :> Voter("voter3", "D3", "P3")

\* Setup phase
ExpectedDecThresholdParams == ThresholdParams(EGParams, Threshold, ThresholdN)
ExpectedSigThresholdParams == ThresholdParams(RSAParams, Threshold, ThresholdN)
ExpectedCryptoParams == CryptoParams(ExpectedDecThresholdParams, ExpectedSigThresholdParams)
GenerateKeyShares(params, ids) == ThresholdShareStore(ids, params, ElectionSK)
GenerateSignKeyShares(params, ids) == ThresholdShareStore(ids, params, ElectionSignSK)
ExpectedDecShares == ThresholdShareStore(KeyHolderIds, ExpectedDecThresholdParams, ElectionSK)
ExpectedSigShares == ThresholdShareStore(KeyHolderIds, ExpectedSigThresholdParams, ElectionSignSK)
ExpectedSmartCardStore == [i \in KeyHolderIds |-> SmartCardData(i, ExpectedDecShares[i], ExpectedSigShares[i]) ]
ExpectedElectionPK == PubKey(ElectionSK)
ExpectedSignPK == PubKey(ElectionSignSK)
ExpectedSignShareSet == { ExpectedSigShares[i] : i \in DOMAIN ExpectedSigShares }
ExpectedElectionCert ==
  X509Cert(ExpectedElectionPK,
           NoStr,
           Cert(ExpectedSignPK),
           ShoupSign(ExpectedSigThresholdParams, ExpectedSignPK, ExpectedSignShareSet, Hash(<< ExpectedElectionPK, NoStr >>)))
ExpectedSignCert ==
  X509Cert(ExpectedSignPK,
           NoStr,
           Cert(ExpectedSignPK),
           ShoupSign(ExpectedSigThresholdParams, ExpectedSignPK, ExpectedSignShareSet, Hash(<< ExpectedSignPK, NoStr >>)))
ExpectedPublicConfig ==
  PublicElectionConfig(
			ElectionId, Question1, CandidateList, 
			ExpectedElectionCert, 
			ExpectedSignCert, 
      RootCACert,
			TSPClientPK, TSPRegCert, OCSPCert, ExpectedCryptoParams)
ExpectedCSConfig == CSConfig(ExpectedPublicConfig, StageTTL, VerifyWindow, VerifyCountLimit, TSPPastSlack, TSPFutureSlack, VoterList)

\* Voting phase
\* subphase time oracle: this is used to address the challenge with using a global clock + arbitrary stage time
PhaseStartTime == 0
PhaseAuthTime == 1
PhaseAuthStatusTime == 2
PhaseChoicesTime == 3
PhaseCertTime == 4
PhaseSignTime == 5
PhaseSignStatusTime == 6
PhaseVoteSubmittedTime == 7
PhaseTSPTime == 8
PhaseOCSPTime == 9
PhaseVerifyTime == 10

\* Model secrets
CSFreshnessStore == 
	[i \in 1..MAXFRESH |-> 
		[ authChallenge |-> <<"authChallenge", i>>, 
			csSid |-> <<"csSid", i>>,
			csAuthTokNonce |-> <<"csAuthTokNonce", i>>,
			issuedVid |-> 999 + i ]]

ProviderFreshnessStore == 
	[i \in 1..MAXFRESH |-> [ sidProv |-> <<"sidProv", i>> ]]

VCDFreshnessStore(clientId) == 
	[i \in 1..MAXFRESH |-> [ r |-> <<"vcdRand", clientId, i>> ]]

ClientIds == {1, 2, 3}

\* Private to voter
VoterProfilesStore ==
  1 :> VoterRef("voter1", "37200007")
  @@ 2 :> VoterRef("voter2", "37200008")
  @@ 3 :> VoterRef("voter3", "37200009")

\* Private to sign device
SignInputStore ==
  [i \in ClientIds |->
    LET phone == VoterProfilesStore[i].phone IN 
			[ phone |-> phone, sk |-> SignSKStore[phone] ]]

\* Private to Provider, stores voter certs issued by CA, maps phone to cert
ProviderCertStore ==
  "37200007" :> IssueX509Cert(RootCASK, PubKey("simSK1"), "voter1")
  @@ "37200008" :> IssueX509Cert(RootCASK, PubKey("simSK2"), "voter2")
  @@ "37200009" :> IssueX509Cert(RootCASK, PubKey("simSK3"), "voter3")

VCDConfigStore == [i \in ClientIds |-> ExpectedPublicConfig]
VVDConfigStore == [i \in ClientIds |-> ExpectedPublicConfig]
CSSymKey == "CSSymKey"
AllowVotingFaultInjection == FALSE

\* Sequential voting scenarios, each picks a voter profile and sign secret from corresponding stores and specifies one choice
HonestVote(clientId, choice) == [ kind |-> "HonestVote", clientId |-> clientId, choice |-> choice ]
VotingScenario ==
  << HonestVote(1, "Bob"),
     HonestVote(1, "Alice"),
     HonestVote(2, "Alice"),
     HonestVote(3, "Bob"),
     HonestVote(3, "Alice") >>
ScenarioIds == 1..Len(VotingScenario)
ScenarioClient(i) == VotingScenario[i].clientId
ScenarioVoterProfile(i) == VoterProfilesStore[ScenarioClient(i)]
ScenarioChoice(i) == VotingScenario[i].choice
ScenarioSignSK(i) == SignInputStore[ScenarioClient(i)].sk
ScenarioVCDRand(i) == VCDFreshnessStore(ScenarioClient(i))[i].r
ScenarioVid(i) == CSFreshnessStore[i].issuedVid
ScenarioIdForVid(vid) == CHOOSE i \in ScenarioIds : ScenarioVid(i) = vid

\* Voting-phase expected output derived from VotingScenario
BuildScenarioRegisteredBallot(i) ==
  LET voterProfile == ScenarioVoterProfile(i)
      voterId == voterProfile.voterId
      phone == voterProfile.phone
      cert == ProviderCertStore[phone]
      ct == EGEnc(ExpectedPublicConfig.decCert.pk, ScenarioChoice(i), ScenarioVCDRand(i))
      bdoc == SignedBDOC(ct, cert, Sign(SignSKStore[phone], DigestOf(ct, cert)))
      req == TSPReq(Hash(bdoc.sig), Sign(TSPClientSK, Hash(bdoc.sig)))
      tsp == TSPRes(req.m, req.n, PhaseTSPTime, ExpectedPublicConfig.tspRegCert, Sign(TSPRegSK, << req.m, req.n, PhaseTSPTime >>))
      ocspReq == OCSPReq(bdoc.signerCert)
      ocsp == OCSPRes(ocspReq, TRUE, PhaseOCSPTime, ExpectedPublicConfig.ocspCert, Sign(OCSPSK, << ocspReq, TRUE, PhaseOCSPTime >>))
  IN  RegisteredBallot(ScenarioVid(i), voterId, PhaseVoteSubmittedTime, tsp.t, bdoc, tsp, ocsp, 0, FALSE)

ExpectedCSExportFromScenario ==
  [vid \in { ScenarioVid(i) : i \in ScenarioIds } |-> BuildScenarioRegisteredBallot(ScenarioIdForVid(vid))]

ExpectedRegExportFromScenario ==
  [i \in ScenarioIds |->
    LET vote == ExpectedCSExportFromScenario[ScenarioVid(i)]
        m == Hash(vote.bdoc.sig)
    IN RegLogEntry(TSPReq(m, Sign(TSPClientSK, m)))]

\* Tally phase
RevokeList == {"voter2"}
ExpectedVotingExport ==
  [ csExport   |-> ExpectedCSExportFromScenario,
    regExport  |-> ExpectedRegExportFromScenario,
    revokeList |-> RevokeList ]

KHData == ExpectedSmartCardStore
EmptyKHData == EmptySmartCardStore(KeyHolderIds)

=============================================================================
