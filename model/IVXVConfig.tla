------------------------------ MODULE IVXVConfig ------------------------------
EXTENDS Integers, IVXVData, IVXVHelper

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
ExpectedCryptoParams == CryptoParams(Threshold, ThresholdN, EGParams, RSAParams)
ExpectedDecThresholdParams == DecThresholdParamsFromCrypto(ExpectedCryptoParams)
ExpectedSigThresholdParams == SigThresholdParamsFromCrypto(ExpectedCryptoParams)
ExpectedDecThresholdKey == ThresholdKey(ExpectedDecThresholdParams, ElectionSK)
ExpectedSigThresholdKey == ThresholdKey(ExpectedSigThresholdParams, ElectionSignSK)
GenerateKeyShares(params, ids, t, n) == ThresholdShareStore(ThresholdKey(ThresholdParams(params, t, n), ElectionSK), ids)
GenerateSignKeyShares(params, ids, t, n) == ThresholdShareStore(ThresholdKey(ThresholdParams(params, t, n), ElectionSignSK), ids)
ExpectedDecShares == ThresholdShareStore(ExpectedDecThresholdKey, KeyHolderIds)
ExpectedSigShares == ThresholdShareStore(ExpectedSigThresholdKey, KeyHolderIds)
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
\* proc in voting phase should not access config constants above this point
\* as they are supposed to be accessed by their owner during setup phase and shared
\* with other participants to build their local config. Invariants bind local config
\* to expected config, and these expected configs serve as the input for the voting phase
\* exceptions: Reg service can still access TSPClientSK, TSPRegSK, TSPRegCert, OCSPSK, OCSPCert

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

ClientIds == {1, 2}

VoterInputStore ==
  1 :> [ voterRef |-> VoterRef("voter1", "37200007"), choice |-> "Alice" ]
  @@ 2 :> [ voterRef |-> VoterRef("voter2", "37200008"), choice |-> "Bob" ]

SignInputStore ==
  [i \in ClientIds |->
    LET phone == VoterInputStore[i].voterRef.phone IN 
			[ phone |-> phone, sk |-> SignSKStore[phone] ]]

VCDConfigStore == [i \in ClientIds |-> ExpectedPublicConfig]
VVDConfigStore == [i \in ClientIds |-> ExpectedPublicConfig]
CSSymKey == "CSSymKey"

\* Private to Provider, stores voter certs issued by CA
ProviderCertStore ==
  "37200007" :> IssueX509Cert(RootCASK, PubKey("simSK1"), "voter1")
  @@ "37200008" :> IssueX509Cert(RootCASK, PubKey("simSK2"), "voter2")
  @@ "37200009" :> IssueX509Cert(RootCASK, PubKey("simSK3"), "voter3")


\* TODO remove/replace below config for voting phase 
ReactionTimeVoter == StageTTL
VerifyWindowVoter == VerifyWindow
VoterId == "voter1"
Phone == "37200007"
SimSK == "simSK1"
VoterProfiles ==
  "voter1" :> "37200007"
  @@ "voter2" :> "37200008"
  @@ "voter3" :> "37200009"


\* TODO voting phase currently only support one vote, the expected data is not bind to any invariant
\* it is only to provide input for tally phase
BuildStoredVote(vid, voterId, choice, submitted, tspTime, ocspTime) ==
  LET ct == EGEnc(ExpectedPublicConfig.decCert.pk, choice, submitted)
  phone == VoterProfiles[voterId]
  cert == ProviderCertStore[phone]
  bdoc == SignedBDOC(ct, cert, Sign(SignSKStore[phone], DigestOf(ct, cert)))
  req == TSPReq(Hash(bdoc.sig), Sign(TSPClientSK, Hash(bdoc.sig)))
  tsp == TSPRes(req.m, req.n, tspTime, ExpectedPublicConfig.tspRegCert, Sign(TSPRegSK, << req.m, req.n, tspTime >>))
  ocspReq == OCSPReq(bdoc.signerCert)
  ocsp == OCSPRes(ocspReq, TRUE, ocspTime, ExpectedPublicConfig.ocspCert, Sign(OCSPSK, << ocspReq, TRUE, ocspTime >>))
  IN  StoredVote(vid, voterId, submitted, bdoc, tsp, ocsp, 0)

ExpectedCSExport ==
  1000 :> BuildStoredVote(1000, "voter1", "Bob", 1, 1, 2)
  @@ 1001 :> BuildStoredVote(1001, "voter1", "Alice", 2, 2, 3)
  @@ 1002 :> BuildStoredVote(1002, "voter2", "Alice", 3, 3, 4)
  @@ 1003 :> BuildStoredVote(1003, "voter3", "Bob", 4, 4, 5)
  @@ 1004 :> BuildStoredVote(1004, "voter3", "Alice", 5, 5, 6)

ExpectedRegExport ==
  1 :> RegLogEntry(ExtractTSPReqFromResp(ExpectedCSExport[1000].tsp), ExpectedCSExport[1000].tsp)
  @@ 2 :> RegLogEntry(ExtractTSPReqFromResp(ExpectedCSExport[1001].tsp), ExpectedCSExport[1001].tsp)
  @@ 3 :> RegLogEntry(ExtractTSPReqFromResp(ExpectedCSExport[1002].tsp), ExpectedCSExport[1002].tsp)
  @@ 4 :> RegLogEntry(ExtractTSPReqFromResp(ExpectedCSExport[1003].tsp), ExpectedCSExport[1003].tsp)
  @@ 5 :> RegLogEntry(ExtractTSPReqFromResp(ExpectedCSExport[1004].tsp), ExpectedCSExport[1004].tsp)


\* Tally phase
ExpectedRevokeList == {"voter2"}
ExpectedVotingExport ==
  [ csExport   |-> ExpectedCSExport,
    regExport  |-> ExpectedRegExport,
    revokeList |-> ExpectedRevokeList ]

KHData == ExpectedSmartCardStore
EmptyKHData == EmptySmartCardStore(KeyHolderIds)

=============================================================================
