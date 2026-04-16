---- MODULE TallyPhase ----
EXTENDS IVXVChannel, Integers, TLC, FiniteSets, IVXVConfig, IVXVHelper

\* Tally participants
EAPid == 0
PAPid == 1
MixerPid == 2
KHPids == KeyHolderIds
KAPid == 6
AAPid == 7


\* ======================
\* CheckTool
\* ======================
\* Load CS Export 
CreateBallotResponseErr(cfg, voterList, r) ==
  CASE ~(r.voterId \in DOMAIN voterList) -> VOTER_NOT_FOUND
    [] ~VerifyTrustedX509Cert(cfg.rootCACert, r.bdoc.signerCert) -> INVALID_BALLOT_SIGNATURE
    [] r.bdoc.signerCert.pnoee # r.voterId -> INVALID_BALLOT_SIGNATURE
				\* GetTrustedBDOC
    [] r.tsp.cert # cfg.tspRegCert -> REG_RESP_INVALID
            [] ~Verify(CertPK(r.tsp.cert), << r.tsp.m, r.tsp.n, r.tsp.t >>, r.tsp.sig) -> REG_RESP_INVALID
            [] ~Verify(r.bdoc.signerCert.pk, r.bdoc.tbs, r.bdoc.sig) -> INVALID_BALLOT_SIGNATURE
			\* CreateBallot
			[] r.bdoc.sig = Empty -> MISSING_VOTER_SIGNATURE
			[] ~Verify(cfg.tspClientPK, r.tsp.m, r.tsp.n) -> REG_NONCE_SIG_INVALID
			\* omitted UNKNOWN_FILE_IN_VOTE_CONTAINER
    [] r.tsp.t < TimeElectionStart -> TIME_BEFORE_START
    [] OTHER -> OK

CreateBallotResponse(cfg, voterList, r) ==
  LET req == ExtractTSPReqFromResp(r.tsp)
      b ==  Ballot(r.vid, r.tsp.t, voterList[r.voterId], [ q \in {cfg.question} |-> r.bdoc.ct])
  IN IF CreateBallotResponseErr(cfg, voterList, r) = OK
     THEN BallotResponse(b, req, r.tsp)
     ELSE EmptyBallotResponse

LoadedBallotResponses(cfg, voterList, csExport) ==
  [ vid \in { v \in DOMAIN csExport : CreateBallotResponse(cfg, voterList, StoreLookup(csExport, v)) # EmptyBallotResponse }
      |-> CreateBallotResponse(cfg, voterList, StoreLookup(csExport, vid)) ]

LoadBallotFileRecord(cfg, voterList, csExport) ==
  LET loaded == LoadedBallotResponses(cfg, voterList, csExport)
      keptIdxs == { j \in DOMAIN loaded : KeepEarliestBallotResp(j, loaded) }
      localErr == { PAErrorLogEntry(vid, CreateBallotResponseErr(cfg, voterList, StoreLookup(csExport, vid))) :
                      vid \in { v \in DOMAIN csExport :
                                  CreateBallotResponseErr(cfg, voterList, StoreLookup(csExport, v)) # OK } }
      recurrentRespErr == { PAErrorLogEntry(i, REG_RESP_NOT_UNIQUE) : i \in { j \in DOMAIN loaded : ~KeepEarliestBallotResp(j, loaded) } }
  IN [ good |-> [ i \in keptIdxs |-> StoreLookup(loaded, i) ],
       err  |-> localErr \cup recurrentRespErr ]

\* Load Reg Export
LoadRegData(regExport) ==
  [ good |-> [ i \in { j \in DOMAIN regExport :
                         Cardinality(RegIdxsForReq(StoreLookup(regExport, j).req, regExport)) = 1 }
               |-> StoreLookup(regExport, i) ],
    err  |-> { PAErrorLogEntry(req, REG_REQ_NOT_UNIQUE) :
                 req \in { x \in RegReqs(regExport) :
                             Cardinality(RegIdxsForReq(x, regExport)) > 1 } } ]

\* Consistency check CS-Reg
CheckCSRegConsistencyErr(br, regExport) ==
  CASE ~(\E i \in DOMAIN regExport : StoreLookup(regExport, i).req = br.req) -> BALLOT_WITHOUT_REG_REQ
    [] ~(\E i \in DOMAIN regExport :
           /\ StoreLookup(regExport, i).req = br.req
           /\ StoreLookup(regExport, i).resp = br.resp) -> REG_RESP_REQ_UNMATCH
    [] OTHER -> OK

CheckRegCSConsistencyErr(e, cs) ==
  CASE ~(\E i \in DOMAIN cs :
           /\ e.req = StoreLookup(cs, i).req
           /\ e.resp = StoreLookup(cs, i).resp) -> REG_REQ_WITHOUT_BALLOT
  [] OTHER -> OK

CheckCSRegConsistency(cs, reg) ==
  LET goodIdxs == { i \in DOMAIN cs : CheckCSRegConsistencyErr(StoreLookup(cs, i), reg) = OK }
      badIdxs == { i \in DOMAIN cs : CheckCSRegConsistencyErr(StoreLookup(cs, i), reg) # OK }
  IN [ good |-> [ i \in goodIdxs |-> StoreLookup(cs, i) ],
        err  |-> { PAErrorLogEntry(StoreLookup(cs, i).ballot.id, CheckCSRegConsistencyErr(StoreLookup(cs, i), reg)) :
                     i \in badIdxs } ]

CheckRegCSConsistency(reg, cs) ==
  LET goodIdxs == { i \in DOMAIN reg : CheckRegCSConsistencyErr(StoreLookup(reg, i), cs) = OK }
      badIdxs == { i \in DOMAIN reg : CheckRegCSConsistencyErr(StoreLookup(reg, i), cs) # OK }
  IN [ good |-> [ i \in goodIdxs |-> StoreLookup(reg, i) ],
        err  |-> { PAErrorLogEntry(StoreLookup(reg, i).req, CheckRegCSConsistencyErr(StoreLookup(reg, i), cs)) :
                     i \in badIdxs } ]

\* CheckTool Main body
CheckTool_BuildCheckedBB(cfg, voterList, csExport, regExport) ==
  LET checkedCSExport == LoadBallotFileRecord(cfg, voterList, csExport)
			checkedRegExport == LoadRegData(regExport)
			consistency == CheckCSRegConsistency(checkedCSExport.good, checkedRegExport.good)
			checkedBallotResponses == StoreValues(consistency.good)
			voters == { br.ballot.voter.voterId : br \in checkedBallotResponses }
  IN  { VoterBallot(voterId, BallotsByVoterId(voterId, checkedBallotResponses) , FALSE)  : voterId \in voters } \* VoterBallot

CheckTool_GetCSErrLog(cfg, voterList, csExport, regExport) ==
  LET loaded == LoadBallotFileRecord(cfg, voterList, csExport)
      regData == LoadRegData(regExport)
      consistency == CheckCSRegConsistency(loaded.good, regData.good)
  IN loaded.err \cup consistency.err

CheckTool_GetlRegErrLog(cfg, voterList, csExport, regExport) ==
  LET loaded == LoadBallotFileRecord(cfg, voterList, csExport)
      regData == LoadRegData(regExport)
      consistency == CheckRegCSConsistency(regData.good, loaded.good)
  IN regData.err \cup consistency.err

CheckTool_GetAccLog(bbChecked) ==
  UNION { { PALogEntry(b.t, BallotHash(b), vb.voterId, b.id) : b \in vb.ballots } :
            vb \in bbChecked }

\* ======================
\* FilterTool: Squash and filter revoked
\* ======================
KeptBallots(bbChecked, revokeList) ==
{ LatestBallot(vb.ballots) : 
		\* omit IsValidCiphertext-PA
		vb \in { x \in bbChecked : ~(x.voterId \in revokeList) } } 
	\ {EmptyBallot}

FilterTool_BuildFilteredBB(bbChecked, revokeList) == KeptBallots(bbChecked, revokeList)

FilterTool_FilterLog(bbChecked, revokeList) ==
  { PALogEntry(b.t, BallotHash(b), b.voter.voterId, b.id) :
      b \in UNION { vb.ballots : vb \in bbChecked } \ KeptBallots(bbChecked, revokeList) }

\* ======================
\* AnonTool
\* ======================

AnonTool_AnonymizeBB(cfg, bbFiltered) == { AnonVote(b.voter.d, b.voter.p, cfg.question, b.votes[cfg.question]) : b \in bbFiltered }
AnonTool_AnonLog(bbFiltered) == { PALogEntry(0, Hash(a.ct), NoStr, NoStr) : a \in bbFiltered }

\* ======================
\* Tally
\* ======================
\* RecoverDecryption
Tally_RecoverElectionSK(cfg, shares) == RecoverThresholdKey(DecThresholdParamsFromConfig(cfg), cfg.decCert.pk, { s.decShare : s \in shares })
TallySigTBS(tally) == Hash(<< "tally", tally >>)
PlainSigTBS(plain) == Hash(<< "plain", plain >>)
Tally_ShoupSign(cfg, shares, m) == ShoupSign(SigThresholdParamsFromConfig(cfg), cfg.sigCert.pk, { s.sigShare : s \in shares }, m)

\* DecryptBallotbox 
Tally_DecryptBB(bbMixed, sk) ==
  { DecryptedVote(a.d, a.p, a.q, a.ct, DecryptionProof(sk, a.ct, EGDec(sk, a.ct))) :
  	a \in bbMixed }

\* ComputeElectionResult
Tally_ComputeElectionResult(cfg, bbDec, shares) ==
  LET tally == BuildTally(cfg, bbDec)
      plain == BuildPlainBB(cfg, bbDec)
  IN ElectionResult(tally,
                    plain,
                    { v.dp : v \in ValidDecVotes(cfg, bbDec) },
                    InvalidDecVotes(cfg, bbDec),
                    Tally_ShoupSign(cfg, shares, TallySigTBS(tally)),
                    Tally_ShoupSign(cfg, shares, PlainSigTBS(plain)))

\* ======================
\* Audit
\* ======================
\* DecryptTool
VerifyPlaintexts(cfg, bb, proofs, expectedValid) ==
  /\ ProofsUniqueByCiphertext(proofs)
  /\ ProofCiphertexts(proofs) \subseteq BallotboxCiphertexts(bb)
  /\ \A dp \in proofs :
       /\ VerifyDecryptionProof(cfg.decCert.pk, dp)
       /\ ((dp.m \in cfg.choices) = expectedValid)

BallotboxMatchesProofs(bb, er) ==
  LET validCts == ProofCiphertexts(ERValidProofs(er))
      invalidCts == ProofCiphertexts(ERInvalidProofs(er))
      bbCts == BallotboxCiphertexts(bb)
  IN /\ validCts \cap invalidCts = {}
     /\ bbCts = validCts \cup invalidCts

InvalidProofCountMatches(er) == Cardinality(ERInvalidProofs(er)) = Cardinality(ERInvalidVotes(er))

PlainFromValidProofs(bb, proofs) ==
  UNION { { PlainVote(a.d, a.p, a.q, dp.m) :
              dp \in { p \in proofs : a.ct = p.c } } :
            a \in bb }

VerifyValidConsistency(cfg, bb, er) ==
  /\ er.plain = PlainFromValidProofs(bb, ERValidProofs(er))
  /\ \A p \in er.plain : p.choice \in cfg.choices

PlainTallyKeys(plain) == { [ d |-> pv.d, p |-> pv.p, q |-> pv.q ] : pv \in plain }
PlainVotesForTallyKey(plain, tk) == { pv \in plain : /\ pv.d = tk.d /\ pv.p = tk.p /\ pv.q = tk.q }
CountPlainVotesForChoice(plain, tk, choice) == Cardinality({ pv \in PlainVotesForTallyKey(plain, tk) : pv.choice = choice })
BuildTallyFromPlain(cfg, plain) ==
  { TallyRow(tk.d, tk.p, tk.q, choice, CountPlainVotesForChoice(plain, tk, choice)) :
      tk \in PlainTallyKeys(plain), choice \in cfg.choices }
VerifyTally(cfg, er) == er.tally = BuildTallyFromPlain(cfg, er.plain)

\* IntegrityTool
LogHashSet(log) == { e.h : e \in log }
LogHashSum(log) == Hash(LogHashSet(log))
LogBallotIds(log) == { e.ballotId : e \in log }
ErrorLogRefs(log) == { e.ref : e \in log }

CSRecordBallotHash(cfg, r) == 
	Hash(<< r.vid, r.tsp.t, [ q \in {cfg.question} |-> r.bdoc.ct] >>)

CSRecordAnonHash(r) == Hash(r.bdoc.ct)

CSExportHashSet(cfg, csExport) == 
	{ CSRecordBallotHash(cfg, StoreLookup(csExport, vid)) : vid \in DOMAIN csExport }

CSErrorHashSet(cfg, csExport, errLog) == 
	{ CSRecordBallotHash(cfg, StoreLookup(csExport, vid)) : 
		vid \in ErrorLogRefs(errLog) }

CSAnonHashSetForIds(csExport, ids) ==
  { CSRecordAnonHash(StoreLookup(csExport, vid)) : vid \in ids }

CSExportMatchesPALogs(cfg, csExport, accLog, errLog) ==
  LET accIds == LogBallotIds(accLog)
      errIds == ErrorLogRefs(errLog)
  IN	/\ accIds \cap errIds = {} \* no ballot in both logAcc and logErr for checktool
				\* alg:SumValidInvalid: check logAcc + logErr = csExport
	     	/\ DOMAIN csExport = accIds \cup errIds \* ids match
				/\ \A e \in accLog :
						 /\ e.ballotId \in DOMAIN csExport
						 /\ e.h = CSRecordBallotHash(cfg, StoreLookup(csExport, e.ballotId))
	     	/\ Hash(CSExportHashSet(cfg, csExport)) = \* hash sums match
	          Hash(LogHashSet(accLog) \cup CSErrorHashSet(cfg, csExport, errLog))

AnonCiphertexts(bbAnon) == { a.ct : a \in bbAnon }
AnonBBHashSet(bbAnon) == { Hash(a.ct) : a \in bbAnon }

AnonLogMatchesBB(bbAnon, anonLog) ==
  /\ LogHashSum(anonLog) = Hash(AnonBBHashSet(bbAnon))
  /\ Cardinality(anonLog) = Cardinality(bbAnon)
  /\ \A e \in anonLog :
       /\ e.t = 0
       /\ e.voterId = NoStr
       /\ e.ballotId = NoStr
       /\ e.h \in AnonBBHashSet(bbAnon)

AnonAndFilterLogsMatchAccLog(csExport, accLog, filterLog, anonLog) ==
  LET accIds == LogBallotIds(accLog)
      filterIds == LogBallotIds(filterLog)
      anonIds == accIds \ filterIds
  IN /\ filterLog \subseteq accLog
     /\ anonIds \subseteq DOMAIN csExport
     /\ LogHashSet(anonLog) = CSAnonHashSetForIds(csExport, anonIds)
     /\ Cardinality(anonLog) = Cardinality(anonIds)
	                    	
(*--algorithm TallyPhase {
  variables
    chEAToPA = NoMsg,
    chPAToMixer = NoMsg,
    chPAToEA = NoMsg,
    chMixerToEA = NoMsg,
    chEAToKA = NoMsg,
    chKHToKA = [i \in KHPids |-> NoMsg],
    chKAToEA = NoMsg;

  fair process (ElectionAdminProc = EAPid)
  variables
    eaCfg = ExpectedPublicConfig,
    eaCSBallotStore = EmptyCSBallotStore,
    eaRegTspLog = EmptyRegStore,
    eaRevokeList = {},
    eaPAErrLog = {},
    eaPAAccLog = {},
    eaPARegLog = {},
    eaPAFilterLog = {},
    eaPAAnonLog = {},
    eaAnonBB = {},
    eaMixedBB = {},
    eaProof = EmptyShuffleProof,
    eaER = EmptyElectionResult;
  {
  EA_PrepareVotingData:
    eaCSBallotStore := ExpectedVotingExport.csExport;
    eaRegTspLog := ExpectedVotingExport.regExport;
    eaRevokeList := ExpectedVotingExport.revokeList;

  EA_ExportVotingData:
    chEAToPA := Msg("VotingExport",
                    [ csExport |-> eaCSBallotStore,
                      regExport     |-> eaRegTspLog,
                      revokeList |-> eaRevokeList ]);

  EA_RecvPAOutput:
    await chPAToEA.tag = "PAOutput";
    eaPAErrLog := chPAToEA.body.logErr;
    eaPAAccLog := chPAToEA.body.logAcc;
    eaPARegLog := chPAToEA.body.logReg;
    eaPAFilterLog := chPAToEA.body.logFilter;
    eaPAAnonLog := chPAToEA.body.logAnon;
    eaAnonBB := chPAToEA.body.BBAnon;
    chPAToEA := NoMsg;

  EA_RecvMixOutput:
    await chMixerToEA.tag = "MixOutput";
    eaMixedBB := chMixerToEA.body.BBMixed;
    eaProof := chMixerToEA.body.proof;
    chMixerToEA := NoMsg;

  EA_SendTallyInput:
    chEAToKA := Msg("TallyInput", [ BBMixed |-> eaMixedBB ]);

  EA_RecvTallyResult:
    await chKAToEA.tag = "TallyResult";
    eaER := chKAToEA.body.ER;
    chKAToEA := NoMsg;

  EA_Done:
    skip;
  }

  fair process (ProcessorProc = PAPid)
  variables
    paCfg = ExpectedPublicConfig,
    paVoterList = VoterList,
    paCSBallotStore = EmptyCSBallotStore,
    paRegTspLog = EmptyRegStore,
    paRevokeList = {},
    paCheckedBB = {},
    paErrLog = {},
    paAccLog = {},
    paRegLog = {},
    paFilteredBB = {},
    paFilterLog = {},
    paAnonBB = {},
    paAnonLog = {};
  {
  PA_CheckTool:
    await chEAToPA.tag = "VotingExport";
    paCSBallotStore := chEAToPA.body.csExport;
    paRegTspLog := chEAToPA.body.regExport;
    paRevokeList := chEAToPA.body.revokeList;
    paCheckedBB := CheckTool_BuildCheckedBB(paCfg, paVoterList, paCSBallotStore, paRegTspLog);
    paErrLog := CheckTool_GetCSErrLog(paCfg, paVoterList, paCSBallotStore, paRegTspLog);
    paRegLog := CheckTool_GetlRegErrLog(paCfg, paVoterList, paCSBallotStore, paRegTspLog);
    paAccLog := CheckTool_GetAccLog(paCheckedBB);
    chEAToPA := NoMsg;

  PA_FilterBallotbox:
    paFilteredBB := FilterTool_BuildFilteredBB(paCheckedBB, paRevokeList);
    paFilterLog := FilterTool_FilterLog(paCheckedBB, paRevokeList);

  PA_AnonymizeBallotbox:
    paAnonBB := AnonTool_AnonymizeBB(paCfg, paFilteredBB);
    paAnonLog := AnonTool_AnonLog(paAnonBB);

  PA_SendMix:
    chPAToMixer := Msg("MixInput", [ BBAnon |-> paAnonBB ]);

  PA_SendLog:
    chPAToEA := Msg("PAOutput",
                    [ logErr    |-> paErrLog,
                      logAcc    |-> paAccLog,
                      logReg    |-> paRegLog,
                      logFilter |-> paFilterLog,
                      logAnon   |-> paAnonLog,
                      BBAnon    |-> paAnonBB ]);

  PA_Done:
    skip;
  }

  fair process (MixnetProc = MixerPid)
  variables
    mixerInputBB = {},
    mixerBTIn = {},
    mixerBTOut = {},
    mixerMixedBB = {},
    mixerProof = EmptyShuffleProof;
  {

  Mixer_Mix:
    await chPAToMixer.tag = "MixInput";
    mixerInputBB := chPAToMixer.body.BBAnon;
    chPAToMixer := NoMsg;
    mixerMixedBB := mixerInputBB;
    chMixerToEA := Msg("MixOutput", [ BBMixed |-> mixerMixedBB, proof |-> mixerProof ]);

  Mixer_Done:
    skip;
  }

  fair process (KeyHolderProc \in KHPids)
  variables
    khShare = Empty;
  {
  KH_Init:
    khShare := KHData[self];

  KH_SendKeyShares:
    await chKHToKA[self].tag = "None";
    chKHToKA := [chKHToKA EXCEPT ![self] = Msg("KeyShare", [ share |-> khShare ])];

  KH_Done:
    skip;
  }

  fair process (KeyAppProc = KAPid)
  variables
    kaCfg = ExpectedPublicConfig,
    kaInputBB = {},
    kaShares = {},
    kaDecBB = {},
    kaER = EmptyElectionResult;
  {
  KA_RecvTallyInput:
    await chEAToKA.tag = "TallyInput";
    kaInputBB := chEAToKA.body.BBMixed;
    chEAToKA := NoMsg;

  KA_RecvKeyShares:
    await { i \in KHPids : chKHToKA[i].tag = "KeyShare" } # {};
    with (i \in { j \in KHPids : chKHToKA[j].tag = "KeyShare" }) {
      kaShares := kaShares \cup { chKHToKA[i].body.share };
      chKHToKA := [chKHToKA EXCEPT ![i] = NoMsg];
    };
    if (Cardinality(kaShares) < Threshold) {
      goto KA_RecvKeyShares;
    };

  KA_DecryptAndTally:
    kaDecBB := Tally_DecryptBB(kaInputBB, Tally_RecoverElectionSK(kaCfg, kaShares));
    kaER := Tally_ComputeElectionResult(kaCfg, kaDecBB, kaShares);

  KA_SendTallyResult:
    chKAToEA := Msg("TallyResult", [ ER |-> kaER ]);

  KA_Done:
    skip;
  }

  fair process (AuditProc = AAPid)
  {
  AA_Done:
    skip;
  }
}
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "301894b3" /\ chksum(tla) = "1fa90be3")
VARIABLES pc, chEAToPA, chPAToMixer, chPAToEA, chMixerToEA, chEAToKA, 
          chKHToKA, chKAToEA, eaCfg, eaCSBallotStore, eaRegTspLog, 
          eaRevokeList, eaPAErrLog, eaPAAccLog, eaPARegLog, eaPAFilterLog, 
          eaPAAnonLog, eaAnonBB, eaMixedBB, eaProof, eaER, paCfg, paVoterList, 
          paCSBallotStore, paRegTspLog, paRevokeList, paCheckedBB, paErrLog, 
          paAccLog, paRegLog, paFilteredBB, paFilterLog, paAnonBB, paAnonLog, 
          mixerInputBB, mixerBTIn, mixerBTOut, mixerMixedBB, mixerProof, 
          khShare, kaCfg, kaInputBB, kaShares, kaDecBB, kaER

vars == << pc, chEAToPA, chPAToMixer, chPAToEA, chMixerToEA, chEAToKA, 
           chKHToKA, chKAToEA, eaCfg, eaCSBallotStore, eaRegTspLog, 
           eaRevokeList, eaPAErrLog, eaPAAccLog, eaPARegLog, eaPAFilterLog, 
           eaPAAnonLog, eaAnonBB, eaMixedBB, eaProof, eaER, paCfg, 
           paVoterList, paCSBallotStore, paRegTspLog, paRevokeList, 
           paCheckedBB, paErrLog, paAccLog, paRegLog, paFilteredBB, 
           paFilterLog, paAnonBB, paAnonLog, mixerInputBB, mixerBTIn, 
           mixerBTOut, mixerMixedBB, mixerProof, khShare, kaCfg, kaInputBB, 
           kaShares, kaDecBB, kaER >>

ProcSet == {EAPid} \cup {PAPid} \cup {MixerPid} \cup (KHPids) \cup {KAPid} \cup {AAPid}

Init == (* Global variables *)
        /\ chEAToPA = NoMsg
        /\ chPAToMixer = NoMsg
        /\ chPAToEA = NoMsg
        /\ chMixerToEA = NoMsg
        /\ chEAToKA = NoMsg
        /\ chKHToKA = [i \in KHPids |-> NoMsg]
        /\ chKAToEA = NoMsg
        (* Process ElectionAdminProc *)
        /\ eaCfg = ExpectedPublicConfig
        /\ eaCSBallotStore = EmptyCSBallotStore
        /\ eaRegTspLog = EmptyRegStore
        /\ eaRevokeList = {}
        /\ eaPAErrLog = {}
        /\ eaPAAccLog = {}
        /\ eaPARegLog = {}
        /\ eaPAFilterLog = {}
        /\ eaPAAnonLog = {}
        /\ eaAnonBB = {}
        /\ eaMixedBB = {}
        /\ eaProof = EmptyShuffleProof
        /\ eaER = EmptyElectionResult
        (* Process ProcessorProc *)
        /\ paCfg = ExpectedPublicConfig
        /\ paVoterList = VoterList
        /\ paCSBallotStore = EmptyCSBallotStore
        /\ paRegTspLog = EmptyRegStore
        /\ paRevokeList = {}
        /\ paCheckedBB = {}
        /\ paErrLog = {}
        /\ paAccLog = {}
        /\ paRegLog = {}
        /\ paFilteredBB = {}
        /\ paFilterLog = {}
        /\ paAnonBB = {}
        /\ paAnonLog = {}
        (* Process MixnetProc *)
        /\ mixerInputBB = {}
        /\ mixerBTIn = {}
        /\ mixerBTOut = {}
        /\ mixerMixedBB = {}
        /\ mixerProof = EmptyShuffleProof
        (* Process KeyHolderProc *)
        /\ khShare = [self \in KHPids |-> Empty]
        (* Process KeyAppProc *)
        /\ kaCfg = ExpectedPublicConfig
        /\ kaInputBB = {}
        /\ kaShares = {}
        /\ kaDecBB = {}
        /\ kaER = EmptyElectionResult
        /\ pc = [self \in ProcSet |-> CASE self = EAPid -> "EA_PrepareVotingData"
                                        [] self = PAPid -> "PA_CheckTool"
                                        [] self = MixerPid -> "Mixer_Mix"
                                        [] self \in KHPids -> "KH_Init"
                                        [] self = KAPid -> "KA_RecvTallyInput"
                                        [] self = AAPid -> "AA_Done"]

EA_PrepareVotingData == /\ pc[EAPid] = "EA_PrepareVotingData"
                        /\ eaCSBallotStore' = ExpectedVotingExport.csExport
                        /\ eaRegTspLog' = ExpectedVotingExport.regExport
                        /\ eaRevokeList' = ExpectedVotingExport.revokeList
                        /\ pc' = [pc EXCEPT ![EAPid] = "EA_ExportVotingData"]
                        /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, 
                                        chMixerToEA, chEAToKA, chKHToKA, 
                                        chKAToEA, eaCfg, eaPAErrLog, 
                                        eaPAAccLog, eaPARegLog, eaPAFilterLog, 
                                        eaPAAnonLog, eaAnonBB, eaMixedBB, 
                                        eaProof, eaER, paCfg, paVoterList, 
                                        paCSBallotStore, paRegTspLog, 
                                        paRevokeList, paCheckedBB, paErrLog, 
                                        paAccLog, paRegLog, paFilteredBB, 
                                        paFilterLog, paAnonBB, paAnonLog, 
                                        mixerInputBB, mixerBTIn, mixerBTOut, 
                                        mixerMixedBB, mixerProof, khShare, 
                                        kaCfg, kaInputBB, kaShares, kaDecBB, 
                                        kaER >>

EA_ExportVotingData == /\ pc[EAPid] = "EA_ExportVotingData"
                       /\ chEAToPA' = Msg("VotingExport",
                                          [ csExport |-> eaCSBallotStore,
                                            regExport     |-> eaRegTspLog,
                                            revokeList |-> eaRevokeList ])
                       /\ pc' = [pc EXCEPT ![EAPid] = "EA_RecvPAOutput"]
                       /\ UNCHANGED << chPAToMixer, chPAToEA, chMixerToEA, 
                                       chEAToKA, chKHToKA, chKAToEA, eaCfg, 
                                       eaCSBallotStore, eaRegTspLog, 
                                       eaRevokeList, eaPAErrLog, eaPAAccLog, 
                                       eaPARegLog, eaPAFilterLog, eaPAAnonLog, 
                                       eaAnonBB, eaMixedBB, eaProof, eaER, 
                                       paCfg, paVoterList, paCSBallotStore, 
                                       paRegTspLog, paRevokeList, paCheckedBB, 
                                       paErrLog, paAccLog, paRegLog, 
                                       paFilteredBB, paFilterLog, paAnonBB, 
                                       paAnonLog, mixerInputBB, mixerBTIn, 
                                       mixerBTOut, mixerMixedBB, mixerProof, 
                                       khShare, kaCfg, kaInputBB, kaShares, 
                                       kaDecBB, kaER >>

EA_RecvPAOutput == /\ pc[EAPid] = "EA_RecvPAOutput"
                   /\ chPAToEA.tag = "PAOutput"
                   /\ eaPAErrLog' = chPAToEA.body.logErr
                   /\ eaPAAccLog' = chPAToEA.body.logAcc
                   /\ eaPARegLog' = chPAToEA.body.logReg
                   /\ eaPAFilterLog' = chPAToEA.body.logFilter
                   /\ eaPAAnonLog' = chPAToEA.body.logAnon
                   /\ eaAnonBB' = chPAToEA.body.BBAnon
                   /\ chPAToEA' = NoMsg
                   /\ pc' = [pc EXCEPT ![EAPid] = "EA_RecvMixOutput"]
                   /\ UNCHANGED << chEAToPA, chPAToMixer, chMixerToEA, 
                                   chEAToKA, chKHToKA, chKAToEA, eaCfg, 
                                   eaCSBallotStore, eaRegTspLog, eaRevokeList, 
                                   eaMixedBB, eaProof, eaER, paCfg, 
                                   paVoterList, paCSBallotStore, paRegTspLog, 
                                   paRevokeList, paCheckedBB, paErrLog, 
                                   paAccLog, paRegLog, paFilteredBB, 
                                   paFilterLog, paAnonBB, paAnonLog, 
                                   mixerInputBB, mixerBTIn, mixerBTOut, 
                                   mixerMixedBB, mixerProof, khShare, kaCfg, 
                                   kaInputBB, kaShares, kaDecBB, kaER >>

EA_RecvMixOutput == /\ pc[EAPid] = "EA_RecvMixOutput"
                    /\ chMixerToEA.tag = "MixOutput"
                    /\ eaMixedBB' = chMixerToEA.body.BBMixed
                    /\ eaProof' = chMixerToEA.body.proof
                    /\ chMixerToEA' = NoMsg
                    /\ pc' = [pc EXCEPT ![EAPid] = "EA_SendTallyInput"]
                    /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, chEAToKA, 
                                    chKHToKA, chKAToEA, eaCfg, eaCSBallotStore, 
                                    eaRegTspLog, eaRevokeList, eaPAErrLog, 
                                    eaPAAccLog, eaPARegLog, eaPAFilterLog, 
                                    eaPAAnonLog, eaAnonBB, eaER, paCfg, 
                                    paVoterList, paCSBallotStore, paRegTspLog, 
                                    paRevokeList, paCheckedBB, paErrLog, 
                                    paAccLog, paRegLog, paFilteredBB, 
                                    paFilterLog, paAnonBB, paAnonLog, 
                                    mixerInputBB, mixerBTIn, mixerBTOut, 
                                    mixerMixedBB, mixerProof, khShare, kaCfg, 
                                    kaInputBB, kaShares, kaDecBB, kaER >>

EA_SendTallyInput == /\ pc[EAPid] = "EA_SendTallyInput"
                     /\ chEAToKA' = Msg("TallyInput", [ BBMixed |-> eaMixedBB ])
                     /\ pc' = [pc EXCEPT ![EAPid] = "EA_RecvTallyResult"]
                     /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, 
                                     chMixerToEA, chKHToKA, chKAToEA, eaCfg, 
                                     eaCSBallotStore, eaRegTspLog, 
                                     eaRevokeList, eaPAErrLog, eaPAAccLog, 
                                     eaPARegLog, eaPAFilterLog, eaPAAnonLog, 
                                     eaAnonBB, eaMixedBB, eaProof, eaER, paCfg, 
                                     paVoterList, paCSBallotStore, paRegTspLog, 
                                     paRevokeList, paCheckedBB, paErrLog, 
                                     paAccLog, paRegLog, paFilteredBB, 
                                     paFilterLog, paAnonBB, paAnonLog, 
                                     mixerInputBB, mixerBTIn, mixerBTOut, 
                                     mixerMixedBB, mixerProof, khShare, kaCfg, 
                                     kaInputBB, kaShares, kaDecBB, kaER >>

EA_RecvTallyResult == /\ pc[EAPid] = "EA_RecvTallyResult"
                      /\ chKAToEA.tag = "TallyResult"
                      /\ eaER' = chKAToEA.body.ER
                      /\ chKAToEA' = NoMsg
                      /\ pc' = [pc EXCEPT ![EAPid] = "EA_Done"]
                      /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, 
                                      chMixerToEA, chEAToKA, chKHToKA, eaCfg, 
                                      eaCSBallotStore, eaRegTspLog, 
                                      eaRevokeList, eaPAErrLog, eaPAAccLog, 
                                      eaPARegLog, eaPAFilterLog, eaPAAnonLog, 
                                      eaAnonBB, eaMixedBB, eaProof, paCfg, 
                                      paVoterList, paCSBallotStore, 
                                      paRegTspLog, paRevokeList, paCheckedBB, 
                                      paErrLog, paAccLog, paRegLog, 
                                      paFilteredBB, paFilterLog, paAnonBB, 
                                      paAnonLog, mixerInputBB, mixerBTIn, 
                                      mixerBTOut, mixerMixedBB, mixerProof, 
                                      khShare, kaCfg, kaInputBB, kaShares, 
                                      kaDecBB, kaER >>

EA_Done == /\ pc[EAPid] = "EA_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![EAPid] = "Done"]
           /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, chMixerToEA, 
                           chEAToKA, chKHToKA, chKAToEA, eaCfg, 
                           eaCSBallotStore, eaRegTspLog, eaRevokeList, 
                           eaPAErrLog, eaPAAccLog, eaPARegLog, eaPAFilterLog, 
                           eaPAAnonLog, eaAnonBB, eaMixedBB, eaProof, eaER, 
                           paCfg, paVoterList, paCSBallotStore, paRegTspLog, 
                           paRevokeList, paCheckedBB, paErrLog, paAccLog, 
                           paRegLog, paFilteredBB, paFilterLog, paAnonBB, 
                           paAnonLog, mixerInputBB, mixerBTIn, mixerBTOut, 
                           mixerMixedBB, mixerProof, khShare, kaCfg, kaInputBB, 
                           kaShares, kaDecBB, kaER >>

ElectionAdminProc == EA_PrepareVotingData \/ EA_ExportVotingData
                        \/ EA_RecvPAOutput \/ EA_RecvMixOutput
                        \/ EA_SendTallyInput \/ EA_RecvTallyResult
                        \/ EA_Done

PA_CheckTool == /\ pc[PAPid] = "PA_CheckTool"
                /\ chEAToPA.tag = "VotingExport"
                /\ paCSBallotStore' = chEAToPA.body.csExport
                /\ paRegTspLog' = chEAToPA.body.regExport
                /\ paRevokeList' = chEAToPA.body.revokeList
                /\ paCheckedBB' = CheckTool_BuildCheckedBB(paCfg, paVoterList, paCSBallotStore', paRegTspLog')
                /\ paErrLog' = CheckTool_GetCSErrLog(paCfg, paVoterList, paCSBallotStore', paRegTspLog')
                /\ paRegLog' = CheckTool_GetlRegErrLog(paCfg, paVoterList, paCSBallotStore', paRegTspLog')
                /\ paAccLog' = CheckTool_GetAccLog(paCheckedBB')
                /\ chEAToPA' = NoMsg
                /\ pc' = [pc EXCEPT ![PAPid] = "PA_FilterBallotbox"]
                /\ UNCHANGED << chPAToMixer, chPAToEA, chMixerToEA, chEAToKA, 
                                chKHToKA, chKAToEA, eaCfg, eaCSBallotStore, 
                                eaRegTspLog, eaRevokeList, eaPAErrLog, 
                                eaPAAccLog, eaPARegLog, eaPAFilterLog, 
                                eaPAAnonLog, eaAnonBB, eaMixedBB, eaProof, 
                                eaER, paCfg, paVoterList, paFilteredBB, 
                                paFilterLog, paAnonBB, paAnonLog, mixerInputBB, 
                                mixerBTIn, mixerBTOut, mixerMixedBB, 
                                mixerProof, khShare, kaCfg, kaInputBB, 
                                kaShares, kaDecBB, kaER >>

PA_FilterBallotbox == /\ pc[PAPid] = "PA_FilterBallotbox"
                      /\ paFilteredBB' = FilterTool_BuildFilteredBB(paCheckedBB, paRevokeList)
                      /\ paFilterLog' = FilterTool_FilterLog(paCheckedBB, paRevokeList)
                      /\ pc' = [pc EXCEPT ![PAPid] = "PA_AnonymizeBallotbox"]
                      /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, 
                                      chMixerToEA, chEAToKA, chKHToKA, 
                                      chKAToEA, eaCfg, eaCSBallotStore, 
                                      eaRegTspLog, eaRevokeList, eaPAErrLog, 
                                      eaPAAccLog, eaPARegLog, eaPAFilterLog, 
                                      eaPAAnonLog, eaAnonBB, eaMixedBB, 
                                      eaProof, eaER, paCfg, paVoterList, 
                                      paCSBallotStore, paRegTspLog, 
                                      paRevokeList, paCheckedBB, paErrLog, 
                                      paAccLog, paRegLog, paAnonBB, paAnonLog, 
                                      mixerInputBB, mixerBTIn, mixerBTOut, 
                                      mixerMixedBB, mixerProof, khShare, kaCfg, 
                                      kaInputBB, kaShares, kaDecBB, kaER >>

PA_AnonymizeBallotbox == /\ pc[PAPid] = "PA_AnonymizeBallotbox"
                         /\ paAnonBB' = AnonTool_AnonymizeBB(paCfg, paFilteredBB)
                         /\ paAnonLog' = AnonTool_AnonLog(paAnonBB')
                         /\ pc' = [pc EXCEPT ![PAPid] = "PA_SendMix"]
                         /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, 
                                         chMixerToEA, chEAToKA, chKHToKA, 
                                         chKAToEA, eaCfg, eaCSBallotStore, 
                                         eaRegTspLog, eaRevokeList, eaPAErrLog, 
                                         eaPAAccLog, eaPARegLog, eaPAFilterLog, 
                                         eaPAAnonLog, eaAnonBB, eaMixedBB, 
                                         eaProof, eaER, paCfg, paVoterList, 
                                         paCSBallotStore, paRegTspLog, 
                                         paRevokeList, paCheckedBB, paErrLog, 
                                         paAccLog, paRegLog, paFilteredBB, 
                                         paFilterLog, mixerInputBB, mixerBTIn, 
                                         mixerBTOut, mixerMixedBB, mixerProof, 
                                         khShare, kaCfg, kaInputBB, kaShares, 
                                         kaDecBB, kaER >>

PA_SendMix == /\ pc[PAPid] = "PA_SendMix"
              /\ chPAToMixer' = Msg("MixInput", [ BBAnon |-> paAnonBB ])
              /\ pc' = [pc EXCEPT ![PAPid] = "PA_SendLog"]
              /\ UNCHANGED << chEAToPA, chPAToEA, chMixerToEA, chEAToKA, 
                              chKHToKA, chKAToEA, eaCfg, eaCSBallotStore, 
                              eaRegTspLog, eaRevokeList, eaPAErrLog, 
                              eaPAAccLog, eaPARegLog, eaPAFilterLog, 
                              eaPAAnonLog, eaAnonBB, eaMixedBB, eaProof, eaER, 
                              paCfg, paVoterList, paCSBallotStore, paRegTspLog, 
                              paRevokeList, paCheckedBB, paErrLog, paAccLog, 
                              paRegLog, paFilteredBB, paFilterLog, paAnonBB, 
                              paAnonLog, mixerInputBB, mixerBTIn, mixerBTOut, 
                              mixerMixedBB, mixerProof, khShare, kaCfg, 
                              kaInputBB, kaShares, kaDecBB, kaER >>

PA_SendLog == /\ pc[PAPid] = "PA_SendLog"
              /\ chPAToEA' = Msg("PAOutput",
                                 [ logErr    |-> paErrLog,
                                   logAcc    |-> paAccLog,
                                   logReg    |-> paRegLog,
                                   logFilter |-> paFilterLog,
                                   logAnon   |-> paAnonLog,
                                   BBAnon    |-> paAnonBB ])
              /\ pc' = [pc EXCEPT ![PAPid] = "PA_Done"]
              /\ UNCHANGED << chEAToPA, chPAToMixer, chMixerToEA, chEAToKA, 
                              chKHToKA, chKAToEA, eaCfg, eaCSBallotStore, 
                              eaRegTspLog, eaRevokeList, eaPAErrLog, 
                              eaPAAccLog, eaPARegLog, eaPAFilterLog, 
                              eaPAAnonLog, eaAnonBB, eaMixedBB, eaProof, eaER, 
                              paCfg, paVoterList, paCSBallotStore, paRegTspLog, 
                              paRevokeList, paCheckedBB, paErrLog, paAccLog, 
                              paRegLog, paFilteredBB, paFilterLog, paAnonBB, 
                              paAnonLog, mixerInputBB, mixerBTIn, mixerBTOut, 
                              mixerMixedBB, mixerProof, khShare, kaCfg, 
                              kaInputBB, kaShares, kaDecBB, kaER >>

PA_Done == /\ pc[PAPid] = "PA_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![PAPid] = "Done"]
           /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, chMixerToEA, 
                           chEAToKA, chKHToKA, chKAToEA, eaCfg, 
                           eaCSBallotStore, eaRegTspLog, eaRevokeList, 
                           eaPAErrLog, eaPAAccLog, eaPARegLog, eaPAFilterLog, 
                           eaPAAnonLog, eaAnonBB, eaMixedBB, eaProof, eaER, 
                           paCfg, paVoterList, paCSBallotStore, paRegTspLog, 
                           paRevokeList, paCheckedBB, paErrLog, paAccLog, 
                           paRegLog, paFilteredBB, paFilterLog, paAnonBB, 
                           paAnonLog, mixerInputBB, mixerBTIn, mixerBTOut, 
                           mixerMixedBB, mixerProof, khShare, kaCfg, kaInputBB, 
                           kaShares, kaDecBB, kaER >>

ProcessorProc == PA_CheckTool \/ PA_FilterBallotbox
                    \/ PA_AnonymizeBallotbox \/ PA_SendMix \/ PA_SendLog
                    \/ PA_Done

Mixer_Mix == /\ pc[MixerPid] = "Mixer_Mix"
             /\ chPAToMixer.tag = "MixInput"
             /\ mixerInputBB' = chPAToMixer.body.BBAnon
             /\ chPAToMixer' = NoMsg
             /\ mixerMixedBB' = mixerInputBB'
             /\ chMixerToEA' = Msg("MixOutput", [ BBMixed |-> mixerMixedBB', proof |-> mixerProof ])
             /\ pc' = [pc EXCEPT ![MixerPid] = "Mixer_Done"]
             /\ UNCHANGED << chEAToPA, chPAToEA, chEAToKA, chKHToKA, chKAToEA, 
                             eaCfg, eaCSBallotStore, eaRegTspLog, eaRevokeList, 
                             eaPAErrLog, eaPAAccLog, eaPARegLog, eaPAFilterLog, 
                             eaPAAnonLog, eaAnonBB, eaMixedBB, eaProof, eaER, 
                             paCfg, paVoterList, paCSBallotStore, paRegTspLog, 
                             paRevokeList, paCheckedBB, paErrLog, paAccLog, 
                             paRegLog, paFilteredBB, paFilterLog, paAnonBB, 
                             paAnonLog, mixerBTIn, mixerBTOut, mixerProof, 
                             khShare, kaCfg, kaInputBB, kaShares, kaDecBB, 
                             kaER >>

Mixer_Done == /\ pc[MixerPid] = "Mixer_Done"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![MixerPid] = "Done"]
              /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, chMixerToEA, 
                              chEAToKA, chKHToKA, chKAToEA, eaCfg, 
                              eaCSBallotStore, eaRegTspLog, eaRevokeList, 
                              eaPAErrLog, eaPAAccLog, eaPARegLog, 
                              eaPAFilterLog, eaPAAnonLog, eaAnonBB, eaMixedBB, 
                              eaProof, eaER, paCfg, paVoterList, 
                              paCSBallotStore, paRegTspLog, paRevokeList, 
                              paCheckedBB, paErrLog, paAccLog, paRegLog, 
                              paFilteredBB, paFilterLog, paAnonBB, paAnonLog, 
                              mixerInputBB, mixerBTIn, mixerBTOut, 
                              mixerMixedBB, mixerProof, khShare, kaCfg, 
                              kaInputBB, kaShares, kaDecBB, kaER >>

MixnetProc == Mixer_Mix \/ Mixer_Done

KH_Init(self) == /\ pc[self] = "KH_Init"
                 /\ khShare' = [khShare EXCEPT ![self] = KHData[self]]
                 /\ pc' = [pc EXCEPT ![self] = "KH_SendKeyShares"]
                 /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, chMixerToEA, 
                                 chEAToKA, chKHToKA, chKAToEA, eaCfg, 
                                 eaCSBallotStore, eaRegTspLog, eaRevokeList, 
                                 eaPAErrLog, eaPAAccLog, eaPARegLog, 
                                 eaPAFilterLog, eaPAAnonLog, eaAnonBB, 
                                 eaMixedBB, eaProof, eaER, paCfg, paVoterList, 
                                 paCSBallotStore, paRegTspLog, paRevokeList, 
                                 paCheckedBB, paErrLog, paAccLog, paRegLog, 
                                 paFilteredBB, paFilterLog, paAnonBB, 
                                 paAnonLog, mixerInputBB, mixerBTIn, 
                                 mixerBTOut, mixerMixedBB, mixerProof, kaCfg, 
                                 kaInputBB, kaShares, kaDecBB, kaER >>

KH_SendKeyShares(self) == /\ pc[self] = "KH_SendKeyShares"
                          /\ chKHToKA[self].tag = "None"
                          /\ chKHToKA' = [chKHToKA EXCEPT ![self] = Msg("KeyShare", [ share |-> khShare[self] ])]
                          /\ pc' = [pc EXCEPT ![self] = "KH_Done"]
                          /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, 
                                          chMixerToEA, chEAToKA, chKAToEA, 
                                          eaCfg, eaCSBallotStore, eaRegTspLog, 
                                          eaRevokeList, eaPAErrLog, eaPAAccLog, 
                                          eaPARegLog, eaPAFilterLog, 
                                          eaPAAnonLog, eaAnonBB, eaMixedBB, 
                                          eaProof, eaER, paCfg, paVoterList, 
                                          paCSBallotStore, paRegTspLog, 
                                          paRevokeList, paCheckedBB, paErrLog, 
                                          paAccLog, paRegLog, paFilteredBB, 
                                          paFilterLog, paAnonBB, paAnonLog, 
                                          mixerInputBB, mixerBTIn, mixerBTOut, 
                                          mixerMixedBB, mixerProof, khShare, 
                                          kaCfg, kaInputBB, kaShares, kaDecBB, 
                                          kaER >>

KH_Done(self) == /\ pc[self] = "KH_Done"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, chMixerToEA, 
                                 chEAToKA, chKHToKA, chKAToEA, eaCfg, 
                                 eaCSBallotStore, eaRegTspLog, eaRevokeList, 
                                 eaPAErrLog, eaPAAccLog, eaPARegLog, 
                                 eaPAFilterLog, eaPAAnonLog, eaAnonBB, 
                                 eaMixedBB, eaProof, eaER, paCfg, paVoterList, 
                                 paCSBallotStore, paRegTspLog, paRevokeList, 
                                 paCheckedBB, paErrLog, paAccLog, paRegLog, 
                                 paFilteredBB, paFilterLog, paAnonBB, 
                                 paAnonLog, mixerInputBB, mixerBTIn, 
                                 mixerBTOut, mixerMixedBB, mixerProof, khShare, 
                                 kaCfg, kaInputBB, kaShares, kaDecBB, kaER >>

KeyHolderProc(self) == KH_Init(self) \/ KH_SendKeyShares(self)
                          \/ KH_Done(self)

KA_RecvTallyInput == /\ pc[KAPid] = "KA_RecvTallyInput"
                     /\ chEAToKA.tag = "TallyInput"
                     /\ kaInputBB' = chEAToKA.body.BBMixed
                     /\ chEAToKA' = NoMsg
                     /\ pc' = [pc EXCEPT ![KAPid] = "KA_RecvKeyShares"]
                     /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, 
                                     chMixerToEA, chKHToKA, chKAToEA, eaCfg, 
                                     eaCSBallotStore, eaRegTspLog, 
                                     eaRevokeList, eaPAErrLog, eaPAAccLog, 
                                     eaPARegLog, eaPAFilterLog, eaPAAnonLog, 
                                     eaAnonBB, eaMixedBB, eaProof, eaER, paCfg, 
                                     paVoterList, paCSBallotStore, paRegTspLog, 
                                     paRevokeList, paCheckedBB, paErrLog, 
                                     paAccLog, paRegLog, paFilteredBB, 
                                     paFilterLog, paAnonBB, paAnonLog, 
                                     mixerInputBB, mixerBTIn, mixerBTOut, 
                                     mixerMixedBB, mixerProof, khShare, kaCfg, 
                                     kaShares, kaDecBB, kaER >>

KA_RecvKeyShares == /\ pc[KAPid] = "KA_RecvKeyShares"
                    /\ { i \in KHPids : chKHToKA[i].tag = "KeyShare" } # {}
                    /\ \E i \in { j \in KHPids : chKHToKA[j].tag = "KeyShare" }:
                         /\ kaShares' = (kaShares \cup { chKHToKA[i].body.share })
                         /\ chKHToKA' = [chKHToKA EXCEPT ![i] = NoMsg]
                    /\ IF Cardinality(kaShares') < Threshold
                          THEN /\ pc' = [pc EXCEPT ![KAPid] = "KA_RecvKeyShares"]
                          ELSE /\ pc' = [pc EXCEPT ![KAPid] = "KA_DecryptAndTally"]
                    /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, 
                                    chMixerToEA, chEAToKA, chKAToEA, eaCfg, 
                                    eaCSBallotStore, eaRegTspLog, eaRevokeList, 
                                    eaPAErrLog, eaPAAccLog, eaPARegLog, 
                                    eaPAFilterLog, eaPAAnonLog, eaAnonBB, 
                                    eaMixedBB, eaProof, eaER, paCfg, 
                                    paVoterList, paCSBallotStore, paRegTspLog, 
                                    paRevokeList, paCheckedBB, paErrLog, 
                                    paAccLog, paRegLog, paFilteredBB, 
                                    paFilterLog, paAnonBB, paAnonLog, 
                                    mixerInputBB, mixerBTIn, mixerBTOut, 
                                    mixerMixedBB, mixerProof, khShare, kaCfg, 
                                    kaInputBB, kaDecBB, kaER >>

KA_DecryptAndTally == /\ pc[KAPid] = "KA_DecryptAndTally"
                      /\ kaDecBB' = Tally_DecryptBB(kaInputBB, Tally_RecoverElectionSK(kaCfg, kaShares))
                      /\ kaER' = Tally_ComputeElectionResult(kaCfg, kaDecBB', kaShares)
                      /\ pc' = [pc EXCEPT ![KAPid] = "KA_SendTallyResult"]
                      /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, 
                                      chMixerToEA, chEAToKA, chKHToKA, 
                                      chKAToEA, eaCfg, eaCSBallotStore, 
                                      eaRegTspLog, eaRevokeList, eaPAErrLog, 
                                      eaPAAccLog, eaPARegLog, eaPAFilterLog, 
                                      eaPAAnonLog, eaAnonBB, eaMixedBB, 
                                      eaProof, eaER, paCfg, paVoterList, 
                                      paCSBallotStore, paRegTspLog, 
                                      paRevokeList, paCheckedBB, paErrLog, 
                                      paAccLog, paRegLog, paFilteredBB, 
                                      paFilterLog, paAnonBB, paAnonLog, 
                                      mixerInputBB, mixerBTIn, mixerBTOut, 
                                      mixerMixedBB, mixerProof, khShare, kaCfg, 
                                      kaInputBB, kaShares >>

KA_SendTallyResult == /\ pc[KAPid] = "KA_SendTallyResult"
                      /\ chKAToEA' = Msg("TallyResult", [ ER |-> kaER ])
                      /\ pc' = [pc EXCEPT ![KAPid] = "KA_Done"]
                      /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, 
                                      chMixerToEA, chEAToKA, chKHToKA, eaCfg, 
                                      eaCSBallotStore, eaRegTspLog, 
                                      eaRevokeList, eaPAErrLog, eaPAAccLog, 
                                      eaPARegLog, eaPAFilterLog, eaPAAnonLog, 
                                      eaAnonBB, eaMixedBB, eaProof, eaER, 
                                      paCfg, paVoterList, paCSBallotStore, 
                                      paRegTspLog, paRevokeList, paCheckedBB, 
                                      paErrLog, paAccLog, paRegLog, 
                                      paFilteredBB, paFilterLog, paAnonBB, 
                                      paAnonLog, mixerInputBB, mixerBTIn, 
                                      mixerBTOut, mixerMixedBB, mixerProof, 
                                      khShare, kaCfg, kaInputBB, kaShares, 
                                      kaDecBB, kaER >>

KA_Done == /\ pc[KAPid] = "KA_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![KAPid] = "Done"]
           /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, chMixerToEA, 
                           chEAToKA, chKHToKA, chKAToEA, eaCfg, 
                           eaCSBallotStore, eaRegTspLog, eaRevokeList, 
                           eaPAErrLog, eaPAAccLog, eaPARegLog, eaPAFilterLog, 
                           eaPAAnonLog, eaAnonBB, eaMixedBB, eaProof, eaER, 
                           paCfg, paVoterList, paCSBallotStore, paRegTspLog, 
                           paRevokeList, paCheckedBB, paErrLog, paAccLog, 
                           paRegLog, paFilteredBB, paFilterLog, paAnonBB, 
                           paAnonLog, mixerInputBB, mixerBTIn, mixerBTOut, 
                           mixerMixedBB, mixerProof, khShare, kaCfg, kaInputBB, 
                           kaShares, kaDecBB, kaER >>

KeyAppProc == KA_RecvTallyInput \/ KA_RecvKeyShares \/ KA_DecryptAndTally
                 \/ KA_SendTallyResult \/ KA_Done

AA_Done == /\ pc[AAPid] = "AA_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![AAPid] = "Done"]
           /\ UNCHANGED << chEAToPA, chPAToMixer, chPAToEA, chMixerToEA, 
                           chEAToKA, chKHToKA, chKAToEA, eaCfg, 
                           eaCSBallotStore, eaRegTspLog, eaRevokeList, 
                           eaPAErrLog, eaPAAccLog, eaPARegLog, eaPAFilterLog, 
                           eaPAAnonLog, eaAnonBB, eaMixedBB, eaProof, eaER, 
                           paCfg, paVoterList, paCSBallotStore, paRegTspLog, 
                           paRevokeList, paCheckedBB, paErrLog, paAccLog, 
                           paRegLog, paFilteredBB, paFilterLog, paAnonBB, 
                           paAnonLog, mixerInputBB, mixerBTIn, mixerBTOut, 
                           mixerMixedBB, mixerProof, khShare, kaCfg, kaInputBB, 
                           kaShares, kaDecBB, kaER >>

AuditProc == AA_Done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ElectionAdminProc \/ ProcessorProc \/ MixnetProc \/ KeyAppProc
           \/ AuditProc
           \/ (\E self \in KHPids: KeyHolderProc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ElectionAdminProc)
        /\ WF_vars(ProcessorProc)
        /\ WF_vars(MixnetProc)
        /\ \A self \in KHPids : WF_vars(KeyHolderProc(self))
        /\ WF_vars(KeyAppProc)
        /\ WF_vars(AuditProc)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
PlainCount(choice) ==  Cardinality({ p \in eaER.plain : p.choice = choice })

AuditReady == \A self \in ProcSet: pc[self] = "Done"

\* =================
\* Audit Tool
\* =================
Inv_AA_VerifyAuditInput ==
  AuditReady => 
		/\ VerifyX509Cert(ExpectedPublicConfig.sigCert)
		/\ VerifyX509Cert(ExpectedPublicConfig.decCert)
		\* model assumes 1 election question, omit check on tallyset/plainset keys
		/\ Verify(ExpectedPublicConfig.sigCert.pk, TallySigTBS(eaER.tally), eaER.sigTally)
    /\ Verify(ExpectedPublicConfig.sigCert.pk, PlainSigTBS(eaER.plain), eaER.sigPlain)

Inv_AA_DecryptTool ==
  AuditReady => 
    /\ VerifyPlaintexts(ExpectedPublicConfig, eaMixedBB, ERValidProofs(eaER), TRUE)
    /\ VerifyPlaintexts(ExpectedPublicConfig, eaMixedBB, ERInvalidProofs(eaER), FALSE)
    /\ BallotboxMatchesProofs(eaMixedBB, eaER)
    /\ InvalidProofCountMatches(eaER)
    /\ VerifyValidConsistency(ExpectedPublicConfig, eaMixedBB, eaER)
    /\ VerifyTally(ExpectedPublicConfig, eaER)

Inv_AA_IntegrityTool ==
  AuditReady =>
    /\ CSExportMatchesPALogs(ExpectedPublicConfig, eaCSBallotStore, eaPAAccLog, eaPAErrLog)
    /\ AnonLogMatchesBB(eaAnonBB, eaPAAnonLog)
    /\ AnonAndFilterLogsMatchAccLog(eaCSBallotStore, eaPAAccLog, eaPAFilterLog, eaPAAnonLog)

\* =================
\* Other invariants
\* =================
Inv_HonestEA ==
  AuditReady => eaAnonBB = paAnonBB /\ eaMixedBB = mixerMixedBB /\ eaER = kaER

Inv_PA_FilterKeepsLatest ==
  AuditReady
    => \A vb \in paCheckedBB : 
			vb.voterId \notin eaRevokeList /\ vb.ballots # {}
         => \E b \in paFilteredBB :
              /\ b.voter.voterId = vb.voterId
              /\ \A other \in vb.ballots : b.t >= other.t

Inv_Voter1LatestTallied == 
	AuditReady =>
		\E b \in paFilteredBB :
			/\ b.voter.voterId = "voter1" /\ b.id = 1001
			/\ \E dv \in kaDecBB :
					/\ dv.ct = b.votes[ExpectedPublicConfig.question]
					/\ dv.dp.m = "Alice"

Inv_Voter2RevokedFiltered ==
  AuditReady =>	
		/\ ~(\E b \in paFilteredBB : b.voter.voterId = "voter2")
		/\ \E e \in eaPAFilterLog : e.voterId = "voter2" /\ e.ballotId = 1002

Inv_AliceWinsElection == AuditReady => PlainCount("Alice") > PlainCount("Bob")

=============================================================================
