---- MODULE VotingPhase ----
EXTENDS IVXVChannel, Integers, TLC, IVXVConfig, IVXVHelper

VoterPid == 0
VCDPid == 1
CSPid == 2
ProviderPid == 3
SignPid == 4
RegPid == 5
VVDPid == 6

VerifyTSPCS(cfg, req, res, now) ==
	/\ ExtractTSPReqFromResp(res) = req /\ res.cert = cfg.cfg.tspRegCert
  /\ Verify(cfg.cfg.tspClientPK, res.m, res.n)
  /\ (-cfg.tSPPastSlack < res.t - now) /\ (res.t - now < cfg.tSPFutureSlack)
  /\ Verify(CertPK(res.cert), <<res.m, res.n, res.t>>, res.sig)

VerifyOCSPCS(cfg, req, res) ==
  /\ res.req = req /\ res.status = TRUE /\ res.cert = cfg.cfg.ocspCert
  /\ Verify(CertPK(res.cert), <<res.req, res.status, res.t>>, res.sig)

VerifyVoteRes(vcdCfg, voteRes, bdoc) ==
LET h == Hash(bdoc.sig)
  IN /\ voteRes.vid # NoInt
     /\ voteRes.tsp.m = h
     /\ Verify(vcdCfg.tspClientPK, voteRes.tsp.m, voteRes.tsp.n)
     /\ Verify(CertPK(vcdCfg.tspRegCert),  <<voteRes.tsp.m, voteRes.tsp.n, voteRes.tsp.t>>, voteRes.tsp.sig)
     /\ voteRes.ocsp.req = OCSPReq(bdoc.signerCert)
     /\ voteRes.ocsp.status = TRUE
     /\ Verify(CertPK(vcdCfg.ocspCert), <<voteRes.ocsp.req, voteRes.ocsp.status, voteRes.ocsp.t>>, voteRes.ocsp.sig)

VerifyTSPVVD(vvdCfg, res, bdoc) ==
  /\ res.m = Hash(bdoc.sig) 
	/\ res.cert = vvdCfg.tspRegCert
  /\ Verify(vvdCfg.tspClientPK, res.m, res.n)
  /\ Verify(CertPK(res.cert), <<res.m, res.n, res.t>>, res.sig)

VerifyOCSPVVD(vvdCfg, res, bdoc) ==
  /\ res.req = OCSPReq(bdoc.signerCert) /\ res.status = TRUE 
	/\ res.cert = vvdCfg.ocspCert
  /\ Verify(CertPK(res.cert), <<res.req, res.status, res.t>>, res.sig)

ValidateBallot(vvdCfg, bdoc, tsp, ocsp, choices) ==
  /\ choices # {}
  /\ VerifyTrustedX509Cert(vvdCfg.rootCACert, bdoc.signerCert)
  /\ Verify(bdoc.signerCert.pk, bdoc.tbs, bdoc.sig)
  /\ VerifyTSPVVD(vvdCfg, tsp, bdoc)
  /\ VerifyOCSPVVD(vvdCfg, ocsp, bdoc)

RecoverChoiceByRand(vvdCfg, r, ct, choices) ==
	LET epk == vvdCfg.decCert.pk IN
  IF /\ EGCheckRandomness(ct, r) /\ \E c \in choices : EGEnc(epk, c, r) = ct
  THEN CHOOSE c \in choices : EGEnc(epk, c, r) = ct
  ELSE NoStr

LatestVoteForVoter(ballotStore, voterId) ==
  IF VoteVidsForVoter(ballotStore, voterId) # {}
  THEN LET latestVid ==
             CHOOSE v \in VoteVidsForVoter(ballotStore, voterId) :
               \A other \in VoteVidsForVoter(ballotStore, voterId) :
                 \/ ballotStore[v].tsp.t > ballotStore[other].tsp.t
                 \/ /\ ballotStore[v].tsp.t = ballotStore[other].tsp.t
                    /\ v <= other
       IN LatestVote(latestVid, ballotStore[latestVid].tsp.t)
  ELSE EmptyLatestVote

FreshSessionCtx(req) == SessionCtx(req.authChallenge, req.csAuthTokNonce, req.issuedVid, Empty, NoInt, NoTSPReq, NoOCSPReq)

ActiveVoteSessionSids(sessionStore) ==
  { sid \in DOMAIN sessionStore :
      /\ sessionStore[sid].phase = "Vote"
      /\ sessionStore[sid].ctx.voteVid # NoInt }

ActiveVoteSessionSid(sessionStore) ==
  IF ActiveVoteSessionSids(sessionStore) # {}
  THEN CHOOSE sid \in ActiveVoteSessionSids(sessionStore) : TRUE
  ELSE Empty

AdvanceSession(ttl, session, stage, now) == [session EXCEPT !.phase = stage, !.exp = now + ttl]

VerifyAndUpdateSession(cfg, store, sid, stage, tok, voterRef, now) ==
	LET ttl == cfg.stageTTL IN
  IF stage = "Auth"
  THEN IF /\ voterRef # NoVoterRef
          /\ ~(sid \in DOMAIN store)
       THEN LET created == SessionData(sid, "Auth", voterRef.voterId, voterRef.phone, Empty, now + ttl, EmptySessionCtx)
            IN [ ok |-> TRUE, session |-> created, store |-> StorePut(store, sid, created) ]
       ELSE [ ok |-> FALSE, session |-> Empty, store |-> store ]
  ELSE LET session == StoreLookup(store, sid)
       IN IF /\ session # Empty
             /\ now <= session.exp
             /\ CanAdvance(session.phase, stage)
             /\ (tok = Empty \/ tok = session.tok)
          THEN LET updated == AdvanceSession(ttl, session, stage, now)
               IN [ ok |-> TRUE, session |-> updated, store |-> StorePut(store, sid, updated) ]
          ELSE [ ok |-> FALSE, session |-> Empty, store |-> store ]

(*--algorithm VotingPhase {
  variables
  	\* global clock
    now = 0,
    \* shared channels
    chVoterToVCD = NoMsg,
    chVCDToVoter = NoMsg,
    chVCDToCS = NoMsg,
    chCSToVCD = NoMsg,
    chCSToProvider = NoMsg,
    chProviderToCS = NoMsg,
    chProviderToSign = NoMsg,
    chSignToProvider = NoMsg,
    chSignToVoter = NoMsg,
    chVoterToSign = NoMsg,
    chCSToReg = NoMsg,
    chRegToCS = NoMsg,
    chVCDToVVD = NoMsg,
    chVVDToCS = NoMsg,
    chCSToVVD = NoMsg,
    chVVDToVoter = NoMsg;

  fair process (VoterProc = VoterPid)
  variables
    voterPhase = "Idle",
    voterChoice = NoStr,
    authStarted = NoInt,
    signStarted = NoInt,
    verifyStarted = NoInt,
    accepted = FALSE,
    voterAccept = NoStr,
    verifiedBDOCs = {};
  {

  Voter_StartVoting: \* sends voterRef (voterId and phone) to VCD (fig:Auth)
    assert VoterCanAdvance(voterPhase, "AuthPending");
    chVoterToVCD := VoterToVCD("StartVoting", VoterRef(VoterId, Phone));
    voterPhase := "AuthPending";
    authStarted := now;
  
  Voter_ApproveAuth: \* (fig:Auth) approves if: the challenge displayed on vcd and sign matches & the voter has just started voting
    await chVCDToVoter.tag = "AuthChallengeDisplay" /\ chSignToVoter.tag = "AuthChallengeDisplay";
    assert voterPhase = "AuthPending";
    assert now <= authStarted + StageTTL;
    assert chVCDToVoter.body.payload.challenge = chSignToVoter.body.payload.challenge;
    chVoterToVCD := VoterToVCD("ApproveAuth", NoBody);
    chVoterToSign := VoterToSign("ApproveAuth", NoBody);
    voterPhase := "ChoicePending";
    chVCDToVoter := NoMsg;
    chSignToVoter := NoMsg;

  Voter_ChooseChoice:
    await chVCDToVoter.tag = "ChoicesDisplay";
    assert voterPhase = "ChoicePending";
    with (c \in chVCDToVoter.body.payload) {
      voterChoice := c;
      chVoterToVCD := VoterToVCD("Choose", c);
    };
    assert VoterCanAdvance(voterPhase, "SignPending");
    voterPhase := "SignPending";
    signStarted := now;
    chVCDToVoter := NoMsg;

  Voter_ApproveSign: \* (fig:Sign) approves if it makes sense to the voter (e.g., voter has made a choice) and sign digest on VCD and Sign matches
    await /\ chVCDToVoter.tag = "SignChallengeDisplay" /\ chSignToVoter.tag = "SignChallengeDisplay";
    assert voterPhase = "SignPending";
    assert voterChoice # NoStr;
    assert now <= signStarted + ReactionTimeVoter;
    assert chVCDToVoter.body.payload.challenge = chSignToVoter.body.payload.challenge;
    chVoterToVCD := VoterToVCD("ApproveSign", NoBody);
    chVoterToSign := VoterToSign("ApproveSign", NoBody);
    assert VoterCanAdvance(voterPhase, "VerifyPending");
    voterPhase := "VerifyPending";
    chVCDToVoter := NoMsg;
		chSignToVoter := NoMsg;

  Voter_VerifyReq:
    await chVCDToVoter.tag = "Voted";
    assert voterPhase = "VerifyPending";
    chVoterToVCD := VoterToVCD("StartVerify", NoBody);
    verifyStarted := now;
    chVCDToVoter := NoMsg;

  Voter_VerifyBallot:
    await chVVDToVoter.tag = "VerifyDisplay" \/ chVVDToVoter.tag = "VerifyFailed" \/ now > verifyStarted + ReactionTimeVoter;
    assert voterPhase = "VerifyPending";
    if (chVVDToVoter.tag = "VerifyDisplay") {
      assert now <= verifyStarted + VerifyWindowVoter;
      assert chVVDToVoter.body.payload.choice = voterChoice;
      assert VoterCanAdvance(voterPhase, "Verified");
      accepted := TRUE;
      voterAccept := chVVDToVoter.body.payload.choice;
      voterPhase := "Verified";
      verifiedBDOCs := verifiedBDOCs \cup {chVVDToVoter.body.payload.bdoc};
    } else {
      accepted := FALSE;
      voterAccept := NoStr;
      if (chVVDToVoter.tag = "VerifyFailed") {
        voterPhase := "Verified";
      } else {
        voterPhase := "Verified";
      };
    };
    chVVDToVoter := NoMsg;

  Voter_Done:
    skip;
  }

  fair process (VCDProc = VCDPid)
  variables
    vcdCtx = EmptyVCDCtx,
    vcdChoice = NoStr,
    vcdVoteBDOC = EmptyBDOC,
    vcdVoteReq = NoVoteReq,
    vcdVoteRes = NoVoteRes;
		vcdRand = 1;
		vcdCfg = ExpectedPublicConfig;
  {
  VCD_RecvStartVoting: \* sends auth req to CS (fig:Auth)
    await chVoterToVCD.tag = "StartVoting";
    chVCDToCS := VCDToCS("AuthReq", Empty, NoInt, Empty, chVoterToVCD.body.payload);
    chVoterToVCD := NoMsg;

  VCD_RecvAuthRes: \* (fig:Auth) records the sids, displays auth challenge
    await chCSToVCD.tag = "AuthRes";
    vcdCtx := [vcdCtx EXCEPT !.sidCS = chCSToVCD.body.sidCS, !.sidAuth = chCSToVCD.body.sidProv];
    chVCDToVoter := VCDToVoter("AuthChallengeDisplay", chCSToVCD.body.payload);
    chCSToVCD := NoMsg;

  VCD_RecvAuthApproval: \* (fig:Auth) sends AuthStatus req to CS with sidCS and sidAuth
    await chVoterToVCD.tag = "ApproveAuth";
    chVCDToCS := VCDToCS("AuthStatusReq", vcdCtx.sidCS, vcdCtx.sidAuth, Empty, NoBody);
    chVoterToVCD := NoMsg;

  VCD_RecvAuthStatus: \* (fig:Auth) receives an authToken, uses it to start the Choices phase
    await chCSToVCD.tag = "AuthStatusRes";
    assert chCSToVCD.body.sidCS = vcdCtx.sidCS;
    vcdCtx := [vcdCtx EXCEPT !.tok = chCSToVCD.body.payload];
    chCSToVCD := NoMsg;

  VCD_SendChoicesReq: \* (fig:Choices) sends a Choices req that contains sidCS and authToken
    chVCDToCS := VCDToCS("ChoicesReq", vcdCtx.sidCS, NoInt, vcdCtx.tok, NoBody);

  VCD_RecvChoices: \* (fig:Choices) displays to voter
    await chCSToVCD.tag = "ChoicesRes";
    assert chCSToVCD.body.sidCS = vcdCtx.sidCS;
    vcdCtx := [vcdCtx EXCEPT !.choices = chCSToVCD.body.payload];
    chVCDToVoter := VCDToVoter("ChoicesDisplay", chCSToVCD.body.payload);
    chCSToVCD := NoMsg;

  VCD_RecvChoice: \* (fig:GetCert) sends a Cert req
    await chVoterToVCD.tag = "Choose";
    assert chVoterToVCD.body.payload \in vcdCtx.choices;
    vcdChoice := chVoterToVCD.body.payload;
    chVCDToCS := VCDToCS("GetCertReq", vcdCtx.sidCS, NoInt, vcdCtx.tok, NoBody);
    chVoterToVCD := NoMsg;

  VCD_RecvCert: \* fig:GetCert) creates an unsigned BDOC from voter choice and signerCert 
    await chCSToVCD.tag = "CertRes";
    assert chCSToVCD.body.sidCS = vcdCtx.sidCS;
    with (cert = chCSToVCD.body.payload) {
			vcdVoteBDOC := UnsignedBDOC(EGEnc(vcdCfg.decCert.pk, vcdChoice, vcdRand), cert);
			vcdCtx := [vcdCtx EXCEPT !.r = vcdRand, !.bdoc = vcdVoteBDOC];
			chCSToVCD := NoMsg;
		};

  VCD_SendSignReq: \* (fig:Sign) sends a Sign req containing the BDOC's tbs field 
    chVCDToCS := VCDToCS("SignReq", vcdCtx.sidCS, NoInt, vcdCtx.tok, vcdCtx.bdoc.tbs);

  VCD_RecvSignRes: \* (fig:Sign) records sidSign, displays sign digest
    await chCSToVCD.tag = "SignChallenge";
    assert chCSToVCD.body.sidCS = vcdCtx.sidCS;
    assert chCSToVCD.body.payload = vcdCtx.bdoc.tbs;
    vcdCtx := [vcdCtx EXCEPT !.sidSign = chCSToVCD.body.sidProv];
    chVCDToVoter := VCDToVoter("SignChallengeDisplay", [challenge |-> chCSToVCD.body.payload, cert |-> vcdCtx.bdoc.signerCert]);
    chCSToVCD := NoMsg;

  VCD_SendSignStatusReq:
    await chVoterToVCD.tag = "ApproveSign";
    chVCDToCS := VCDToCS("SignStatusReq", vcdCtx.sidCS, vcdCtx.sidSign, Empty, NoBody);
    chVoterToVCD := NoMsg;

  VCD_RecvSignResult: \* (fig:Sign) verifies signature, creates a signed BDOC
    await chCSToVCD.tag = "SignStatusRes";
    assert chCSToVCD.body.sidCS = vcdCtx.sidCS;
  	assert Verify(vcdCtx.bdoc.signerCert.pk, vcdCtx.bdoc.tbs, chCSToVCD.body.payload);
    vcdVoteBDOC := SignedBDOC(vcdCtx.bdoc.ct, vcdCtx.bdoc.signerCert, chCSToVCD.body.payload);
    vcdCtx := [vcdCtx EXCEPT !.bdoc = vcdVoteBDOC];
    chCSToVCD := NoMsg;

  VCD_SubmitVote:
    vcdVoteReq := VoteReq(vcdCtx.choices, vcdCtx.bdoc);
    chVCDToCS := VCDToCS("VoteReq", vcdCtx.sidCS, NoInt, vcdCtx.tok, vcdVoteReq);

  VCD_RecvVoteRes: \* stores vid, verify tsp.m matches bdoc digest, verify tsp req, verify tsp res, verify ocsp
    await chCSToVCD.tag = "VoteRes";
    assert chCSToVCD.body.sidCS = vcdCtx.sidCS;
    assert VerifyVoteRes(vcdCfg, chCSToVCD.body.payload, vcdVoteBDOC);
    vcdVoteRes := chCSToVCD.body.payload;
    chVCDToVoter := VCDToVoter("Voted", NoBody);
    chCSToVCD := NoMsg;

  VCD_SendToVVD:
    await chVoterToVCD.tag = "StartVerify";
    chVCDToVVD := VCDToVVD("VerifyQR", vcdCtx.r, vcdVoteRes.vid, vcdCtx.sidCS);
    chVoterToVCD := NoMsg;

  VCD_Done:
    skip;
  }

  fair process (CSProc = CSPid)
  variables
    csSessionStore = EmptySessionStore,
    csBallotStore = EmptyCSBallotStore,
    csLatest = EmptyLatestVote,
    csDroppedBallot = FALSE,
			csReqCnt = 0,
			csFreshnessStore = CSFreshnessStore,
			csCfg = ExpectedCSConfig;
  {
  \* (fig:Auth) generates auth challenge, session ID, sends challenge to vcd and provider
  CS_RecvAuthReq: \* CreateSession
    await chVCDToCS.tag = "AuthReq";
  	csReqCnt := csReqCnt + 1;
  	with (p = chVCDToCS.body.payload,
					req = csFreshnessStore[csReqCnt]) {
			now := now + 1;
			with (upd = VerifyAndUpdateSession(csCfg, csSessionStore, req.csSid, "Auth", Empty, p, now)) {
        assert upd.ok;
					csSessionStore := StorePut(upd.store, req.csSid, [upd.session EXCEPT !.ctx = FreshSessionCtx(req)]);
      };
			chCSToProvider := CSToProvider("AuthStart", req.csSid, NoInt, [challenge |-> req.authChallenge, voterRef |-> VoterRef(p.voterId, p.phone)]);
			chVCDToCS := NoMsg;
		};
  
	CS_RecvAuthStarted: \* (fig:Auth) returns sidCS, sidAuth, and auth Challenge to VCD
    await chProviderToCS.tag = "AuthStarted";
		with (session = StoreLookup(csSessionStore, chProviderToCS.body.sidCS)) {
      assert session # Empty;
			assert chProviderToCS.body.payload.challenge = session.ctx.authChallenge;
			chCSToVCD := CSToVCD("AuthRes", chProviderToCS.body.sidCS, chProviderToCS.body.sidProv, chProviderToCS.body.payload);
			chProviderToCS := NoMsg;
		};

  CS_SendAuthStatusReq: \* (fig:Auth) forwards AuthStatus req to provider
    await chVCDToCS.tag = "AuthStatusReq";
    now := now + 1;
    with (upd = VerifyAndUpdateSession(csCfg, csSessionStore, chVCDToCS.body.sidCS, "AuthStatus", Empty, NoVoterRef, now)) {
      assert upd.ok;
      csSessionStore := upd.store;
      chCSToProvider := CSToProvider("AuthStatusReq", chVCDToCS.body.sidCS, chVCDToCS.body.sidProv, NoBody);
      chVCDToCS := NoMsg;
    };

  CS_RecvAuthStatusRes: \* (fig:Auth) checks if the signed challenge matches the actual challenge, verifies signature using the cert, returns to VCD
    await chProviderToCS.tag = "AuthStatusRes";
			with (cert = chProviderToCS.body.payload.cert,
            session = StoreLookup(csSessionStore, chProviderToCS.body.sidCS)) {
        assert session # Empty;
				assert VerifyTrustedX509Cert(csCfg.cfg.rootCACert, cert);
				assert Verify(cert.pk, session.ctx.authChallenge, chProviderToCS.body.payload.sig);
				\* AuthenticateSession
				with (tok = CreateAuthToken(CSSymKey, cert, session.ctx.issuedVid, session.ctx.authTokNonce)) {
				csSessionStore := StorePut(csSessionStore,
																		chProviderToCS.body.sidCS,
																		[session EXCEPT !.phase = "AuthStatus", !.tok = tok, !.exp = now + csCfg.stageTTL]);
				chCSToVCD := CSToVCD("AuthStatusRes", chProviderToCS.body.sidCS, NoInt, tok);
			};
		};
    chProviderToCS := NoMsg;

  CS_RecvChoicesReq: \* (fig:Choices) verifies CS session (alg:VerifyAndUpdateSessionStatus), returns choices (alg:VoterChoices)
    await chVCDToCS.tag = "ChoicesReq";
    now := now + 1;
    with (upd = VerifyAndUpdateSession(csCfg, csSessionStore, chVCDToCS.body.sidCS, "Choices", chVCDToCS.body.tok, NoVoterRef, now)) {
      assert upd.ok;
      csSessionStore := upd.store;
			chCSToVCD := CSToVCD("ChoicesRes", chVCDToCS.body.sidCS, NoInt, csCfg.cfg.choices);
      chVCDToCS := NoMsg;
    };

  CS_RecvGetCertReq: \* (fig:GetCert) (alg:VerifyAndUpdateSessionStatus), returns cert previously used to sign the challenge
    await chVCDToCS.tag = "GetCertReq";
    now := now + 1;
    with (upd = VerifyAndUpdateSession(csCfg, csSessionStore, chVCDToCS.body.sidCS, "Cert", chVCDToCS.body.tok, NoVoterRef, now)) {
      assert upd.ok;
      csSessionStore := upd.store;
      chCSToProvider := CSToProvider("GetCertReq", chVCDToCS.body.sidCS, NoInt, [phone |-> upd.session.phone]);
      chVCDToCS := NoMsg;
    };

  CS_RecvGetCertRes:
    await chProviderToCS.tag = "GetCertRes";
    assert StoreLookup(csSessionStore, chProviderToCS.body.sidCS) # Empty;
    chCSToVCD := CSToVCD("CertRes", chProviderToCS.body.sidCS, NoInt, chProviderToCS.body.payload);
    chProviderToCS := NoMsg;

  CS_RecvSignReq:  \* (fig:Sign) (alg:VerifyAndUpdateSessionStatus), forward sign digest to provider
    await chVCDToCS.tag = "SignReq";
    now := now + 1;
    with (upd = VerifyAndUpdateSession(csCfg, csSessionStore, chVCDToCS.body.sidCS, "Sign", chVCDToCS.body.tok, NoVoterRef, now)) {
      assert upd.ok;
      with (session = [upd.session EXCEPT !.ctx.signDigest = chVCDToCS.body.payload]) {
        csSessionStore := StorePut(upd.store, chVCDToCS.body.sidCS, session);
        chCSToProvider := CSToProvider("SignStart", chVCDToCS.body.sidCS, NoInt, [challenge |-> session.ctx.signDigest, voterRef |-> VoterRef(session.voterId, session.phone)]);
      };
      chVCDToCS := NoMsg;
    };

  CS_RecvSignStarted: \* Notify VCD that it can start to poll SignStatus (not in (fig:Sign))
    await chProviderToCS.tag = "SignStarted";
    with (session = StoreLookup(csSessionStore, chProviderToCS.body.sidCS)) {
      assert session # Empty;
      chCSToVCD := CSToVCD("SignChallenge", chProviderToCS.body.sidCS, chProviderToCS.body.sidProv, session.ctx.signDigest);
    };
    chProviderToCS := NoMsg;

  CS_SendSignStatusReq:
    await chVCDToCS.tag = "SignStatusReq";
    now := now + 1;
    with (upd = VerifyAndUpdateSession(csCfg, csSessionStore, chVCDToCS.body.sidCS, "SignStatus", Empty, NoVoterRef, now)) {
      assert upd.ok;
      csSessionStore := upd.store;
      chCSToProvider := CSToProvider("SignStatusReq", chVCDToCS.body.sidCS,  chVCDToCS.body.sidProv, NoBody);
      chVCDToCS := NoMsg;
    };

  CS_RecvSignStatusRes: \* (fig:Sign) returns signature to vcd
    await chProviderToCS.tag = "SignStatusRes";
    with (session = StoreLookup(csSessionStore, chProviderToCS.body.sidCS)) {
      assert session # Empty;
      csSessionStore := StorePut(csSessionStore,
                                   chProviderToCS.body.sidCS,
                                   [session EXCEPT !.phase = "SignStatus", !.exp = now + csCfg.stageTTL]);
    };
    chCSToVCD := CSToVCD("SignStatusRes", chProviderToCS.body.sidCS, chProviderToCS.body.sidProv, chProviderToCS.body.payload);
    chProviderToCS := NoMsg;

  CS_RecvVoteReq: \* alg:VerifyAndUpdateSessionStatus, alg:verify-ballot
    await chVCDToCS.tag = "VoteReq";
    now := now + 1;
    with (upd = VerifyAndUpdateSession(csCfg, csSessionStore, chVCDToCS.body.sidCS, "Vote", chVCDToCS.body.tok, NoVoterRef, now)) {
      assert upd.ok;
			  with (openedTok = OpenAuthToken(CSSymKey, chVCDToCS.body.tok),
              p = chVCDToCS.body.payload) {
        assert openedTok # Empty;
				  assert openedTok[1] = p.bdoc.signerCert;
				  assert openedTok[2] = upd.session.ctx.issuedVid;
				  assert VerifyTrustedX509Cert(csCfg.cfg.rootCACert, p.bdoc.signerCert);
				  assert p.bdoc.signerCert.pnoee \in DOMAIN csCfg.voterList;
				  assert upd.session.voterId = p.bdoc.signerCert.pnoee;
				  assert Verify(p.bdoc.signerCert.pk, p.bdoc.tbs, p.bdoc.sig);
          with (voteVid = upd.session.ctx.issuedVid,
                tspReq = LET h == Hash(p.bdoc.sig) IN TSPReq(h, Sign(TSPClientSK, h)),
                ocspReq = OCSPReq(p.bdoc.signerCert),
                session = [upd.session EXCEPT !.ctx.voteVid = voteVid,
                                               !.ctx.tspReq = LET h == Hash(p.bdoc.sig) IN TSPReq(h, Sign(TSPClientSK, h)),
                                               !.ctx.ocspReq = OCSPReq(p.bdoc.signerCert)]) {
            csSessionStore := StorePut(upd.store, chVCDToCS.body.sidCS, session);
			      csBallotStore := StorePut(csBallotStore,
                                    voteVid,
                                    StoredVote(voteVid, upd.session.voterId, now, p.bdoc, NoTSPRes, NoOCSPRes, 0));
          };
		  };
    };
		
  CS_SendTSPReq:
    with (sid = ActiveVoteSessionSid(csSessionStore),
          session = StoreLookup(csSessionStore, ActiveVoteSessionSid(csSessionStore))) {
      assert sid # Empty;
      assert session # Empty;
      chCSToReg := CSToReg("TSPReq", session.ctx.tspReq);
    };

  CS_RecvTSPRes:
    await chRegToCS.tag = "TSPRes";
    now := now + 1;
    with (sid = ActiveVoteSessionSid(csSessionStore),
          session = StoreLookup(csSessionStore, ActiveVoteSessionSid(csSessionStore))) {
      assert sid # Empty;
      assert session # Empty;
      assert VerifyTSPCS(csCfg, session.ctx.tspReq, chRegToCS.body.payload, now);
      csBallotStore := [csBallotStore EXCEPT ![session.ctx.voteVid].tsp = chRegToCS.body.payload];
    };
    chRegToCS := NoMsg;

  CS_SendOCSPReq:
    with (sid = ActiveVoteSessionSid(csSessionStore),
          session = StoreLookup(csSessionStore, ActiveVoteSessionSid(csSessionStore))) {
      assert sid # Empty;
      assert session # Empty;
      chCSToReg := CSToReg("OCSPReq", session.ctx.ocspReq);
    };

  CS_RecvOCSPRes:
    await chRegToCS.tag = "OCSPRes";
    now := now + 1;
    with (sid = ActiveVoteSessionSid(csSessionStore),
          session = StoreLookup(csSessionStore, ActiveVoteSessionSid(csSessionStore)),
          ballot = StoreLookup(csBallotStore, StoreLookup(csSessionStore, ActiveVoteSessionSid(csSessionStore)).ctx.voteVid)) {
      assert sid # Empty;
      assert session # Empty;
      assert ballot # Empty;
      assert VerifyOCSPCS(csCfg, session.ctx.ocspReq, chRegToCS.body.payload);
      assert chRegToCS.body.payload.t >= ballot.tsp.t;
      with (updatedStore = StorePut(csBallotStore,
                                    session.ctx.voteVid,
                                    [ballot EXCEPT !.ocsp = chRegToCS.body.payload])) {
        csBallotStore := updatedStore;
        csLatest := LatestVoteForVoter(updatedStore, ballot.voterId);
      };
    };
    chRegToCS := NoMsg;

  CS_SendVoteRes:
    with (sid = ActiveVoteSessionSid(csSessionStore),
          session = StoreLookup(csSessionStore, ActiveVoteSessionSid(csSessionStore)),
          ballot = StoreLookup(csBallotStore, StoreLookup(csSessionStore, ActiveVoteSessionSid(csSessionStore)).ctx.voteVid)) {
      assert sid # Empty;
      assert session # Empty;
      assert ballot # Empty;
      chCSToVCD := CSToVCD("VoteRes", sid, NoInt, VoteRes(session.ctx.voteVid, ballot.tsp, ballot.ocsp));
    	chVCDToCS := NoMsg;
    };

  CS_RecvVerifyReq:
    await chVVDToCS.tag = "VerifyReq";
    now := now + 1;
    with (upd = VerifyAndUpdateSession(csCfg, csSessionStore, chVVDToCS.body.sidCS, "Verify", Empty, NoVoterRef, now),
          ballot = StoreLookup(csBallotStore, chVVDToCS.body.vid)) {
      if (/\ upd.ok
          /\ ballot # Empty
          /\ chVVDToCS.body.vid = csLatest.vid
          /\ ballot.verCount < csCfg.verifyCountLimit
          /\ now <= ballot.submitted + csCfg.verifyWindow
          /\ ballot.tsp # NoTSPRes
          /\ ballot.ocsp # NoOCSPRes) {
        csSessionStore := upd.store;
        csBallotStore := [csBallotStore EXCEPT ![chVVDToCS.body.vid].verCount = @ + 1];
				chCSToVVD := CSToVVD("VerifyRes", VerifyRes(ballot.bdoc, ballot.tsp, ballot.ocsp, csCfg.cfg.choices));
      } else {
        skip;
      };
    };
    chVVDToCS := NoMsg;

  CS_DropBallot:
    either {
      skip;
    } or {
      if (/\ csLatest.vid # NoInt /\ csLatest.vid \in DOMAIN csBallotStore) {
          with (ballot = StoreLookup(csBallotStore, csLatest.vid),
                updatedStore = StoreDelete(csBallotStore, csLatest.vid)) {
            assert ballot # Empty;
            csBallotStore := updatedStore;
            csLatest := LatestVoteForVoter(updatedStore, ballot.voterId);
          };
          csDroppedBallot := TRUE;
      } else {
        skip;
      };
    };

  CS_Done:
    skip;
  }

  fair process (ProviderProc = ProviderPid)
  variables
    providerSessionStore = EmptyProviderSessionStore,
    providerCertStore = ProviderCertStore;
		provAuthSid = 101;
		provSignSid = 102;
  {
  Provider_RecvAuthStart: \* (fig:Auth) generates sidAuth for CS, forwards challenge to Sign, stores voterRef in an entry with sidAuth
    await chCSToProvider.tag = "AuthStart";
  	with (p = chCSToProvider.body.payload) {
      assert ProviderSidsForPhone(providerSessionStore, p.voterRef.phone, "Auth") = {};
			providerSessionStore := StorePut(providerSessionStore, provAuthSid, ProviderEntry(provAuthSid, p.voterRef.phone, "Auth", p.challenge, Empty));
			chProviderToSign := ProviderToSign("AuthChallenge", [challenge |-> p.challenge, phone |-> p.voterRef.phone]);
			chProviderToCS := ProviderToCS("AuthStarted", chCSToProvider.body.sidCS, provAuthSid, [challenge |-> p.challenge]);
			chCSToProvider := NoMsg;
		};

  Provider_RecvAuthSignature:  \* (fig:Auth) stores the signature in an entry that binds to phone and auth kind
    await chSignToProvider.tag = "AuthSignature";
    with (sid = ProviderSidForPhone(providerSessionStore, chSignToProvider.body.payload.phone, "Auth"),
          entry = StoreLookup(providerSessionStore, sid)) {
      assert sid # NoInt;
      assert entry # Empty;
      assert chSignToProvider.body.payload.phone = entry.phone;
      providerSessionStore := StorePut(providerSessionStore,
                                                 sid,
                                                 [entry EXCEPT !.sig = chSignToProvider.body.payload.sig]);
      chSignToProvider := NoMsg;
    };

  Provider_RecvAuthStatusReq: \* (fig:Auth) checks if the requested sidAuth matches entry, and whether the entry has sig, returns sig
    await chCSToProvider.tag = "AuthStatusReq";
    with (entry = StoreLookup(providerSessionStore, chCSToProvider.body.sidProv)) {
      assert entry # Empty;
      assert chCSToProvider.body.sidProv = entry.sidProv;
      assert entry.sig # Empty;
      assert entry.phone \in DOMAIN providerCertStore;
      chProviderToCS := ProviderToCS("AuthStatusRes", chCSToProvider.body.sidCS, entry.sidProv, [cert |-> providerCertStore[entry.phone], sig |-> entry.sig]);
      chCSToProvider := NoMsg;
    };

  Provider_RecvGetCertReq:
    await chCSToProvider.tag = "GetCertReq";
    with (phone = chCSToProvider.body.payload.phone) {
      assert phone \in DOMAIN providerCertStore;
      chProviderToCS := ProviderToCS("GetCertRes", chCSToProvider.body.sidCS, NoInt, providerCertStore[phone]);
      chCSToProvider := NoMsg;
    };

  Provider_RecvSignStart: \* (fig:Sign)  generates sidSign for CS, forwards challenge to Sign, stores voterRef in an entry with sidSign
    await chCSToProvider.tag = "SignStart";
  	with (p = chCSToProvider.body.payload) {
      assert ProviderSidsForPhone(providerSessionStore, p.voterRef.phone, "Sign") = {};
      assert p.voterRef.phone \in DOMAIN providerCertStore;
			providerSessionStore := StorePut(providerSessionStore, provSignSid, ProviderEntry(provSignSid, p.voterRef.phone, "Sign", p.challenge, Empty));
			chProviderToSign := ProviderToSign("SignChallenge", [challenge |-> p.challenge, cert |-> providerCertStore[p.voterRef.phone], phone |-> p.voterRef.phone]);
			chProviderToCS := ProviderToCS("SignStarted", chCSToProvider.body.sidCS, provSignSid, [challenge |-> p.challenge]);
			chCSToProvider := NoMsg;
		};

  Provider_RecvSignSignature: 
    await chSignToProvider.tag = "SignSignature";
    with (sid = ProviderSidForPhone(providerSessionStore, chSignToProvider.body.payload.phone, "Sign"),
          entry = StoreLookup(providerSessionStore, sid)) {
      assert sid # NoInt;
      assert entry # Empty;
      assert chSignToProvider.body.payload.phone = entry.phone;
      providerSessionStore := StorePut(providerSessionStore,
                                                 sid,
                                                 [entry EXCEPT !.sig = chSignToProvider.body.payload.sig]);
      chSignToProvider := NoMsg;
    };

  Provider_RecvSignStatusReq: \* (fig:Sign) checks if the requested sidSign matches entry, and whether the entry has sig, returns sig
    await chCSToProvider.tag = "SignStatusReq";
    with (entry = StoreLookup(providerSessionStore, chCSToProvider.body.sidProv)) {
      assert entry # Empty;
      assert chCSToProvider.body.sidProv = entry.sidProv;
      assert entry.sig # Empty;
      chProviderToCS := ProviderToCS("SignStatusRes", chCSToProvider.body.sidCS, entry.sidProv, entry.sig);
      chCSToProvider := NoMsg;
    };

  Provider_Done:
    skip;
  }

  fair process (SignProc = SignPid)
  variables
    signAuthChallenge = Empty,
    authPhone = NoStr,
    signChallenge = Empty,
    signPhone = NoStr;
  {
  Sign_RecvAuthChallenge: \* (fig:Auth) displays auth challenge
    await chProviderToSign.tag = "AuthChallenge";
    signAuthChallenge := chProviderToSign.body.payload.challenge;
    authPhone := chProviderToSign.body.payload.phone;
    chSignToVoter := SignToVoter("AuthChallengeDisplay", chProviderToSign.body.payload);
    chProviderToSign := NoMsg;

  Sign_RecvAuthApproval:  \* (fig:Auth) starts signing, and returns result to provider
    await chVoterToSign.tag = "ApproveAuth";
    chSignToProvider := SignToProvider("AuthSignature", [phone |-> authPhone, sig |-> Sign(SimSK, signAuthChallenge)]);
    chVoterToSign := NoMsg;
    signAuthChallenge := Empty;
    authPhone := NoStr;

  Sign_RecvSignChallenge:
    await chProviderToSign.tag = "SignChallenge";
    signChallenge := chProviderToSign.body.payload.challenge;
    signPhone := chProviderToSign.body.payload.phone;
    chSignToVoter := SignToVoter("SignChallengeDisplay", chProviderToSign.body.payload);
    chProviderToSign := NoMsg;

  Sign_RecvSignApproval:
    await chVoterToSign.tag = "ApproveSign";
    chSignToProvider := SignToProvider("SignSignature", [phone |-> signPhone, sig |-> Sign(SimSK, signChallenge)]);
    chVoterToSign := NoMsg;
    signChallenge := Empty;
    signPhone := NoStr;

  Sign_Done:
    skip;
  }

  fair process (RegProc = RegPid)
  variables
    regStore = EmptyRegStore,
    regNextIdx = 1,
    regOcspStore = EmptyOCSPStore,
    regNextOCSPIdx = 1,
    regDroppedLogEntry = FALSE;
  {
  Reg_RecvTSPReq:
    await chCSToReg.tag = "TSPReq";
  	with (p = chCSToReg.body.payload) {
      with (tsp = TSPRes(p.m, p.n, now, TSPRegCert, Sign(TSPRegSK, <<p.m, p.n, now>>))) {
			  regStore := StorePut(regStore, regNextIdx, RegLogEntry(p, tsp));
        regNextIdx := regNextIdx + 1;
			  chRegToCS := RegToCS("TSPRes", tsp);
      };
			chCSToReg := NoMsg;
		};

  Reg_RecvOCSPReq:
    await chCSToReg.tag = "OCSPReq";
		with (p = chCSToReg.body.payload) {
      with (ocsp = OCSPRes(p, TRUE, now, OCSPCert, Sign(OCSPSK, <<p, TRUE, now>>))) {
			  regOcspStore := StorePut(regOcspStore, regNextOCSPIdx, ocsp);
        regNextOCSPIdx := regNextOCSPIdx + 1;
			  chRegToCS := RegToCS("OCSPRes", ocsp);
      };
				chCSToReg := NoMsg;
			};

  Reg_DropLogEntry:
    either {
      skip;
    } or {
      if (DOMAIN regStore # {}) {
        with (idx = CHOOSE i \in DOMAIN regStore : TRUE) {
          regStore := StoreDelete(regStore, idx);
          regDroppedLogEntry := TRUE;
        };
      } else {
        skip;
      };
    };

  Reg_Done:
    skip;
  }

  fair process (VVDProc = VVDPid)
  variables
    vvdSidCS = Empty,
    vvdVid = NoInt,
    vvdRand = NoInt,
    vvdChoice = NoStr,
    vvdAccepted = FALSE,
    vvdRejected = FALSE;
		vvdCfg = ExpectedPublicConfig;
  {
  VVD_RecvQR:
    await chVCDToVVD.tag = "VerifyQR";
    vvdRand := chVCDToVVD.body.r;
    vvdVid := chVCDToVVD.body.vid;
    vvdSidCS := chVCDToVVD.body.sidCS;
    chVVDToCS := VVDToCS("VerifyReq", vvdSidCS, vvdVid);
    chVCDToVVD := NoMsg;

  VVD_RecvVerifyRes: \* verify signature, tsp, ocsp, then try decrypt
    await chCSToVVD.tag = "VerifyRes";
  	with (p = chCSToVVD.body.payload) {
				if (/\ ValidateBallot(vvdCfg, p.bdoc, p.tsp, p.ocsp, p.choices) /\ RecoverChoiceByRand(vvdCfg, vvdRand, p.bdoc.ct, p.choices) # NoStr) {
					vvdChoice := RecoverChoiceByRand(vvdCfg, vvdRand, p.bdoc.ct, p.choices);
					vvdAccepted := TRUE;
					chVVDToVoter := VVDToVoter("VerifyDisplay", [choice |-> vvdChoice, bdoc |-> p.bdoc]);
				} else {
					vvdRejected := TRUE;
					chVVDToVoter := VVDToVoter("VerifyFailed", NoBody);
				};
				chCSToVVD := NoMsg;
			};

  VVD_Done:
    skip;
  }
}
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "5de66ee4" /\ chksum(tla) = "5370ec08")
VARIABLES pc, now, chVoterToVCD, chVCDToVoter, chVCDToCS, chCSToVCD, 
          chCSToProvider, chProviderToCS, chProviderToSign, chSignToProvider, 
          chSignToVoter, chVoterToSign, chCSToReg, chRegToCS, chVCDToVVD, 
          chVVDToCS, chCSToVVD, chVVDToVoter, voterPhase, voterChoice, 
          authStarted, signStarted, verifyStarted, accepted, voterAccept, 
          verifiedBDOCs, vcdCtx, vcdChoice, vcdVoteBDOC, vcdVoteReq, 
          vcdVoteRes, vcdRand, vcdCfg, csSessionStore, csBallotStore, 
          csLatest, csDroppedBallot, csReqCnt, csFreshnessStore, csCfg, 
          providerSessionStore, providerCertStore, provAuthSid, provSignSid, 
          signAuthChallenge, authPhone, signChallenge, signPhone, regStore, 
          regNextIdx, regOcspStore, regNextOCSPIdx, regDroppedLogEntry, 
          vvdSidCS, vvdVid, vvdRand, vvdChoice, vvdAccepted, vvdRejected, 
          vvdCfg

vars == << pc, now, chVoterToVCD, chVCDToVoter, chVCDToCS, chCSToVCD, 
           chCSToProvider, chProviderToCS, chProviderToSign, chSignToProvider, 
           chSignToVoter, chVoterToSign, chCSToReg, chRegToCS, chVCDToVVD, 
           chVVDToCS, chCSToVVD, chVVDToVoter, voterPhase, voterChoice, 
           authStarted, signStarted, verifyStarted, accepted, voterAccept, 
           verifiedBDOCs, vcdCtx, vcdChoice, vcdVoteBDOC, vcdVoteReq, 
           vcdVoteRes, vcdRand, vcdCfg, csSessionStore, csBallotStore, 
           csLatest, csDroppedBallot, csReqCnt, csFreshnessStore, csCfg, 
           providerSessionStore, providerCertStore, provAuthSid, provSignSid, 
           signAuthChallenge, authPhone, signChallenge, signPhone, regStore, 
           regNextIdx, regOcspStore, regNextOCSPIdx, regDroppedLogEntry, 
           vvdSidCS, vvdVid, vvdRand, vvdChoice, vvdAccepted, vvdRejected, 
           vvdCfg >>

ProcSet == {VoterPid} \cup {VCDPid} \cup {CSPid} \cup {ProviderPid} \cup {SignPid} \cup {RegPid} \cup {VVDPid}

Init == (* Global variables *)
        /\ now = 0
        /\ chVoterToVCD = NoMsg
        /\ chVCDToVoter = NoMsg
        /\ chVCDToCS = NoMsg
        /\ chCSToVCD = NoMsg
        /\ chCSToProvider = NoMsg
        /\ chProviderToCS = NoMsg
        /\ chProviderToSign = NoMsg
        /\ chSignToProvider = NoMsg
        /\ chSignToVoter = NoMsg
        /\ chVoterToSign = NoMsg
        /\ chCSToReg = NoMsg
        /\ chRegToCS = NoMsg
        /\ chVCDToVVD = NoMsg
        /\ chVVDToCS = NoMsg
        /\ chCSToVVD = NoMsg
        /\ chVVDToVoter = NoMsg
        (* Process VoterProc *)
        /\ voterPhase = "Idle"
        /\ voterChoice = NoStr
        /\ authStarted = NoInt
        /\ signStarted = NoInt
        /\ verifyStarted = NoInt
        /\ accepted = FALSE
        /\ voterAccept = NoStr
        /\ verifiedBDOCs = {}
        (* Process VCDProc *)
        /\ vcdCtx = EmptyVCDCtx
        /\ vcdChoice = NoStr
        /\ vcdVoteBDOC = EmptyBDOC
        /\ vcdVoteReq = NoVoteReq
        /\ vcdVoteRes = NoVoteRes
        /\ vcdRand = 1
        /\ vcdCfg = ExpectedPublicConfig
        (* Process CSProc *)
        /\ csSessionStore = EmptySessionStore
        /\ csBallotStore = EmptyCSBallotStore
        /\ csLatest = EmptyLatestVote
        /\ csDroppedBallot = FALSE
        /\ csReqCnt = 0
        /\ csFreshnessStore = CSFreshnessStore
        /\ csCfg = ExpectedCSConfig
        (* Process ProviderProc *)
        /\ providerSessionStore = EmptyProviderSessionStore
        /\ providerCertStore = ProviderCertStore
        /\ provAuthSid = 101
        /\ provSignSid = 102
        (* Process SignProc *)
        /\ signAuthChallenge = Empty
        /\ authPhone = NoStr
        /\ signChallenge = Empty
        /\ signPhone = NoStr
        (* Process RegProc *)
        /\ regStore = EmptyRegStore
        /\ regNextIdx = 1
        /\ regOcspStore = EmptyOCSPStore
        /\ regNextOCSPIdx = 1
        /\ regDroppedLogEntry = FALSE
        (* Process VVDProc *)
        /\ vvdSidCS = Empty
        /\ vvdVid = NoInt
        /\ vvdRand = NoInt
        /\ vvdChoice = NoStr
        /\ vvdAccepted = FALSE
        /\ vvdRejected = FALSE
        /\ vvdCfg = ExpectedPublicConfig
        /\ pc = [self \in ProcSet |-> CASE self = VoterPid -> "Voter_StartVoting"
                                        [] self = VCDPid -> "VCD_RecvStartVoting"
                                        [] self = CSPid -> "CS_RecvAuthReq"
                                        [] self = ProviderPid -> "Provider_RecvAuthStart"
                                        [] self = SignPid -> "Sign_RecvAuthChallenge"
                                        [] self = RegPid -> "Reg_RecvTSPReq"
                                        [] self = VVDPid -> "VVD_RecvQR"]

Voter_StartVoting == /\ pc[VoterPid] = "Voter_StartVoting"
                     /\ Assert(VoterCanAdvance(voterPhase, "AuthPending"), 
                               "Failure of assertion at line 133, column 5.")
                     /\ chVoterToVCD' = VoterToVCD("StartVoting", VoterRef(VoterId, Phone))
                     /\ voterPhase' = "AuthPending"
                     /\ authStarted' = now
                     /\ pc' = [pc EXCEPT ![VoterPid] = "Voter_ApproveAuth"]
                     /\ UNCHANGED << now, chVCDToVoter, chVCDToCS, chCSToVCD, 
                                     chCSToProvider, chProviderToCS, 
                                     chProviderToSign, chSignToProvider, 
                                     chSignToVoter, chVoterToSign, chCSToReg, 
                                     chRegToCS, chVCDToVVD, chVVDToCS, 
                                     chCSToVVD, chVVDToVoter, voterChoice, 
                                     signStarted, verifyStarted, accepted, 
                                     voterAccept, verifiedBDOCs, vcdCtx, 
                                     vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                     vcdVoteRes, vcdRand, vcdCfg, 
                                     csSessionStore, csBallotStore, csLatest, 
                                     csDroppedBallot, csReqCnt, 
                                     csFreshnessStore, csCfg, 
                                     providerSessionStore, providerCertStore, 
                                     provAuthSid, provSignSid, 
                                     signAuthChallenge, authPhone, 
                                     signChallenge, signPhone, regStore, 
                                     regNextIdx, regOcspStore, regNextOCSPIdx, 
                                     regDroppedLogEntry, vvdSidCS, vvdVid, 
                                     vvdRand, vvdChoice, vvdAccepted, 
                                     vvdRejected, vvdCfg >>

Voter_ApproveAuth == /\ pc[VoterPid] = "Voter_ApproveAuth"
                     /\ chVCDToVoter.tag = "AuthChallengeDisplay" /\ chSignToVoter.tag = "AuthChallengeDisplay"
                     /\ Assert(voterPhase = "AuthPending", 
                               "Failure of assertion at line 140, column 5.")
                     /\ Assert(now <= authStarted + StageTTL, 
                               "Failure of assertion at line 141, column 5.")
                     /\ Assert(chVCDToVoter.body.payload.challenge = chSignToVoter.body.payload.challenge, 
                               "Failure of assertion at line 142, column 5.")
                     /\ chVoterToVCD' = VoterToVCD("ApproveAuth", NoBody)
                     /\ chVoterToSign' = VoterToSign("ApproveAuth", NoBody)
                     /\ voterPhase' = "ChoicePending"
                     /\ chVCDToVoter' = NoMsg
                     /\ chSignToVoter' = NoMsg
                     /\ pc' = [pc EXCEPT ![VoterPid] = "Voter_ChooseChoice"]
                     /\ UNCHANGED << now, chVCDToCS, chCSToVCD, chCSToProvider, 
                                     chProviderToCS, chProviderToSign, 
                                     chSignToProvider, chCSToReg, chRegToCS, 
                                     chVCDToVVD, chVVDToCS, chCSToVVD, 
                                     chVVDToVoter, voterChoice, authStarted, 
                                     signStarted, verifyStarted, accepted, 
                                     voterAccept, verifiedBDOCs, vcdCtx, 
                                     vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                     vcdVoteRes, vcdRand, vcdCfg, 
                                     csSessionStore, csBallotStore, csLatest, 
                                     csDroppedBallot, csReqCnt, 
                                     csFreshnessStore, csCfg, 
                                     providerSessionStore, providerCertStore, 
                                     provAuthSid, provSignSid, 
                                     signAuthChallenge, authPhone, 
                                     signChallenge, signPhone, regStore, 
                                     regNextIdx, regOcspStore, regNextOCSPIdx, 
                                     regDroppedLogEntry, vvdSidCS, vvdVid, 
                                     vvdRand, vvdChoice, vvdAccepted, 
                                     vvdRejected, vvdCfg >>

Voter_ChooseChoice == /\ pc[VoterPid] = "Voter_ChooseChoice"
                      /\ chVCDToVoter.tag = "ChoicesDisplay"
                      /\ Assert(voterPhase = "ChoicePending", 
                                "Failure of assertion at line 151, column 5.")
                      /\ \E c \in chVCDToVoter.body.payload:
                           /\ voterChoice' = c
                           /\ chVoterToVCD' = VoterToVCD("Choose", c)
                      /\ Assert(VoterCanAdvance(voterPhase, "SignPending"), 
                                "Failure of assertion at line 156, column 5.")
                      /\ voterPhase' = "SignPending"
                      /\ signStarted' = now
                      /\ chVCDToVoter' = NoMsg
                      /\ pc' = [pc EXCEPT ![VoterPid] = "Voter_ApproveSign"]
                      /\ UNCHANGED << now, chVCDToCS, chCSToVCD, 
                                      chCSToProvider, chProviderToCS, 
                                      chProviderToSign, chSignToProvider, 
                                      chSignToVoter, chVoterToSign, chCSToReg, 
                                      chRegToCS, chVCDToVVD, chVVDToCS, 
                                      chCSToVVD, chVVDToVoter, authStarted, 
                                      verifyStarted, accepted, voterAccept, 
                                      verifiedBDOCs, vcdCtx, vcdChoice, 
                                      vcdVoteBDOC, vcdVoteReq, vcdVoteRes, 
                                      vcdRand, vcdCfg, csSessionStore, 
                                      csBallotStore, csLatest, csDroppedBallot, 
                                      csReqCnt, csFreshnessStore, csCfg, 
                                      providerSessionStore, providerCertStore, 
                                      provAuthSid, provSignSid, 
                                      signAuthChallenge, authPhone, 
                                      signChallenge, signPhone, regStore, 
                                      regNextIdx, regOcspStore, regNextOCSPIdx, 
                                      regDroppedLogEntry, vvdSidCS, vvdVid, 
                                      vvdRand, vvdChoice, vvdAccepted, 
                                      vvdRejected, vvdCfg >>

Voter_ApproveSign == /\ pc[VoterPid] = "Voter_ApproveSign"
                     /\ /\ chVCDToVoter.tag = "SignChallengeDisplay" /\ chSignToVoter.tag = "SignChallengeDisplay"
                     /\ Assert(voterPhase = "SignPending", 
                               "Failure of assertion at line 163, column 5.")
                     /\ Assert(voterChoice # NoStr, 
                               "Failure of assertion at line 164, column 5.")
                     /\ Assert(now <= signStarted + ReactionTimeVoter, 
                               "Failure of assertion at line 165, column 5.")
                     /\ Assert(chVCDToVoter.body.payload.challenge = chSignToVoter.body.payload.challenge, 
                               "Failure of assertion at line 166, column 5.")
                     /\ chVoterToVCD' = VoterToVCD("ApproveSign", NoBody)
                     /\ chVoterToSign' = VoterToSign("ApproveSign", NoBody)
                     /\ Assert(VoterCanAdvance(voterPhase, "VerifyPending"), 
                               "Failure of assertion at line 171, column 5.")
                     /\ voterPhase' = "VerifyPending"
                     /\ chVCDToVoter' = NoMsg
                     /\ chSignToVoter' = NoMsg
                     /\ pc' = [pc EXCEPT ![VoterPid] = "Voter_VerifyReq"]
                     /\ UNCHANGED << now, chVCDToCS, chCSToVCD, chCSToProvider, 
                                     chProviderToCS, chProviderToSign, 
                                     chSignToProvider, chCSToReg, chRegToCS, 
                                     chVCDToVVD, chVVDToCS, chCSToVVD, 
                                     chVVDToVoter, voterChoice, authStarted, 
                                     signStarted, verifyStarted, accepted, 
                                     voterAccept, verifiedBDOCs, vcdCtx, 
                                     vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                     vcdVoteRes, vcdRand, vcdCfg, 
                                     csSessionStore, csBallotStore, csLatest, 
                                     csDroppedBallot, csReqCnt, 
                                     csFreshnessStore, csCfg, 
                                     providerSessionStore, providerCertStore, 
                                     provAuthSid, provSignSid, 
                                     signAuthChallenge, authPhone, 
                                     signChallenge, signPhone, regStore, 
                                     regNextIdx, regOcspStore, regNextOCSPIdx, 
                                     regDroppedLogEntry, vvdSidCS, vvdVid, 
                                     vvdRand, vvdChoice, vvdAccepted, 
                                     vvdRejected, vvdCfg >>

Voter_VerifyReq == /\ pc[VoterPid] = "Voter_VerifyReq"
                   /\ chVCDToVoter.tag = "Voted"
                   /\ Assert(voterPhase = "VerifyPending", 
                             "Failure of assertion at line 178, column 5.")
                   /\ chVoterToVCD' = VoterToVCD("StartVerify", NoBody)
                   /\ verifyStarted' = now
                   /\ chVCDToVoter' = NoMsg
                   /\ pc' = [pc EXCEPT ![VoterPid] = "Voter_VerifyBallot"]
                   /\ UNCHANGED << now, chVCDToCS, chCSToVCD, chCSToProvider, 
                                   chProviderToCS, chProviderToSign, 
                                   chSignToProvider, chSignToVoter, 
                                   chVoterToSign, chCSToReg, chRegToCS, 
                                   chVCDToVVD, chVVDToCS, chCSToVVD, 
                                   chVVDToVoter, voterPhase, voterChoice, 
                                   authStarted, signStarted, accepted, 
                                   voterAccept, verifiedBDOCs, vcdCtx, 
                                   vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                   vcdVoteRes, vcdRand, vcdCfg, csSessionStore, 
                                   csBallotStore, csLatest, csDroppedBallot, 
                                   csReqCnt, csFreshnessStore, csCfg, 
                                   providerSessionStore, providerCertStore, 
                                   provAuthSid, provSignSid, signAuthChallenge, 
                                   authPhone, signChallenge, signPhone, 
                                   regStore, regNextIdx, regOcspStore, 
                                   regNextOCSPIdx, regDroppedLogEntry, 
                                   vvdSidCS, vvdVid, vvdRand, vvdChoice, 
                                   vvdAccepted, vvdRejected, vvdCfg >>

Voter_VerifyBallot == /\ pc[VoterPid] = "Voter_VerifyBallot"
                      /\ chVVDToVoter.tag = "VerifyDisplay" \/ chVVDToVoter.tag = "VerifyFailed" \/ now > verifyStarted + ReactionTimeVoter
                      /\ Assert(voterPhase = "VerifyPending", 
                                "Failure of assertion at line 185, column 5.")
                      /\ IF chVVDToVoter.tag = "VerifyDisplay"
                            THEN /\ Assert(now <= verifyStarted + VerifyWindowVoter, 
                                           "Failure of assertion at line 187, column 7.")
                                 /\ Assert(chVVDToVoter.body.payload.choice = voterChoice, 
                                           "Failure of assertion at line 188, column 7.")
                                 /\ Assert(VoterCanAdvance(voterPhase, "Verified"), 
                                           "Failure of assertion at line 189, column 7.")
                                 /\ accepted' = TRUE
                                 /\ voterAccept' = chVVDToVoter.body.payload.choice
                                 /\ voterPhase' = "Verified"
                                 /\ verifiedBDOCs' = (verifiedBDOCs \cup {chVVDToVoter.body.payload.bdoc})
                            ELSE /\ accepted' = FALSE
                                 /\ voterAccept' = NoStr
                                 /\ IF chVVDToVoter.tag = "VerifyFailed"
                                       THEN /\ voterPhase' = "Verified"
                                       ELSE /\ voterPhase' = "Verified"
                                 /\ UNCHANGED verifiedBDOCs
                      /\ chVVDToVoter' = NoMsg
                      /\ pc' = [pc EXCEPT ![VoterPid] = "Voter_Done"]
                      /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                      chVCDToCS, chCSToVCD, chCSToProvider, 
                                      chProviderToCS, chProviderToSign, 
                                      chSignToProvider, chSignToVoter, 
                                      chVoterToSign, chCSToReg, chRegToCS, 
                                      chVCDToVVD, chVVDToCS, chCSToVVD, 
                                      voterChoice, authStarted, signStarted, 
                                      verifyStarted, vcdCtx, vcdChoice, 
                                      vcdVoteBDOC, vcdVoteReq, vcdVoteRes, 
                                      vcdRand, vcdCfg, csSessionStore, 
                                      csBallotStore, csLatest, csDroppedBallot, 
                                      csReqCnt, csFreshnessStore, csCfg, 
                                      providerSessionStore, providerCertStore, 
                                      provAuthSid, provSignSid, 
                                      signAuthChallenge, authPhone, 
                                      signChallenge, signPhone, regStore, 
                                      regNextIdx, regOcspStore, regNextOCSPIdx, 
                                      regDroppedLogEntry, vvdSidCS, vvdVid, 
                                      vvdRand, vvdChoice, vvdAccepted, 
                                      vvdRejected, vvdCfg >>

Voter_Done == /\ pc[VoterPid] = "Voter_Done"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![VoterPid] = "Done"]
              /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, chVCDToCS, 
                              chCSToVCD, chCSToProvider, chProviderToCS, 
                              chProviderToSign, chSignToProvider, 
                              chSignToVoter, chVoterToSign, chCSToReg, 
                              chRegToCS, chVCDToVVD, chVVDToCS, chCSToVVD, 
                              chVVDToVoter, voterPhase, voterChoice, 
                              authStarted, signStarted, verifyStarted, 
                              accepted, voterAccept, verifiedBDOCs, vcdCtx, 
                              vcdChoice, vcdVoteBDOC, vcdVoteReq, vcdVoteRes, 
                              vcdRand, vcdCfg, csSessionStore, csBallotStore, 
                              csLatest, csDroppedBallot, csReqCnt, 
                              csFreshnessStore, csCfg, providerSessionStore, 
                              providerCertStore, provAuthSid, provSignSid, 
                              signAuthChallenge, authPhone, signChallenge, 
                              signPhone, regStore, regNextIdx, regOcspStore, 
                              regNextOCSPIdx, regDroppedLogEntry, vvdSidCS, 
                              vvdVid, vvdRand, vvdChoice, vvdAccepted, 
                              vvdRejected, vvdCfg >>

VoterProc == Voter_StartVoting \/ Voter_ApproveAuth \/ Voter_ChooseChoice
                \/ Voter_ApproveSign \/ Voter_VerifyReq
                \/ Voter_VerifyBallot \/ Voter_Done

VCD_RecvStartVoting == /\ pc[VCDPid] = "VCD_RecvStartVoting"
                       /\ chVoterToVCD.tag = "StartVoting"
                       /\ chVCDToCS' = VCDToCS("AuthReq", Empty, NoInt, Empty, chVoterToVCD.body.payload)
                       /\ chVoterToVCD' = NoMsg
                       /\ pc' = [pc EXCEPT ![VCDPid] = "VCD_RecvAuthRes"]
                       /\ UNCHANGED << now, chVCDToVoter, chCSToVCD, 
                                       chCSToProvider, chProviderToCS, 
                                       chProviderToSign, chSignToProvider, 
                                       chSignToVoter, chVoterToSign, chCSToReg, 
                                       chRegToCS, chVCDToVVD, chVVDToCS, 
                                       chCSToVVD, chVVDToVoter, voterPhase, 
                                       voterChoice, authStarted, signStarted, 
                                       verifyStarted, accepted, voterAccept, 
                                       verifiedBDOCs, vcdCtx, vcdChoice, 
                                       vcdVoteBDOC, vcdVoteReq, vcdVoteRes, 
                                       vcdRand, vcdCfg, csSessionStore, 
                                       csBallotStore, csLatest, 
                                       csDroppedBallot, csReqCnt, 
                                       csFreshnessStore, csCfg, 
                                       providerSessionStore, providerCertStore, 
                                       provAuthSid, provSignSid, 
                                       signAuthChallenge, authPhone, 
                                       signChallenge, signPhone, regStore, 
                                       regNextIdx, regOcspStore, 
                                       regNextOCSPIdx, regDroppedLogEntry, 
                                       vvdSidCS, vvdVid, vvdRand, vvdChoice, 
                                       vvdAccepted, vvdRejected, vvdCfg >>

VCD_RecvAuthRes == /\ pc[VCDPid] = "VCD_RecvAuthRes"
                   /\ chCSToVCD.tag = "AuthRes"
                   /\ vcdCtx' = [vcdCtx EXCEPT !.sidCS = chCSToVCD.body.sidCS, !.sidAuth = chCSToVCD.body.sidProv]
                   /\ chVCDToVoter' = VCDToVoter("AuthChallengeDisplay", chCSToVCD.body.payload)
                   /\ chCSToVCD' = NoMsg
                   /\ pc' = [pc EXCEPT ![VCDPid] = "VCD_RecvAuthApproval"]
                   /\ UNCHANGED << now, chVoterToVCD, chVCDToCS, 
                                   chCSToProvider, chProviderToCS, 
                                   chProviderToSign, chSignToProvider, 
                                   chSignToVoter, chVoterToSign, chCSToReg, 
                                   chRegToCS, chVCDToVVD, chVVDToCS, chCSToVVD, 
                                   chVVDToVoter, voterPhase, voterChoice, 
                                   authStarted, signStarted, verifyStarted, 
                                   accepted, voterAccept, verifiedBDOCs, 
                                   vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                   vcdVoteRes, vcdRand, vcdCfg, csSessionStore, 
                                   csBallotStore, csLatest, csDroppedBallot, 
                                   csReqCnt, csFreshnessStore, csCfg, 
                                   providerSessionStore, providerCertStore, 
                                   provAuthSid, provSignSid, signAuthChallenge, 
                                   authPhone, signChallenge, signPhone, 
                                   regStore, regNextIdx, regOcspStore, 
                                   regNextOCSPIdx, regDroppedLogEntry, 
                                   vvdSidCS, vvdVid, vvdRand, vvdChoice, 
                                   vvdAccepted, vvdRejected, vvdCfg >>

VCD_RecvAuthApproval == /\ pc[VCDPid] = "VCD_RecvAuthApproval"
                        /\ chVoterToVCD.tag = "ApproveAuth"
                        /\ chVCDToCS' = VCDToCS("AuthStatusReq", vcdCtx.sidCS, vcdCtx.sidAuth, Empty, NoBody)
                        /\ chVoterToVCD' = NoMsg
                        /\ pc' = [pc EXCEPT ![VCDPid] = "VCD_RecvAuthStatus"]
                        /\ UNCHANGED << now, chVCDToVoter, chCSToVCD, 
                                        chCSToProvider, chProviderToCS, 
                                        chProviderToSign, chSignToProvider, 
                                        chSignToVoter, chVoterToSign, 
                                        chCSToReg, chRegToCS, chVCDToVVD, 
                                        chVVDToCS, chCSToVVD, chVVDToVoter, 
                                        voterPhase, voterChoice, authStarted, 
                                        signStarted, verifyStarted, accepted, 
                                        voterAccept, verifiedBDOCs, vcdCtx, 
                                        vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                        vcdVoteRes, vcdRand, vcdCfg, 
                                        csSessionStore, csBallotStore, 
                                        csLatest, csDroppedBallot, csReqCnt, 
                                        csFreshnessStore, csCfg, 
                                        providerSessionStore, 
                                        providerCertStore, provAuthSid, 
                                        provSignSid, signAuthChallenge, 
                                        authPhone, signChallenge, signPhone, 
                                        regStore, regNextIdx, regOcspStore, 
                                        regNextOCSPIdx, regDroppedLogEntry, 
                                        vvdSidCS, vvdVid, vvdRand, vvdChoice, 
                                        vvdAccepted, vvdRejected, vvdCfg >>

VCD_RecvAuthStatus == /\ pc[VCDPid] = "VCD_RecvAuthStatus"
                      /\ chCSToVCD.tag = "AuthStatusRes"
                      /\ Assert(chCSToVCD.body.sidCS = vcdCtx.sidCS, 
                                "Failure of assertion at line 237, column 5.")
                      /\ vcdCtx' = [vcdCtx EXCEPT !.tok = chCSToVCD.body.payload]
                      /\ chCSToVCD' = NoMsg
                      /\ pc' = [pc EXCEPT ![VCDPid] = "VCD_SendChoicesReq"]
                      /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                      chVCDToCS, chCSToProvider, 
                                      chProviderToCS, chProviderToSign, 
                                      chSignToProvider, chSignToVoter, 
                                      chVoterToSign, chCSToReg, chRegToCS, 
                                      chVCDToVVD, chVVDToCS, chCSToVVD, 
                                      chVVDToVoter, voterPhase, voterChoice, 
                                      authStarted, signStarted, verifyStarted, 
                                      accepted, voterAccept, verifiedBDOCs, 
                                      vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                      vcdVoteRes, vcdRand, vcdCfg, 
                                      csSessionStore, csBallotStore, csLatest, 
                                      csDroppedBallot, csReqCnt, 
                                      csFreshnessStore, csCfg, 
                                      providerSessionStore, providerCertStore, 
                                      provAuthSid, provSignSid, 
                                      signAuthChallenge, authPhone, 
                                      signChallenge, signPhone, regStore, 
                                      regNextIdx, regOcspStore, regNextOCSPIdx, 
                                      regDroppedLogEntry, vvdSidCS, vvdVid, 
                                      vvdRand, vvdChoice, vvdAccepted, 
                                      vvdRejected, vvdCfg >>

VCD_SendChoicesReq == /\ pc[VCDPid] = "VCD_SendChoicesReq"
                      /\ chVCDToCS' = VCDToCS("ChoicesReq", vcdCtx.sidCS, NoInt, vcdCtx.tok, NoBody)
                      /\ pc' = [pc EXCEPT ![VCDPid] = "VCD_RecvChoices"]
                      /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                      chCSToVCD, chCSToProvider, 
                                      chProviderToCS, chProviderToSign, 
                                      chSignToProvider, chSignToVoter, 
                                      chVoterToSign, chCSToReg, chRegToCS, 
                                      chVCDToVVD, chVVDToCS, chCSToVVD, 
                                      chVVDToVoter, voterPhase, voterChoice, 
                                      authStarted, signStarted, verifyStarted, 
                                      accepted, voterAccept, verifiedBDOCs, 
                                      vcdCtx, vcdChoice, vcdVoteBDOC, 
                                      vcdVoteReq, vcdVoteRes, vcdRand, vcdCfg, 
                                      csSessionStore, csBallotStore, csLatest, 
                                      csDroppedBallot, csReqCnt, 
                                      csFreshnessStore, csCfg, 
                                      providerSessionStore, providerCertStore, 
                                      provAuthSid, provSignSid, 
                                      signAuthChallenge, authPhone, 
                                      signChallenge, signPhone, regStore, 
                                      regNextIdx, regOcspStore, regNextOCSPIdx, 
                                      regDroppedLogEntry, vvdSidCS, vvdVid, 
                                      vvdRand, vvdChoice, vvdAccepted, 
                                      vvdRejected, vvdCfg >>

VCD_RecvChoices == /\ pc[VCDPid] = "VCD_RecvChoices"
                   /\ chCSToVCD.tag = "ChoicesRes"
                   /\ Assert(chCSToVCD.body.sidCS = vcdCtx.sidCS, 
                             "Failure of assertion at line 246, column 5.")
                   /\ vcdCtx' = [vcdCtx EXCEPT !.choices = chCSToVCD.body.payload]
                   /\ chVCDToVoter' = VCDToVoter("ChoicesDisplay", chCSToVCD.body.payload)
                   /\ chCSToVCD' = NoMsg
                   /\ pc' = [pc EXCEPT ![VCDPid] = "VCD_RecvChoice"]
                   /\ UNCHANGED << now, chVoterToVCD, chVCDToCS, 
                                   chCSToProvider, chProviderToCS, 
                                   chProviderToSign, chSignToProvider, 
                                   chSignToVoter, chVoterToSign, chCSToReg, 
                                   chRegToCS, chVCDToVVD, chVVDToCS, chCSToVVD, 
                                   chVVDToVoter, voterPhase, voterChoice, 
                                   authStarted, signStarted, verifyStarted, 
                                   accepted, voterAccept, verifiedBDOCs, 
                                   vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                   vcdVoteRes, vcdRand, vcdCfg, csSessionStore, 
                                   csBallotStore, csLatest, csDroppedBallot, 
                                   csReqCnt, csFreshnessStore, csCfg, 
                                   providerSessionStore, providerCertStore, 
                                   provAuthSid, provSignSid, signAuthChallenge, 
                                   authPhone, signChallenge, signPhone, 
                                   regStore, regNextIdx, regOcspStore, 
                                   regNextOCSPIdx, regDroppedLogEntry, 
                                   vvdSidCS, vvdVid, vvdRand, vvdChoice, 
                                   vvdAccepted, vvdRejected, vvdCfg >>

VCD_RecvChoice == /\ pc[VCDPid] = "VCD_RecvChoice"
                  /\ chVoterToVCD.tag = "Choose"
                  /\ Assert(chVoterToVCD.body.payload \in vcdCtx.choices, 
                            "Failure of assertion at line 253, column 5.")
                  /\ vcdChoice' = chVoterToVCD.body.payload
                  /\ chVCDToCS' = VCDToCS("GetCertReq", vcdCtx.sidCS, NoInt, vcdCtx.tok, NoBody)
                  /\ chVoterToVCD' = NoMsg
                  /\ pc' = [pc EXCEPT ![VCDPid] = "VCD_RecvCert"]
                  /\ UNCHANGED << now, chVCDToVoter, chCSToVCD, chCSToProvider, 
                                  chProviderToCS, chProviderToSign, 
                                  chSignToProvider, chSignToVoter, 
                                  chVoterToSign, chCSToReg, chRegToCS, 
                                  chVCDToVVD, chVVDToCS, chCSToVVD, 
                                  chVVDToVoter, voterPhase, voterChoice, 
                                  authStarted, signStarted, verifyStarted, 
                                  accepted, voterAccept, verifiedBDOCs, vcdCtx, 
                                  vcdVoteBDOC, vcdVoteReq, vcdVoteRes, vcdRand, 
                                  vcdCfg, csSessionStore, csBallotStore, 
                                  csLatest, csDroppedBallot, csReqCnt, 
                                  csFreshnessStore, csCfg, 
                                  providerSessionStore, providerCertStore, 
                                  provAuthSid, provSignSid, signAuthChallenge, 
                                  authPhone, signChallenge, signPhone, 
                                  regStore, regNextIdx, regOcspStore, 
                                  regNextOCSPIdx, regDroppedLogEntry, vvdSidCS, 
                                  vvdVid, vvdRand, vvdChoice, vvdAccepted, 
                                  vvdRejected, vvdCfg >>

VCD_RecvCert == /\ pc[VCDPid] = "VCD_RecvCert"
                /\ chCSToVCD.tag = "CertRes"
                /\ Assert(chCSToVCD.body.sidCS = vcdCtx.sidCS, 
                          "Failure of assertion at line 260, column 5.")
                /\ LET cert == chCSToVCD.body.payload IN
                     /\ vcdVoteBDOC' = UnsignedBDOC(EGEnc(vcdCfg.decCert.pk, vcdChoice, vcdRand), cert)
                     /\ vcdCtx' = [vcdCtx EXCEPT !.r = vcdRand, !.bdoc = vcdVoteBDOC']
                     /\ chCSToVCD' = NoMsg
                /\ pc' = [pc EXCEPT ![VCDPid] = "VCD_SendSignReq"]
                /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, chVCDToCS, 
                                chCSToProvider, chProviderToCS, 
                                chProviderToSign, chSignToProvider, 
                                chSignToVoter, chVoterToSign, chCSToReg, 
                                chRegToCS, chVCDToVVD, chVVDToCS, chCSToVVD, 
                                chVVDToVoter, voterPhase, voterChoice, 
                                authStarted, signStarted, verifyStarted, 
                                accepted, voterAccept, verifiedBDOCs, 
                                vcdChoice, vcdVoteReq, vcdVoteRes, vcdRand, 
                                vcdCfg, csSessionStore, csBallotStore, 
                                csLatest, csDroppedBallot, csReqCnt, 
                                csFreshnessStore, csCfg, providerSessionStore, 
                                providerCertStore, provAuthSid, provSignSid, 
                                signAuthChallenge, authPhone, signChallenge, 
                                signPhone, regStore, regNextIdx, regOcspStore, 
                                regNextOCSPIdx, regDroppedLogEntry, vvdSidCS, 
                                vvdVid, vvdRand, vvdChoice, vvdAccepted, 
                                vvdRejected, vvdCfg >>

VCD_SendSignReq == /\ pc[VCDPid] = "VCD_SendSignReq"
                   /\ chVCDToCS' = VCDToCS("SignReq", vcdCtx.sidCS, NoInt, vcdCtx.tok, vcdCtx.bdoc.tbs)
                   /\ pc' = [pc EXCEPT ![VCDPid] = "VCD_RecvSignRes"]
                   /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, chCSToVCD, 
                                   chCSToProvider, chProviderToCS, 
                                   chProviderToSign, chSignToProvider, 
                                   chSignToVoter, chVoterToSign, chCSToReg, 
                                   chRegToCS, chVCDToVVD, chVVDToCS, chCSToVVD, 
                                   chVVDToVoter, voterPhase, voterChoice, 
                                   authStarted, signStarted, verifyStarted, 
                                   accepted, voterAccept, verifiedBDOCs, 
                                   vcdCtx, vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                   vcdVoteRes, vcdRand, vcdCfg, csSessionStore, 
                                   csBallotStore, csLatest, csDroppedBallot, 
                                   csReqCnt, csFreshnessStore, csCfg, 
                                   providerSessionStore, providerCertStore, 
                                   provAuthSid, provSignSid, signAuthChallenge, 
                                   authPhone, signChallenge, signPhone, 
                                   regStore, regNextIdx, regOcspStore, 
                                   regNextOCSPIdx, regDroppedLogEntry, 
                                   vvdSidCS, vvdVid, vvdRand, vvdChoice, 
                                   vvdAccepted, vvdRejected, vvdCfg >>

VCD_RecvSignRes == /\ pc[VCDPid] = "VCD_RecvSignRes"
                   /\ chCSToVCD.tag = "SignChallenge"
                   /\ Assert(chCSToVCD.body.sidCS = vcdCtx.sidCS, 
                             "Failure of assertion at line 272, column 5.")
                   /\ Assert(chCSToVCD.body.payload = vcdCtx.bdoc.tbs, 
                             "Failure of assertion at line 273, column 5.")
                   /\ vcdCtx' = [vcdCtx EXCEPT !.sidSign = chCSToVCD.body.sidProv]
                   /\ chVCDToVoter' = VCDToVoter("SignChallengeDisplay", [challenge |-> chCSToVCD.body.payload, cert |-> vcdCtx'.bdoc.signerCert])
                   /\ chCSToVCD' = NoMsg
                   /\ pc' = [pc EXCEPT ![VCDPid] = "VCD_SendSignStatusReq"]
                   /\ UNCHANGED << now, chVoterToVCD, chVCDToCS, 
                                   chCSToProvider, chProviderToCS, 
                                   chProviderToSign, chSignToProvider, 
                                   chSignToVoter, chVoterToSign, chCSToReg, 
                                   chRegToCS, chVCDToVVD, chVVDToCS, chCSToVVD, 
                                   chVVDToVoter, voterPhase, voterChoice, 
                                   authStarted, signStarted, verifyStarted, 
                                   accepted, voterAccept, verifiedBDOCs, 
                                   vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                   vcdVoteRes, vcdRand, vcdCfg, csSessionStore, 
                                   csBallotStore, csLatest, csDroppedBallot, 
                                   csReqCnt, csFreshnessStore, csCfg, 
                                   providerSessionStore, providerCertStore, 
                                   provAuthSid, provSignSid, signAuthChallenge, 
                                   authPhone, signChallenge, signPhone, 
                                   regStore, regNextIdx, regOcspStore, 
                                   regNextOCSPIdx, regDroppedLogEntry, 
                                   vvdSidCS, vvdVid, vvdRand, vvdChoice, 
                                   vvdAccepted, vvdRejected, vvdCfg >>

VCD_SendSignStatusReq == /\ pc[VCDPid] = "VCD_SendSignStatusReq"
                         /\ chVoterToVCD.tag = "ApproveSign"
                         /\ chVCDToCS' = VCDToCS("SignStatusReq", vcdCtx.sidCS, vcdCtx.sidSign, Empty, NoBody)
                         /\ chVoterToVCD' = NoMsg
                         /\ pc' = [pc EXCEPT ![VCDPid] = "VCD_RecvSignResult"]
                         /\ UNCHANGED << now, chVCDToVoter, chCSToVCD, 
                                         chCSToProvider, chProviderToCS, 
                                         chProviderToSign, chSignToProvider, 
                                         chSignToVoter, chVoterToSign, 
                                         chCSToReg, chRegToCS, chVCDToVVD, 
                                         chVVDToCS, chCSToVVD, chVVDToVoter, 
                                         voterPhase, voterChoice, authStarted, 
                                         signStarted, verifyStarted, accepted, 
                                         voterAccept, verifiedBDOCs, vcdCtx, 
                                         vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                         vcdVoteRes, vcdRand, vcdCfg, 
                                         csSessionStore, csBallotStore, 
                                         csLatest, csDroppedBallot, csReqCnt, 
                                         csFreshnessStore, csCfg, 
                                         providerSessionStore, 
                                         providerCertStore, provAuthSid, 
                                         provSignSid, signAuthChallenge, 
                                         authPhone, signChallenge, signPhone, 
                                         regStore, regNextIdx, regOcspStore, 
                                         regNextOCSPIdx, regDroppedLogEntry, 
                                         vvdSidCS, vvdVid, vvdRand, vvdChoice, 
                                         vvdAccepted, vvdRejected, vvdCfg >>

VCD_RecvSignResult == /\ pc[VCDPid] = "VCD_RecvSignResult"
                      /\ chCSToVCD.tag = "SignStatusRes"
                      /\ Assert(chCSToVCD.body.sidCS = vcdCtx.sidCS, 
                                "Failure of assertion at line 285, column 5.")
                      /\ Assert(Verify(vcdCtx.bdoc.signerCert.pk, vcdCtx.bdoc.tbs, chCSToVCD.body.payload), 
                                "Failure of assertion at line 286, column 9.")
                      /\ vcdVoteBDOC' = SignedBDOC(vcdCtx.bdoc.ct, vcdCtx.bdoc.signerCert, chCSToVCD.body.payload)
                      /\ vcdCtx' = [vcdCtx EXCEPT !.bdoc = vcdVoteBDOC']
                      /\ chCSToVCD' = NoMsg
                      /\ pc' = [pc EXCEPT ![VCDPid] = "VCD_SubmitVote"]
                      /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                      chVCDToCS, chCSToProvider, 
                                      chProviderToCS, chProviderToSign, 
                                      chSignToProvider, chSignToVoter, 
                                      chVoterToSign, chCSToReg, chRegToCS, 
                                      chVCDToVVD, chVVDToCS, chCSToVVD, 
                                      chVVDToVoter, voterPhase, voterChoice, 
                                      authStarted, signStarted, verifyStarted, 
                                      accepted, voterAccept, verifiedBDOCs, 
                                      vcdChoice, vcdVoteReq, vcdVoteRes, 
                                      vcdRand, vcdCfg, csSessionStore, 
                                      csBallotStore, csLatest, csDroppedBallot, 
                                      csReqCnt, csFreshnessStore, csCfg, 
                                      providerSessionStore, providerCertStore, 
                                      provAuthSid, provSignSid, 
                                      signAuthChallenge, authPhone, 
                                      signChallenge, signPhone, regStore, 
                                      regNextIdx, regOcspStore, regNextOCSPIdx, 
                                      regDroppedLogEntry, vvdSidCS, vvdVid, 
                                      vvdRand, vvdChoice, vvdAccepted, 
                                      vvdRejected, vvdCfg >>

VCD_SubmitVote == /\ pc[VCDPid] = "VCD_SubmitVote"
                  /\ vcdVoteReq' = VoteReq(vcdCtx.choices, vcdCtx.bdoc)
                  /\ chVCDToCS' = VCDToCS("VoteReq", vcdCtx.sidCS, NoInt, vcdCtx.tok, vcdVoteReq')
                  /\ pc' = [pc EXCEPT ![VCDPid] = "VCD_RecvVoteRes"]
                  /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, chCSToVCD, 
                                  chCSToProvider, chProviderToCS, 
                                  chProviderToSign, chSignToProvider, 
                                  chSignToVoter, chVoterToSign, chCSToReg, 
                                  chRegToCS, chVCDToVVD, chVVDToCS, chCSToVVD, 
                                  chVVDToVoter, voterPhase, voterChoice, 
                                  authStarted, signStarted, verifyStarted, 
                                  accepted, voterAccept, verifiedBDOCs, vcdCtx, 
                                  vcdChoice, vcdVoteBDOC, vcdVoteRes, vcdRand, 
                                  vcdCfg, csSessionStore, csBallotStore, 
                                  csLatest, csDroppedBallot, csReqCnt, 
                                  csFreshnessStore, csCfg, 
                                  providerSessionStore, providerCertStore, 
                                  provAuthSid, provSignSid, signAuthChallenge, 
                                  authPhone, signChallenge, signPhone, 
                                  regStore, regNextIdx, regOcspStore, 
                                  regNextOCSPIdx, regDroppedLogEntry, vvdSidCS, 
                                  vvdVid, vvdRand, vvdChoice, vvdAccepted, 
                                  vvdRejected, vvdCfg >>

VCD_RecvVoteRes == /\ pc[VCDPid] = "VCD_RecvVoteRes"
                   /\ chCSToVCD.tag = "VoteRes"
                   /\ Assert(chCSToVCD.body.sidCS = vcdCtx.sidCS, 
                             "Failure of assertion at line 297, column 5.")
                   /\ Assert(VerifyVoteRes(vcdCfg, chCSToVCD.body.payload, vcdVoteBDOC), 
                             "Failure of assertion at line 298, column 5.")
                   /\ vcdVoteRes' = chCSToVCD.body.payload
                   /\ chVCDToVoter' = VCDToVoter("Voted", NoBody)
                   /\ chCSToVCD' = NoMsg
                   /\ pc' = [pc EXCEPT ![VCDPid] = "VCD_SendToVVD"]
                   /\ UNCHANGED << now, chVoterToVCD, chVCDToCS, 
                                   chCSToProvider, chProviderToCS, 
                                   chProviderToSign, chSignToProvider, 
                                   chSignToVoter, chVoterToSign, chCSToReg, 
                                   chRegToCS, chVCDToVVD, chVVDToCS, chCSToVVD, 
                                   chVVDToVoter, voterPhase, voterChoice, 
                                   authStarted, signStarted, verifyStarted, 
                                   accepted, voterAccept, verifiedBDOCs, 
                                   vcdCtx, vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                   vcdRand, vcdCfg, csSessionStore, 
                                   csBallotStore, csLatest, csDroppedBallot, 
                                   csReqCnt, csFreshnessStore, csCfg, 
                                   providerSessionStore, providerCertStore, 
                                   provAuthSid, provSignSid, signAuthChallenge, 
                                   authPhone, signChallenge, signPhone, 
                                   regStore, regNextIdx, regOcspStore, 
                                   regNextOCSPIdx, regDroppedLogEntry, 
                                   vvdSidCS, vvdVid, vvdRand, vvdChoice, 
                                   vvdAccepted, vvdRejected, vvdCfg >>

VCD_SendToVVD == /\ pc[VCDPid] = "VCD_SendToVVD"
                 /\ chVoterToVCD.tag = "StartVerify"
                 /\ chVCDToVVD' = VCDToVVD("VerifyQR", vcdCtx.r, vcdVoteRes.vid, vcdCtx.sidCS)
                 /\ chVoterToVCD' = NoMsg
                 /\ pc' = [pc EXCEPT ![VCDPid] = "VCD_Done"]
                 /\ UNCHANGED << now, chVCDToVoter, chVCDToCS, chCSToVCD, 
                                 chCSToProvider, chProviderToCS, 
                                 chProviderToSign, chSignToProvider, 
                                 chSignToVoter, chVoterToSign, chCSToReg, 
                                 chRegToCS, chVVDToCS, chCSToVVD, chVVDToVoter, 
                                 voterPhase, voterChoice, authStarted, 
                                 signStarted, verifyStarted, accepted, 
                                 voterAccept, verifiedBDOCs, vcdCtx, vcdChoice, 
                                 vcdVoteBDOC, vcdVoteReq, vcdVoteRes, vcdRand, 
                                 vcdCfg, csSessionStore, csBallotStore, 
                                 csLatest, csDroppedBallot, csReqCnt, 
                                 csFreshnessStore, csCfg, providerSessionStore, 
                                 providerCertStore, provAuthSid, provSignSid, 
                                 signAuthChallenge, authPhone, signChallenge, 
                                 signPhone, regStore, regNextIdx, regOcspStore, 
                                 regNextOCSPIdx, regDroppedLogEntry, vvdSidCS, 
                                 vvdVid, vvdRand, vvdChoice, vvdAccepted, 
                                 vvdRejected, vvdCfg >>

VCD_Done == /\ pc[VCDPid] = "VCD_Done"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![VCDPid] = "Done"]
            /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, chVCDToCS, 
                            chCSToVCD, chCSToProvider, chProviderToCS, 
                            chProviderToSign, chSignToProvider, chSignToVoter, 
                            chVoterToSign, chCSToReg, chRegToCS, chVCDToVVD, 
                            chVVDToCS, chCSToVVD, chVVDToVoter, voterPhase, 
                            voterChoice, authStarted, signStarted, 
                            verifyStarted, accepted, voterAccept, 
                            verifiedBDOCs, vcdCtx, vcdChoice, vcdVoteBDOC, 
                            vcdVoteReq, vcdVoteRes, vcdRand, vcdCfg, 
                            csSessionStore, csBallotStore, csLatest, 
                            csDroppedBallot, csReqCnt, csFreshnessStore, csCfg, 
                            providerSessionStore, providerCertStore, 
                            provAuthSid, provSignSid, signAuthChallenge, 
                            authPhone, signChallenge, signPhone, regStore, 
                            regNextIdx, regOcspStore, regNextOCSPIdx, 
                            regDroppedLogEntry, vvdSidCS, vvdVid, vvdRand, 
                            vvdChoice, vvdAccepted, vvdRejected, vvdCfg >>

VCDProc == VCD_RecvStartVoting \/ VCD_RecvAuthRes \/ VCD_RecvAuthApproval
              \/ VCD_RecvAuthStatus \/ VCD_SendChoicesReq
              \/ VCD_RecvChoices \/ VCD_RecvChoice \/ VCD_RecvCert
              \/ VCD_SendSignReq \/ VCD_RecvSignRes
              \/ VCD_SendSignStatusReq \/ VCD_RecvSignResult
              \/ VCD_SubmitVote \/ VCD_RecvVoteRes \/ VCD_SendToVVD
              \/ VCD_Done

CS_RecvAuthReq == /\ pc[CSPid] = "CS_RecvAuthReq"
                  /\ chVCDToCS.tag = "AuthReq"
                  /\ csReqCnt' = csReqCnt + 1
                  /\ LET p == chVCDToCS.body.payload IN
                       LET req == csFreshnessStore[csReqCnt'] IN
                         /\ now' = now + 1
                         /\ LET upd == VerifyAndUpdateSession(csCfg, csSessionStore, req.csSid, "Auth", Empty, p, now') IN
                              /\ Assert(upd.ok, 
                                        "Failure of assertion at line 330, column 9.")
                              /\ csSessionStore' = StorePut(upd.store, req.csSid, [upd.session EXCEPT !.ctx = FreshSessionCtx(req)])
                         /\ chCSToProvider' = CSToProvider("AuthStart", req.csSid, NoInt, [challenge |-> req.authChallenge, voterRef |-> VoterRef(p.voterId, p.phone)])
                         /\ chVCDToCS' = NoMsg
                  /\ pc' = [pc EXCEPT ![CSPid] = "CS_RecvAuthStarted"]
                  /\ UNCHANGED << chVoterToVCD, chVCDToVoter, chCSToVCD, 
                                  chProviderToCS, chProviderToSign, 
                                  chSignToProvider, chSignToVoter, 
                                  chVoterToSign, chCSToReg, chRegToCS, 
                                  chVCDToVVD, chVVDToCS, chCSToVVD, 
                                  chVVDToVoter, voterPhase, voterChoice, 
                                  authStarted, signStarted, verifyStarted, 
                                  accepted, voterAccept, verifiedBDOCs, vcdCtx, 
                                  vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                  vcdVoteRes, vcdRand, vcdCfg, csBallotStore, 
                                  csLatest, csDroppedBallot, csFreshnessStore, 
                                  csCfg, providerSessionStore, 
                                  providerCertStore, provAuthSid, provSignSid, 
                                  signAuthChallenge, authPhone, signChallenge, 
                                  signPhone, regStore, regNextIdx, 
                                  regOcspStore, regNextOCSPIdx, 
                                  regDroppedLogEntry, vvdSidCS, vvdVid, 
                                  vvdRand, vvdChoice, vvdAccepted, vvdRejected, 
                                  vvdCfg >>

CS_RecvAuthStarted == /\ pc[CSPid] = "CS_RecvAuthStarted"
                      /\ chProviderToCS.tag = "AuthStarted"
                      /\ LET session == StoreLookup(csSessionStore, chProviderToCS.body.sidCS) IN
                           /\ Assert(session # Empty, 
                                     "Failure of assertion at line 340, column 7.")
                           /\ Assert(chProviderToCS.body.payload.challenge = session.ctx.authChallenge, 
                                     "Failure of assertion at line 341, column 25.")
                           /\ chCSToVCD' = CSToVCD("AuthRes", chProviderToCS.body.sidCS, chProviderToCS.body.sidProv, chProviderToCS.body.payload)
                           /\ chProviderToCS' = NoMsg
                      /\ pc' = [pc EXCEPT ![CSPid] = "CS_SendAuthStatusReq"]
                      /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                      chVCDToCS, chCSToProvider, 
                                      chProviderToSign, chSignToProvider, 
                                      chSignToVoter, chVoterToSign, chCSToReg, 
                                      chRegToCS, chVCDToVVD, chVVDToCS, 
                                      chCSToVVD, chVVDToVoter, voterPhase, 
                                      voterChoice, authStarted, signStarted, 
                                      verifyStarted, accepted, voterAccept, 
                                      verifiedBDOCs, vcdCtx, vcdChoice, 
                                      vcdVoteBDOC, vcdVoteReq, vcdVoteRes, 
                                      vcdRand, vcdCfg, csSessionStore, 
                                      csBallotStore, csLatest, csDroppedBallot, 
                                      csReqCnt, csFreshnessStore, csCfg, 
                                      providerSessionStore, providerCertStore, 
                                      provAuthSid, provSignSid, 
                                      signAuthChallenge, authPhone, 
                                      signChallenge, signPhone, regStore, 
                                      regNextIdx, regOcspStore, regNextOCSPIdx, 
                                      regDroppedLogEntry, vvdSidCS, vvdVid, 
                                      vvdRand, vvdChoice, vvdAccepted, 
                                      vvdRejected, vvdCfg >>

CS_SendAuthStatusReq == /\ pc[CSPid] = "CS_SendAuthStatusReq"
                        /\ chVCDToCS.tag = "AuthStatusReq"
                        /\ now' = now + 1
                        /\ LET upd == VerifyAndUpdateSession(csCfg, csSessionStore, chVCDToCS.body.sidCS, "AuthStatus", Empty, NoVoterRef, now') IN
                             /\ Assert(upd.ok, 
                                       "Failure of assertion at line 350, column 7.")
                             /\ csSessionStore' = upd.store
                             /\ chCSToProvider' = CSToProvider("AuthStatusReq", chVCDToCS.body.sidCS, chVCDToCS.body.sidProv, NoBody)
                             /\ chVCDToCS' = NoMsg
                        /\ pc' = [pc EXCEPT ![CSPid] = "CS_RecvAuthStatusRes"]
                        /\ UNCHANGED << chVoterToVCD, chVCDToVoter, chCSToVCD, 
                                        chProviderToCS, chProviderToSign, 
                                        chSignToProvider, chSignToVoter, 
                                        chVoterToSign, chCSToReg, chRegToCS, 
                                        chVCDToVVD, chVVDToCS, chCSToVVD, 
                                        chVVDToVoter, voterPhase, voterChoice, 
                                        authStarted, signStarted, 
                                        verifyStarted, accepted, voterAccept, 
                                        verifiedBDOCs, vcdCtx, vcdChoice, 
                                        vcdVoteBDOC, vcdVoteReq, vcdVoteRes, 
                                        vcdRand, vcdCfg, csBallotStore, 
                                        csLatest, csDroppedBallot, csReqCnt, 
                                        csFreshnessStore, csCfg, 
                                        providerSessionStore, 
                                        providerCertStore, provAuthSid, 
                                        provSignSid, signAuthChallenge, 
                                        authPhone, signChallenge, signPhone, 
                                        regStore, regNextIdx, regOcspStore, 
                                        regNextOCSPIdx, regDroppedLogEntry, 
                                        vvdSidCS, vvdVid, vvdRand, vvdChoice, 
                                        vvdAccepted, vvdRejected, vvdCfg >>

CS_RecvAuthStatusRes == /\ pc[CSPid] = "CS_RecvAuthStatusRes"
                        /\ chProviderToCS.tag = "AuthStatusRes"
                        /\ LET cert == chProviderToCS.body.payload.cert IN
                             LET session == StoreLookup(csSessionStore, chProviderToCS.body.sidCS) IN
                               /\ Assert(session # Empty, 
                                         "Failure of assertion at line 360, column 9.")
                               /\ Assert(VerifyTrustedX509Cert(csCfg.cfg.rootCACert, cert), 
                                         "Failure of assertion at line 361, column 33.")
                               /\ Assert(Verify(cert.pk, session.ctx.authChallenge, chProviderToCS.body.payload.sig), 
                                         "Failure of assertion at line 362, column 33.")
                               /\ LET tok == CreateAuthToken(CSSymKey, cert, session.ctx.issuedVid, session.ctx.authTokNonce) IN
                                    /\ csSessionStore' = StorePut(csSessionStore,
                                                                                                                                                       chProviderToCS.body.sidCS,
                                                                                                                                                       [session EXCEPT !.phase = "AuthStatus", !.tok = tok, !.exp = now + csCfg.stageTTL])
                                    /\ chCSToVCD' = CSToVCD("AuthStatusRes", chProviderToCS.body.sidCS, NoInt, tok)
                        /\ chProviderToCS' = NoMsg
                        /\ pc' = [pc EXCEPT ![CSPid] = "CS_RecvChoicesReq"]
                        /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                        chVCDToCS, chCSToProvider, 
                                        chProviderToSign, chSignToProvider, 
                                        chSignToVoter, chVoterToSign, 
                                        chCSToReg, chRegToCS, chVCDToVVD, 
                                        chVVDToCS, chCSToVVD, chVVDToVoter, 
                                        voterPhase, voterChoice, authStarted, 
                                        signStarted, verifyStarted, accepted, 
                                        voterAccept, verifiedBDOCs, vcdCtx, 
                                        vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                        vcdVoteRes, vcdRand, vcdCfg, 
                                        csBallotStore, csLatest, 
                                        csDroppedBallot, csReqCnt, 
                                        csFreshnessStore, csCfg, 
                                        providerSessionStore, 
                                        providerCertStore, provAuthSid, 
                                        provSignSid, signAuthChallenge, 
                                        authPhone, signChallenge, signPhone, 
                                        regStore, regNextIdx, regOcspStore, 
                                        regNextOCSPIdx, regDroppedLogEntry, 
                                        vvdSidCS, vvdVid, vvdRand, vvdChoice, 
                                        vvdAccepted, vvdRejected, vvdCfg >>

CS_RecvChoicesReq == /\ pc[CSPid] = "CS_RecvChoicesReq"
                     /\ chVCDToCS.tag = "ChoicesReq"
                     /\ now' = now + 1
                     /\ LET upd == VerifyAndUpdateSession(csCfg, csSessionStore, chVCDToCS.body.sidCS, "Choices", chVCDToCS.body.tok, NoVoterRef, now') IN
                          /\ Assert(upd.ok, 
                                    "Failure of assertion at line 377, column 7.")
                          /\ csSessionStore' = upd.store
                          /\ chCSToVCD' = CSToVCD("ChoicesRes", chVCDToCS.body.sidCS, NoInt, csCfg.cfg.choices)
                          /\ chVCDToCS' = NoMsg
                     /\ pc' = [pc EXCEPT ![CSPid] = "CS_RecvGetCertReq"]
                     /\ UNCHANGED << chVoterToVCD, chVCDToVoter, 
                                     chCSToProvider, chProviderToCS, 
                                     chProviderToSign, chSignToProvider, 
                                     chSignToVoter, chVoterToSign, chCSToReg, 
                                     chRegToCS, chVCDToVVD, chVVDToCS, 
                                     chCSToVVD, chVVDToVoter, voterPhase, 
                                     voterChoice, authStarted, signStarted, 
                                     verifyStarted, accepted, voterAccept, 
                                     verifiedBDOCs, vcdCtx, vcdChoice, 
                                     vcdVoteBDOC, vcdVoteReq, vcdVoteRes, 
                                     vcdRand, vcdCfg, csBallotStore, csLatest, 
                                     csDroppedBallot, csReqCnt, 
                                     csFreshnessStore, csCfg, 
                                     providerSessionStore, providerCertStore, 
                                     provAuthSid, provSignSid, 
                                     signAuthChallenge, authPhone, 
                                     signChallenge, signPhone, regStore, 
                                     regNextIdx, regOcspStore, regNextOCSPIdx, 
                                     regDroppedLogEntry, vvdSidCS, vvdVid, 
                                     vvdRand, vvdChoice, vvdAccepted, 
                                     vvdRejected, vvdCfg >>

CS_RecvGetCertReq == /\ pc[CSPid] = "CS_RecvGetCertReq"
                     /\ chVCDToCS.tag = "GetCertReq"
                     /\ now' = now + 1
                     /\ LET upd == VerifyAndUpdateSession(csCfg, csSessionStore, chVCDToCS.body.sidCS, "Cert", chVCDToCS.body.tok, NoVoterRef, now') IN
                          /\ Assert(upd.ok, 
                                    "Failure of assertion at line 387, column 7.")
                          /\ csSessionStore' = upd.store
                          /\ chCSToProvider' = CSToProvider("GetCertReq", chVCDToCS.body.sidCS, NoInt, [phone |-> upd.session.phone])
                          /\ chVCDToCS' = NoMsg
                     /\ pc' = [pc EXCEPT ![CSPid] = "CS_RecvGetCertRes"]
                     /\ UNCHANGED << chVoterToVCD, chVCDToVoter, chCSToVCD, 
                                     chProviderToCS, chProviderToSign, 
                                     chSignToProvider, chSignToVoter, 
                                     chVoterToSign, chCSToReg, chRegToCS, 
                                     chVCDToVVD, chVVDToCS, chCSToVVD, 
                                     chVVDToVoter, voterPhase, voterChoice, 
                                     authStarted, signStarted, verifyStarted, 
                                     accepted, voterAccept, verifiedBDOCs, 
                                     vcdCtx, vcdChoice, vcdVoteBDOC, 
                                     vcdVoteReq, vcdVoteRes, vcdRand, vcdCfg, 
                                     csBallotStore, csLatest, csDroppedBallot, 
                                     csReqCnt, csFreshnessStore, csCfg, 
                                     providerSessionStore, providerCertStore, 
                                     provAuthSid, provSignSid, 
                                     signAuthChallenge, authPhone, 
                                     signChallenge, signPhone, regStore, 
                                     regNextIdx, regOcspStore, regNextOCSPIdx, 
                                     regDroppedLogEntry, vvdSidCS, vvdVid, 
                                     vvdRand, vvdChoice, vvdAccepted, 
                                     vvdRejected, vvdCfg >>

CS_RecvGetCertRes == /\ pc[CSPid] = "CS_RecvGetCertRes"
                     /\ chProviderToCS.tag = "GetCertRes"
                     /\ Assert(StoreLookup(csSessionStore, chProviderToCS.body.sidCS) # Empty, 
                               "Failure of assertion at line 395, column 5.")
                     /\ chCSToVCD' = CSToVCD("CertRes", chProviderToCS.body.sidCS, NoInt, chProviderToCS.body.payload)
                     /\ chProviderToCS' = NoMsg
                     /\ pc' = [pc EXCEPT ![CSPid] = "CS_RecvSignReq"]
                     /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                     chVCDToCS, chCSToProvider, 
                                     chProviderToSign, chSignToProvider, 
                                     chSignToVoter, chVoterToSign, chCSToReg, 
                                     chRegToCS, chVCDToVVD, chVVDToCS, 
                                     chCSToVVD, chVVDToVoter, voterPhase, 
                                     voterChoice, authStarted, signStarted, 
                                     verifyStarted, accepted, voterAccept, 
                                     verifiedBDOCs, vcdCtx, vcdChoice, 
                                     vcdVoteBDOC, vcdVoteReq, vcdVoteRes, 
                                     vcdRand, vcdCfg, csSessionStore, 
                                     csBallotStore, csLatest, csDroppedBallot, 
                                     csReqCnt, csFreshnessStore, csCfg, 
                                     providerSessionStore, providerCertStore, 
                                     provAuthSid, provSignSid, 
                                     signAuthChallenge, authPhone, 
                                     signChallenge, signPhone, regStore, 
                                     regNextIdx, regOcspStore, regNextOCSPIdx, 
                                     regDroppedLogEntry, vvdSidCS, vvdVid, 
                                     vvdRand, vvdChoice, vvdAccepted, 
                                     vvdRejected, vvdCfg >>

CS_RecvSignReq == /\ pc[CSPid] = "CS_RecvSignReq"
                  /\ chVCDToCS.tag = "SignReq"
                  /\ now' = now + 1
                  /\ LET upd == VerifyAndUpdateSession(csCfg, csSessionStore, chVCDToCS.body.sidCS, "Sign", chVCDToCS.body.tok, NoVoterRef, now') IN
                       /\ Assert(upd.ok, 
                                 "Failure of assertion at line 403, column 7.")
                       /\ LET session == [upd.session EXCEPT !.ctx.signDigest = chVCDToCS.body.payload] IN
                            /\ csSessionStore' = StorePut(upd.store, chVCDToCS.body.sidCS, session)
                            /\ chCSToProvider' = CSToProvider("SignStart", chVCDToCS.body.sidCS, NoInt, [challenge |-> session.ctx.signDigest, voterRef |-> VoterRef(session.voterId, session.phone)])
                       /\ chVCDToCS' = NoMsg
                  /\ pc' = [pc EXCEPT ![CSPid] = "CS_RecvSignStarted"]
                  /\ UNCHANGED << chVoterToVCD, chVCDToVoter, chCSToVCD, 
                                  chProviderToCS, chProviderToSign, 
                                  chSignToProvider, chSignToVoter, 
                                  chVoterToSign, chCSToReg, chRegToCS, 
                                  chVCDToVVD, chVVDToCS, chCSToVVD, 
                                  chVVDToVoter, voterPhase, voterChoice, 
                                  authStarted, signStarted, verifyStarted, 
                                  accepted, voterAccept, verifiedBDOCs, vcdCtx, 
                                  vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                  vcdVoteRes, vcdRand, vcdCfg, csBallotStore, 
                                  csLatest, csDroppedBallot, csReqCnt, 
                                  csFreshnessStore, csCfg, 
                                  providerSessionStore, providerCertStore, 
                                  provAuthSid, provSignSid, signAuthChallenge, 
                                  authPhone, signChallenge, signPhone, 
                                  regStore, regNextIdx, regOcspStore, 
                                  regNextOCSPIdx, regDroppedLogEntry, vvdSidCS, 
                                  vvdVid, vvdRand, vvdChoice, vvdAccepted, 
                                  vvdRejected, vvdCfg >>

CS_RecvSignStarted == /\ pc[CSPid] = "CS_RecvSignStarted"
                      /\ chProviderToCS.tag = "SignStarted"
                      /\ LET session == StoreLookup(csSessionStore, chProviderToCS.body.sidCS) IN
                           /\ Assert(session # Empty, 
                                     "Failure of assertion at line 414, column 7.")
                           /\ chCSToVCD' = CSToVCD("SignChallenge", chProviderToCS.body.sidCS, chProviderToCS.body.sidProv, session.ctx.signDigest)
                      /\ chProviderToCS' = NoMsg
                      /\ pc' = [pc EXCEPT ![CSPid] = "CS_SendSignStatusReq"]
                      /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                      chVCDToCS, chCSToProvider, 
                                      chProviderToSign, chSignToProvider, 
                                      chSignToVoter, chVoterToSign, chCSToReg, 
                                      chRegToCS, chVCDToVVD, chVVDToCS, 
                                      chCSToVVD, chVVDToVoter, voterPhase, 
                                      voterChoice, authStarted, signStarted, 
                                      verifyStarted, accepted, voterAccept, 
                                      verifiedBDOCs, vcdCtx, vcdChoice, 
                                      vcdVoteBDOC, vcdVoteReq, vcdVoteRes, 
                                      vcdRand, vcdCfg, csSessionStore, 
                                      csBallotStore, csLatest, csDroppedBallot, 
                                      csReqCnt, csFreshnessStore, csCfg, 
                                      providerSessionStore, providerCertStore, 
                                      provAuthSid, provSignSid, 
                                      signAuthChallenge, authPhone, 
                                      signChallenge, signPhone, regStore, 
                                      regNextIdx, regOcspStore, regNextOCSPIdx, 
                                      regDroppedLogEntry, vvdSidCS, vvdVid, 
                                      vvdRand, vvdChoice, vvdAccepted, 
                                      vvdRejected, vvdCfg >>

CS_SendSignStatusReq == /\ pc[CSPid] = "CS_SendSignStatusReq"
                        /\ chVCDToCS.tag = "SignStatusReq"
                        /\ now' = now + 1
                        /\ LET upd == VerifyAndUpdateSession(csCfg, csSessionStore, chVCDToCS.body.sidCS, "SignStatus", Empty, NoVoterRef, now') IN
                             /\ Assert(upd.ok, 
                                       "Failure of assertion at line 423, column 7.")
                             /\ csSessionStore' = upd.store
                             /\ chCSToProvider' = CSToProvider("SignStatusReq", chVCDToCS.body.sidCS,  chVCDToCS.body.sidProv, NoBody)
                             /\ chVCDToCS' = NoMsg
                        /\ pc' = [pc EXCEPT ![CSPid] = "CS_RecvSignStatusRes"]
                        /\ UNCHANGED << chVoterToVCD, chVCDToVoter, chCSToVCD, 
                                        chProviderToCS, chProviderToSign, 
                                        chSignToProvider, chSignToVoter, 
                                        chVoterToSign, chCSToReg, chRegToCS, 
                                        chVCDToVVD, chVVDToCS, chCSToVVD, 
                                        chVVDToVoter, voterPhase, voterChoice, 
                                        authStarted, signStarted, 
                                        verifyStarted, accepted, voterAccept, 
                                        verifiedBDOCs, vcdCtx, vcdChoice, 
                                        vcdVoteBDOC, vcdVoteReq, vcdVoteRes, 
                                        vcdRand, vcdCfg, csBallotStore, 
                                        csLatest, csDroppedBallot, csReqCnt, 
                                        csFreshnessStore, csCfg, 
                                        providerSessionStore, 
                                        providerCertStore, provAuthSid, 
                                        provSignSid, signAuthChallenge, 
                                        authPhone, signChallenge, signPhone, 
                                        regStore, regNextIdx, regOcspStore, 
                                        regNextOCSPIdx, regDroppedLogEntry, 
                                        vvdSidCS, vvdVid, vvdRand, vvdChoice, 
                                        vvdAccepted, vvdRejected, vvdCfg >>

CS_RecvSignStatusRes == /\ pc[CSPid] = "CS_RecvSignStatusRes"
                        /\ chProviderToCS.tag = "SignStatusRes"
                        /\ LET session == StoreLookup(csSessionStore, chProviderToCS.body.sidCS) IN
                             /\ Assert(session # Empty, 
                                       "Failure of assertion at line 432, column 7.")
                             /\ csSessionStore' = StorePut(csSessionStore,
                                                             chProviderToCS.body.sidCS,
                                                             [session EXCEPT !.phase = "SignStatus", !.exp = now + csCfg.stageTTL])
                        /\ chCSToVCD' = CSToVCD("SignStatusRes", chProviderToCS.body.sidCS, chProviderToCS.body.sidProv, chProviderToCS.body.payload)
                        /\ chProviderToCS' = NoMsg
                        /\ pc' = [pc EXCEPT ![CSPid] = "CS_RecvVoteReq"]
                        /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                        chVCDToCS, chCSToProvider, 
                                        chProviderToSign, chSignToProvider, 
                                        chSignToVoter, chVoterToSign, 
                                        chCSToReg, chRegToCS, chVCDToVVD, 
                                        chVVDToCS, chCSToVVD, chVVDToVoter, 
                                        voterPhase, voterChoice, authStarted, 
                                        signStarted, verifyStarted, accepted, 
                                        voterAccept, verifiedBDOCs, vcdCtx, 
                                        vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                        vcdVoteRes, vcdRand, vcdCfg, 
                                        csBallotStore, csLatest, 
                                        csDroppedBallot, csReqCnt, 
                                        csFreshnessStore, csCfg, 
                                        providerSessionStore, 
                                        providerCertStore, provAuthSid, 
                                        provSignSid, signAuthChallenge, 
                                        authPhone, signChallenge, signPhone, 
                                        regStore, regNextIdx, regOcspStore, 
                                        regNextOCSPIdx, regDroppedLogEntry, 
                                        vvdSidCS, vvdVid, vvdRand, vvdChoice, 
                                        vvdAccepted, vvdRejected, vvdCfg >>

CS_RecvVoteReq == /\ pc[CSPid] = "CS_RecvVoteReq"
                  /\ chVCDToCS.tag = "VoteReq"
                  /\ now' = now + 1
                  /\ LET upd == VerifyAndUpdateSession(csCfg, csSessionStore, chVCDToCS.body.sidCS, "Vote", chVCDToCS.body.tok, NoVoterRef, now') IN
                       /\ Assert(upd.ok, 
                                 "Failure of assertion at line 444, column 7.")
                       /\ LET openedTok == OpenAuthToken(CSSymKey, chVCDToCS.body.tok) IN
                            LET p == chVCDToCS.body.payload IN
                              /\ Assert(openedTok # Empty, 
                                        "Failure of assertion at line 447, column 9.")
                              /\ Assert(openedTok[1] = p.bdoc.signerCert, 
                                        "Failure of assertion at line 448, column 35.")
                              /\ Assert(openedTok[2] = upd.session.ctx.issuedVid, 
                                        "Failure of assertion at line 449, column 35.")
                              /\ Assert(VerifyTrustedX509Cert(csCfg.cfg.rootCACert, p.bdoc.signerCert), 
                                        "Failure of assertion at line 450, column 35.")
                              /\ Assert(p.bdoc.signerCert.pnoee \in DOMAIN csCfg.voterList, 
                                        "Failure of assertion at line 451, column 35.")
                              /\ Assert(upd.session.voterId = p.bdoc.signerCert.pnoee, 
                                        "Failure of assertion at line 452, column 35.")
                              /\ Assert(Verify(p.bdoc.signerCert.pk, p.bdoc.tbs, p.bdoc.sig), 
                                        "Failure of assertion at line 453, column 35.")
                              /\ LET voteVid == upd.session.ctx.issuedVid IN
                                   LET tspReq == LET h == Hash(p.bdoc.sig) IN TSPReq(h, Sign(TSPClientSK, h)) IN
                                     LET ocspReq == OCSPReq(p.bdoc.signerCert) IN
                                       LET session == [upd.session EXCEPT !.ctx.voteVid = voteVid,
                                                                           !.ctx.tspReq = LET h == Hash(p.bdoc.sig) IN TSPReq(h, Sign(TSPClientSK, h)),
                                                                           !.ctx.ocspReq = OCSPReq(p.bdoc.signerCert)] IN
                                         /\ csSessionStore' = StorePut(upd.store, chVCDToCS.body.sidCS, session)
                                         /\ csBallotStore' =            StorePut(csBallotStore,
                                                             voteVid,
                                                             StoredVote(voteVid, upd.session.voterId, now', p.bdoc, NoTSPRes, NoOCSPRes, 0))
                  /\ pc' = [pc EXCEPT ![CSPid] = "CS_SendTSPReq"]
                  /\ UNCHANGED << chVoterToVCD, chVCDToVoter, chVCDToCS, 
                                  chCSToVCD, chCSToProvider, chProviderToCS, 
                                  chProviderToSign, chSignToProvider, 
                                  chSignToVoter, chVoterToSign, chCSToReg, 
                                  chRegToCS, chVCDToVVD, chVVDToCS, chCSToVVD, 
                                  chVVDToVoter, voterPhase, voterChoice, 
                                  authStarted, signStarted, verifyStarted, 
                                  accepted, voterAccept, verifiedBDOCs, vcdCtx, 
                                  vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                  vcdVoteRes, vcdRand, vcdCfg, csLatest, 
                                  csDroppedBallot, csReqCnt, csFreshnessStore, 
                                  csCfg, providerSessionStore, 
                                  providerCertStore, provAuthSid, provSignSid, 
                                  signAuthChallenge, authPhone, signChallenge, 
                                  signPhone, regStore, regNextIdx, 
                                  regOcspStore, regNextOCSPIdx, 
                                  regDroppedLogEntry, vvdSidCS, vvdVid, 
                                  vvdRand, vvdChoice, vvdAccepted, vvdRejected, 
                                  vvdCfg >>

CS_SendTSPReq == /\ pc[CSPid] = "CS_SendTSPReq"
                 /\ LET sid == ActiveVoteSessionSid(csSessionStore) IN
                      LET session == StoreLookup(csSessionStore, ActiveVoteSessionSid(csSessionStore)) IN
                        /\ Assert(sid # Empty, 
                                  "Failure of assertion at line 471, column 7.")
                        /\ Assert(session # Empty, 
                                  "Failure of assertion at line 472, column 7.")
                        /\ chCSToReg' = CSToReg("TSPReq", session.ctx.tspReq)
                 /\ pc' = [pc EXCEPT ![CSPid] = "CS_RecvTSPRes"]
                 /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, chVCDToCS, 
                                 chCSToVCD, chCSToProvider, chProviderToCS, 
                                 chProviderToSign, chSignToProvider, 
                                 chSignToVoter, chVoterToSign, chRegToCS, 
                                 chVCDToVVD, chVVDToCS, chCSToVVD, 
                                 chVVDToVoter, voterPhase, voterChoice, 
                                 authStarted, signStarted, verifyStarted, 
                                 accepted, voterAccept, verifiedBDOCs, vcdCtx, 
                                 vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                 vcdVoteRes, vcdRand, vcdCfg, csSessionStore, 
                                 csBallotStore, csLatest, csDroppedBallot, 
                                 csReqCnt, csFreshnessStore, csCfg, 
                                 providerSessionStore, providerCertStore, 
                                 provAuthSid, provSignSid, signAuthChallenge, 
                                 authPhone, signChallenge, signPhone, regStore, 
                                 regNextIdx, regOcspStore, regNextOCSPIdx, 
                                 regDroppedLogEntry, vvdSidCS, vvdVid, vvdRand, 
                                 vvdChoice, vvdAccepted, vvdRejected, vvdCfg >>

CS_RecvTSPRes == /\ pc[CSPid] = "CS_RecvTSPRes"
                 /\ chRegToCS.tag = "TSPRes"
                 /\ now' = now + 1
                 /\ LET sid == ActiveVoteSessionSid(csSessionStore) IN
                      LET session == StoreLookup(csSessionStore, ActiveVoteSessionSid(csSessionStore)) IN
                        /\ Assert(sid # Empty, 
                                  "Failure of assertion at line 481, column 7.")
                        /\ Assert(session # Empty, 
                                  "Failure of assertion at line 482, column 7.")
                        /\ Assert(VerifyTSPCS(csCfg, session.ctx.tspReq, chRegToCS.body.payload, now'), 
                                  "Failure of assertion at line 483, column 7.")
                        /\ csBallotStore' = [csBallotStore EXCEPT ![session.ctx.voteVid].tsp = chRegToCS.body.payload]
                 /\ chRegToCS' = NoMsg
                 /\ pc' = [pc EXCEPT ![CSPid] = "CS_SendOCSPReq"]
                 /\ UNCHANGED << chVoterToVCD, chVCDToVoter, chVCDToCS, 
                                 chCSToVCD, chCSToProvider, chProviderToCS, 
                                 chProviderToSign, chSignToProvider, 
                                 chSignToVoter, chVoterToSign, chCSToReg, 
                                 chVCDToVVD, chVVDToCS, chCSToVVD, 
                                 chVVDToVoter, voterPhase, voterChoice, 
                                 authStarted, signStarted, verifyStarted, 
                                 accepted, voterAccept, verifiedBDOCs, vcdCtx, 
                                 vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                 vcdVoteRes, vcdRand, vcdCfg, csSessionStore, 
                                 csLatest, csDroppedBallot, csReqCnt, 
                                 csFreshnessStore, csCfg, providerSessionStore, 
                                 providerCertStore, provAuthSid, provSignSid, 
                                 signAuthChallenge, authPhone, signChallenge, 
                                 signPhone, regStore, regNextIdx, regOcspStore, 
                                 regNextOCSPIdx, regDroppedLogEntry, vvdSidCS, 
                                 vvdVid, vvdRand, vvdChoice, vvdAccepted, 
                                 vvdRejected, vvdCfg >>

CS_SendOCSPReq == /\ pc[CSPid] = "CS_SendOCSPReq"
                  /\ LET sid == ActiveVoteSessionSid(csSessionStore) IN
                       LET session == StoreLookup(csSessionStore, ActiveVoteSessionSid(csSessionStore)) IN
                         /\ Assert(sid # Empty, 
                                   "Failure of assertion at line 491, column 7.")
                         /\ Assert(session # Empty, 
                                   "Failure of assertion at line 492, column 7.")
                         /\ chCSToReg' = CSToReg("OCSPReq", session.ctx.ocspReq)
                  /\ pc' = [pc EXCEPT ![CSPid] = "CS_RecvOCSPRes"]
                  /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, chVCDToCS, 
                                  chCSToVCD, chCSToProvider, chProviderToCS, 
                                  chProviderToSign, chSignToProvider, 
                                  chSignToVoter, chVoterToSign, chRegToCS, 
                                  chVCDToVVD, chVVDToCS, chCSToVVD, 
                                  chVVDToVoter, voterPhase, voterChoice, 
                                  authStarted, signStarted, verifyStarted, 
                                  accepted, voterAccept, verifiedBDOCs, vcdCtx, 
                                  vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                  vcdVoteRes, vcdRand, vcdCfg, csSessionStore, 
                                  csBallotStore, csLatest, csDroppedBallot, 
                                  csReqCnt, csFreshnessStore, csCfg, 
                                  providerSessionStore, providerCertStore, 
                                  provAuthSid, provSignSid, signAuthChallenge, 
                                  authPhone, signChallenge, signPhone, 
                                  regStore, regNextIdx, regOcspStore, 
                                  regNextOCSPIdx, regDroppedLogEntry, vvdSidCS, 
                                  vvdVid, vvdRand, vvdChoice, vvdAccepted, 
                                  vvdRejected, vvdCfg >>

CS_RecvOCSPRes == /\ pc[CSPid] = "CS_RecvOCSPRes"
                  /\ chRegToCS.tag = "OCSPRes"
                  /\ now' = now + 1
                  /\ LET sid == ActiveVoteSessionSid(csSessionStore) IN
                       LET session == StoreLookup(csSessionStore, ActiveVoteSessionSid(csSessionStore)) IN
                         LET ballot == StoreLookup(csBallotStore, StoreLookup(csSessionStore, ActiveVoteSessionSid(csSessionStore)).ctx.voteVid) IN
                           /\ Assert(sid # Empty, 
                                     "Failure of assertion at line 502, column 7.")
                           /\ Assert(session # Empty, 
                                     "Failure of assertion at line 503, column 7.")
                           /\ Assert(ballot # Empty, 
                                     "Failure of assertion at line 504, column 7.")
                           /\ Assert(VerifyOCSPCS(csCfg, session.ctx.ocspReq, chRegToCS.body.payload), 
                                     "Failure of assertion at line 505, column 7.")
                           /\ Assert(chRegToCS.body.payload.t >= ballot.tsp.t, 
                                     "Failure of assertion at line 506, column 7.")
                           /\ LET updatedStore == StorePut(csBallotStore,
                                                           session.ctx.voteVid,
                                                           [ballot EXCEPT !.ocsp = chRegToCS.body.payload]) IN
                                /\ csBallotStore' = updatedStore
                                /\ csLatest' = LatestVoteForVoter(updatedStore, ballot.voterId)
                  /\ chRegToCS' = NoMsg
                  /\ pc' = [pc EXCEPT ![CSPid] = "CS_SendVoteRes"]
                  /\ UNCHANGED << chVoterToVCD, chVCDToVoter, chVCDToCS, 
                                  chCSToVCD, chCSToProvider, chProviderToCS, 
                                  chProviderToSign, chSignToProvider, 
                                  chSignToVoter, chVoterToSign, chCSToReg, 
                                  chVCDToVVD, chVVDToCS, chCSToVVD, 
                                  chVVDToVoter, voterPhase, voterChoice, 
                                  authStarted, signStarted, verifyStarted, 
                                  accepted, voterAccept, verifiedBDOCs, vcdCtx, 
                                  vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                  vcdVoteRes, vcdRand, vcdCfg, csSessionStore, 
                                  csDroppedBallot, csReqCnt, csFreshnessStore, 
                                  csCfg, providerSessionStore, 
                                  providerCertStore, provAuthSid, provSignSid, 
                                  signAuthChallenge, authPhone, signChallenge, 
                                  signPhone, regStore, regNextIdx, 
                                  regOcspStore, regNextOCSPIdx, 
                                  regDroppedLogEntry, vvdSidCS, vvdVid, 
                                  vvdRand, vvdChoice, vvdAccepted, vvdRejected, 
                                  vvdCfg >>

CS_SendVoteRes == /\ pc[CSPid] = "CS_SendVoteRes"
                  /\ LET sid == ActiveVoteSessionSid(csSessionStore) IN
                       LET session == StoreLookup(csSessionStore, ActiveVoteSessionSid(csSessionStore)) IN
                         LET ballot == StoreLookup(csBallotStore, StoreLookup(csSessionStore, ActiveVoteSessionSid(csSessionStore)).ctx.voteVid) IN
                           /\ Assert(sid # Empty, 
                                     "Failure of assertion at line 520, column 7.")
                           /\ Assert(session # Empty, 
                                     "Failure of assertion at line 521, column 7.")
                           /\ Assert(ballot # Empty, 
                                     "Failure of assertion at line 522, column 7.")
                           /\ chCSToVCD' = CSToVCD("VoteRes", sid, NoInt, VoteRes(session.ctx.voteVid, ballot.tsp, ballot.ocsp))
                           /\ chVCDToCS' = NoMsg
                  /\ pc' = [pc EXCEPT ![CSPid] = "CS_RecvVerifyReq"]
                  /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                  chCSToProvider, chProviderToCS, 
                                  chProviderToSign, chSignToProvider, 
                                  chSignToVoter, chVoterToSign, chCSToReg, 
                                  chRegToCS, chVCDToVVD, chVVDToCS, chCSToVVD, 
                                  chVVDToVoter, voterPhase, voterChoice, 
                                  authStarted, signStarted, verifyStarted, 
                                  accepted, voterAccept, verifiedBDOCs, vcdCtx, 
                                  vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                  vcdVoteRes, vcdRand, vcdCfg, csSessionStore, 
                                  csBallotStore, csLatest, csDroppedBallot, 
                                  csReqCnt, csFreshnessStore, csCfg, 
                                  providerSessionStore, providerCertStore, 
                                  provAuthSid, provSignSid, signAuthChallenge, 
                                  authPhone, signChallenge, signPhone, 
                                  regStore, regNextIdx, regOcspStore, 
                                  regNextOCSPIdx, regDroppedLogEntry, vvdSidCS, 
                                  vvdVid, vvdRand, vvdChoice, vvdAccepted, 
                                  vvdRejected, vvdCfg >>

CS_RecvVerifyReq == /\ pc[CSPid] = "CS_RecvVerifyReq"
                    /\ chVVDToCS.tag = "VerifyReq"
                    /\ now' = now + 1
                    /\ LET upd == VerifyAndUpdateSession(csCfg, csSessionStore, chVVDToCS.body.sidCS, "Verify", Empty, NoVoterRef, now') IN
                         LET ballot == StoreLookup(csBallotStore, chVVDToCS.body.vid) IN
                           IF /\ upd.ok
                              /\ ballot # Empty
                              /\ chVVDToCS.body.vid = csLatest.vid
                              /\ ballot.verCount < csCfg.verifyCountLimit
                              /\ now' <= ballot.submitted + csCfg.verifyWindow
                              /\ ballot.tsp # NoTSPRes
                              /\ ballot.ocsp # NoOCSPRes
                              THEN /\ csSessionStore' = upd.store
                                   /\ csBallotStore' = [csBallotStore EXCEPT ![chVVDToCS.body.vid].verCount = @ + 1]
                                   /\ chCSToVVD' = CSToVVD("VerifyRes", VerifyRes(ballot.bdoc, ballot.tsp, ballot.ocsp, csCfg.cfg.choices))
                              ELSE /\ TRUE
                                   /\ UNCHANGED << chCSToVVD, csSessionStore, 
                                                   csBallotStore >>
                    /\ chVVDToCS' = NoMsg
                    /\ pc' = [pc EXCEPT ![CSPid] = "CS_DropBallot"]
                    /\ UNCHANGED << chVoterToVCD, chVCDToVoter, chVCDToCS, 
                                    chCSToVCD, chCSToProvider, chProviderToCS, 
                                    chProviderToSign, chSignToProvider, 
                                    chSignToVoter, chVoterToSign, chCSToReg, 
                                    chRegToCS, chVCDToVVD, chVVDToVoter, 
                                    voterPhase, voterChoice, authStarted, 
                                    signStarted, verifyStarted, accepted, 
                                    voterAccept, verifiedBDOCs, vcdCtx, 
                                    vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                    vcdVoteRes, vcdRand, vcdCfg, csLatest, 
                                    csDroppedBallot, csReqCnt, 
                                    csFreshnessStore, csCfg, 
                                    providerSessionStore, providerCertStore, 
                                    provAuthSid, provSignSid, 
                                    signAuthChallenge, authPhone, 
                                    signChallenge, signPhone, regStore, 
                                    regNextIdx, regOcspStore, regNextOCSPIdx, 
                                    regDroppedLogEntry, vvdSidCS, vvdVid, 
                                    vvdRand, vvdChoice, vvdAccepted, 
                                    vvdRejected, vvdCfg >>

CS_DropBallot == /\ pc[CSPid] = "CS_DropBallot"
                 /\ \/ /\ TRUE
                       /\ UNCHANGED <<csBallotStore, csLatest, csDroppedBallot>>
                    \/ /\ IF /\ csLatest.vid # NoInt /\ csLatest.vid \in DOMAIN csBallotStore
                             THEN /\ LET ballot == StoreLookup(csBallotStore, csLatest.vid) IN
                                       LET updatedStore == StoreDelete(csBallotStore, csLatest.vid) IN
                                         /\ Assert(ballot # Empty, 
                                                   "Failure of assertion at line 556, column 13.")
                                         /\ csBallotStore' = updatedStore
                                         /\ csLatest' = LatestVoteForVoter(updatedStore, ballot.voterId)
                                  /\ csDroppedBallot' = TRUE
                             ELSE /\ TRUE
                                  /\ UNCHANGED << csBallotStore, csLatest, 
                                                  csDroppedBallot >>
                 /\ pc' = [pc EXCEPT ![CSPid] = "CS_Done"]
                 /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, chVCDToCS, 
                                 chCSToVCD, chCSToProvider, chProviderToCS, 
                                 chProviderToSign, chSignToProvider, 
                                 chSignToVoter, chVoterToSign, chCSToReg, 
                                 chRegToCS, chVCDToVVD, chVVDToCS, chCSToVVD, 
                                 chVVDToVoter, voterPhase, voterChoice, 
                                 authStarted, signStarted, verifyStarted, 
                                 accepted, voterAccept, verifiedBDOCs, vcdCtx, 
                                 vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                 vcdVoteRes, vcdRand, vcdCfg, csSessionStore, 
                                 csReqCnt, csFreshnessStore, csCfg, 
                                 providerSessionStore, providerCertStore, 
                                 provAuthSid, provSignSid, signAuthChallenge, 
                                 authPhone, signChallenge, signPhone, regStore, 
                                 regNextIdx, regOcspStore, regNextOCSPIdx, 
                                 regDroppedLogEntry, vvdSidCS, vvdVid, vvdRand, 
                                 vvdChoice, vvdAccepted, vvdRejected, vvdCfg >>

CS_Done == /\ pc[CSPid] = "CS_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![CSPid] = "Done"]
           /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, chVCDToCS, 
                           chCSToVCD, chCSToProvider, chProviderToCS, 
                           chProviderToSign, chSignToProvider, chSignToVoter, 
                           chVoterToSign, chCSToReg, chRegToCS, chVCDToVVD, 
                           chVVDToCS, chCSToVVD, chVVDToVoter, voterPhase, 
                           voterChoice, authStarted, signStarted, 
                           verifyStarted, accepted, voterAccept, verifiedBDOCs, 
                           vcdCtx, vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                           vcdVoteRes, vcdRand, vcdCfg, csSessionStore, 
                           csBallotStore, csLatest, csDroppedBallot, csReqCnt, 
                           csFreshnessStore, csCfg, providerSessionStore, 
                           providerCertStore, provAuthSid, provSignSid, 
                           signAuthChallenge, authPhone, signChallenge, 
                           signPhone, regStore, regNextIdx, regOcspStore, 
                           regNextOCSPIdx, regDroppedLogEntry, vvdSidCS, 
                           vvdVid, vvdRand, vvdChoice, vvdAccepted, 
                           vvdRejected, vvdCfg >>

CSProc == CS_RecvAuthReq \/ CS_RecvAuthStarted \/ CS_SendAuthStatusReq
             \/ CS_RecvAuthStatusRes \/ CS_RecvChoicesReq
             \/ CS_RecvGetCertReq \/ CS_RecvGetCertRes \/ CS_RecvSignReq
             \/ CS_RecvSignStarted \/ CS_SendSignStatusReq
             \/ CS_RecvSignStatusRes \/ CS_RecvVoteReq \/ CS_SendTSPReq
             \/ CS_RecvTSPRes \/ CS_SendOCSPReq \/ CS_RecvOCSPRes
             \/ CS_SendVoteRes \/ CS_RecvVerifyReq \/ CS_DropBallot
             \/ CS_Done

Provider_RecvAuthStart == /\ pc[ProviderPid] = "Provider_RecvAuthStart"
                          /\ chCSToProvider.tag = "AuthStart"
                          /\ LET p == chCSToProvider.body.payload IN
                               /\ Assert(ProviderSidsForPhone(providerSessionStore, p.voterRef.phone, "Auth") = {}, 
                                         "Failure of assertion at line 580, column 7.")
                               /\ providerSessionStore' = StorePut(providerSessionStore, provAuthSid, ProviderEntry(provAuthSid, p.voterRef.phone, "Auth", p.challenge, Empty))
                               /\ chProviderToSign' = ProviderToSign("AuthChallenge", [challenge |-> p.challenge, phone |-> p.voterRef.phone])
                               /\ chProviderToCS' = ProviderToCS("AuthStarted", chCSToProvider.body.sidCS, provAuthSid, [challenge |-> p.challenge])
                               /\ chCSToProvider' = NoMsg
                          /\ pc' = [pc EXCEPT ![ProviderPid] = "Provider_RecvAuthSignature"]
                          /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                          chVCDToCS, chCSToVCD, 
                                          chSignToProvider, chSignToVoter, 
                                          chVoterToSign, chCSToReg, chRegToCS, 
                                          chVCDToVVD, chVVDToCS, chCSToVVD, 
                                          chVVDToVoter, voterPhase, 
                                          voterChoice, authStarted, 
                                          signStarted, verifyStarted, accepted, 
                                          voterAccept, verifiedBDOCs, vcdCtx, 
                                          vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                          vcdVoteRes, vcdRand, vcdCfg, 
                                          csSessionStore, csBallotStore, 
                                          csLatest, csDroppedBallot, csReqCnt, 
                                          csFreshnessStore, csCfg, 
                                          providerCertStore, provAuthSid, 
                                          provSignSid, signAuthChallenge, 
                                          authPhone, signChallenge, signPhone, 
                                          regStore, regNextIdx, regOcspStore, 
                                          regNextOCSPIdx, regDroppedLogEntry, 
                                          vvdSidCS, vvdVid, vvdRand, vvdChoice, 
                                          vvdAccepted, vvdRejected, vvdCfg >>

Provider_RecvAuthSignature == /\ pc[ProviderPid] = "Provider_RecvAuthSignature"
                              /\ chSignToProvider.tag = "AuthSignature"
                              /\ LET sid == ProviderSidForPhone(providerSessionStore, chSignToProvider.body.payload.phone, "Auth") IN
                                   LET entry == StoreLookup(providerSessionStore, sid) IN
                                     /\ Assert(sid # NoInt, 
                                               "Failure of assertion at line 591, column 7.")
                                     /\ Assert(entry # Empty, 
                                               "Failure of assertion at line 592, column 7.")
                                     /\ Assert(chSignToProvider.body.payload.phone = entry.phone, 
                                               "Failure of assertion at line 593, column 7.")
                                     /\ providerSessionStore' = StorePut(providerSessionStore,
                                                                                   sid,
                                                                                   [entry EXCEPT !.sig = chSignToProvider.body.payload.sig])
                                     /\ chSignToProvider' = NoMsg
                              /\ pc' = [pc EXCEPT ![ProviderPid] = "Provider_RecvAuthStatusReq"]
                              /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                              chVCDToCS, chCSToVCD, 
                                              chCSToProvider, chProviderToCS, 
                                              chProviderToSign, chSignToVoter, 
                                              chVoterToSign, chCSToReg, 
                                              chRegToCS, chVCDToVVD, chVVDToCS, 
                                              chCSToVVD, chVVDToVoter, 
                                              voterPhase, voterChoice, 
                                              authStarted, signStarted, 
                                              verifyStarted, accepted, 
                                              voterAccept, verifiedBDOCs, 
                                              vcdCtx, vcdChoice, vcdVoteBDOC, 
                                              vcdVoteReq, vcdVoteRes, vcdRand, 
                                              vcdCfg, csSessionStore, 
                                              csBallotStore, csLatest, 
                                              csDroppedBallot, csReqCnt, 
                                              csFreshnessStore, csCfg, 
                                              providerCertStore, provAuthSid, 
                                              provSignSid, signAuthChallenge, 
                                              authPhone, signChallenge, 
                                              signPhone, regStore, regNextIdx, 
                                              regOcspStore, regNextOCSPIdx, 
                                              regDroppedLogEntry, vvdSidCS, 
                                              vvdVid, vvdRand, vvdChoice, 
                                              vvdAccepted, vvdRejected, vvdCfg >>

Provider_RecvAuthStatusReq == /\ pc[ProviderPid] = "Provider_RecvAuthStatusReq"
                              /\ chCSToProvider.tag = "AuthStatusReq"
                              /\ LET entry == StoreLookup(providerSessionStore, chCSToProvider.body.sidProv) IN
                                   /\ Assert(entry # Empty, 
                                             "Failure of assertion at line 603, column 7.")
                                   /\ Assert(chCSToProvider.body.sidProv = entry.sidProv, 
                                             "Failure of assertion at line 604, column 7.")
                                   /\ Assert(entry.sig # Empty, 
                                             "Failure of assertion at line 605, column 7.")
                                   /\ Assert(entry.phone \in DOMAIN providerCertStore, 
                                             "Failure of assertion at line 606, column 7.")
                                   /\ chProviderToCS' = ProviderToCS("AuthStatusRes", chCSToProvider.body.sidCS, entry.sidProv, [cert |-> providerCertStore[entry.phone], sig |-> entry.sig])
                                   /\ chCSToProvider' = NoMsg
                              /\ pc' = [pc EXCEPT ![ProviderPid] = "Provider_RecvGetCertReq"]
                              /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                              chVCDToCS, chCSToVCD, 
                                              chProviderToSign, 
                                              chSignToProvider, chSignToVoter, 
                                              chVoterToSign, chCSToReg, 
                                              chRegToCS, chVCDToVVD, chVVDToCS, 
                                              chCSToVVD, chVVDToVoter, 
                                              voterPhase, voterChoice, 
                                              authStarted, signStarted, 
                                              verifyStarted, accepted, 
                                              voterAccept, verifiedBDOCs, 
                                              vcdCtx, vcdChoice, vcdVoteBDOC, 
                                              vcdVoteReq, vcdVoteRes, vcdRand, 
                                              vcdCfg, csSessionStore, 
                                              csBallotStore, csLatest, 
                                              csDroppedBallot, csReqCnt, 
                                              csFreshnessStore, csCfg, 
                                              providerSessionStore, 
                                              providerCertStore, provAuthSid, 
                                              provSignSid, signAuthChallenge, 
                                              authPhone, signChallenge, 
                                              signPhone, regStore, regNextIdx, 
                                              regOcspStore, regNextOCSPIdx, 
                                              regDroppedLogEntry, vvdSidCS, 
                                              vvdVid, vvdRand, vvdChoice, 
                                              vvdAccepted, vvdRejected, vvdCfg >>

Provider_RecvGetCertReq == /\ pc[ProviderPid] = "Provider_RecvGetCertReq"
                           /\ chCSToProvider.tag = "GetCertReq"
                           /\ LET phone == chCSToProvider.body.payload.phone IN
                                /\ Assert(phone \in DOMAIN providerCertStore, 
                                          "Failure of assertion at line 614, column 7.")
                                /\ chProviderToCS' = ProviderToCS("GetCertRes", chCSToProvider.body.sidCS, NoInt, providerCertStore[phone])
                                /\ chCSToProvider' = NoMsg
                           /\ pc' = [pc EXCEPT ![ProviderPid] = "Provider_RecvSignStart"]
                           /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                           chVCDToCS, chCSToVCD, 
                                           chProviderToSign, chSignToProvider, 
                                           chSignToVoter, chVoterToSign, 
                                           chCSToReg, chRegToCS, chVCDToVVD, 
                                           chVVDToCS, chCSToVVD, chVVDToVoter, 
                                           voterPhase, voterChoice, 
                                           authStarted, signStarted, 
                                           verifyStarted, accepted, 
                                           voterAccept, verifiedBDOCs, vcdCtx, 
                                           vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                           vcdVoteRes, vcdRand, vcdCfg, 
                                           csSessionStore, csBallotStore, 
                                           csLatest, csDroppedBallot, csReqCnt, 
                                           csFreshnessStore, csCfg, 
                                           providerSessionStore, 
                                           providerCertStore, provAuthSid, 
                                           provSignSid, signAuthChallenge, 
                                           authPhone, signChallenge, signPhone, 
                                           regStore, regNextIdx, regOcspStore, 
                                           regNextOCSPIdx, regDroppedLogEntry, 
                                           vvdSidCS, vvdVid, vvdRand, 
                                           vvdChoice, vvdAccepted, vvdRejected, 
                                           vvdCfg >>

Provider_RecvSignStart == /\ pc[ProviderPid] = "Provider_RecvSignStart"
                          /\ chCSToProvider.tag = "SignStart"
                          /\ LET p == chCSToProvider.body.payload IN
                               /\ Assert(ProviderSidsForPhone(providerSessionStore, p.voterRef.phone, "Sign") = {}, 
                                         "Failure of assertion at line 622, column 7.")
                               /\ Assert(p.voterRef.phone \in DOMAIN providerCertStore, 
                                         "Failure of assertion at line 623, column 7.")
                               /\ providerSessionStore' = StorePut(providerSessionStore, provSignSid, ProviderEntry(provSignSid, p.voterRef.phone, "Sign", p.challenge, Empty))
                               /\ chProviderToSign' = ProviderToSign("SignChallenge", [challenge |-> p.challenge, cert |-> providerCertStore[p.voterRef.phone], phone |-> p.voterRef.phone])
                               /\ chProviderToCS' = ProviderToCS("SignStarted", chCSToProvider.body.sidCS, provSignSid, [challenge |-> p.challenge])
                               /\ chCSToProvider' = NoMsg
                          /\ pc' = [pc EXCEPT ![ProviderPid] = "Provider_RecvSignSignature"]
                          /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                          chVCDToCS, chCSToVCD, 
                                          chSignToProvider, chSignToVoter, 
                                          chVoterToSign, chCSToReg, chRegToCS, 
                                          chVCDToVVD, chVVDToCS, chCSToVVD, 
                                          chVVDToVoter, voterPhase, 
                                          voterChoice, authStarted, 
                                          signStarted, verifyStarted, accepted, 
                                          voterAccept, verifiedBDOCs, vcdCtx, 
                                          vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                          vcdVoteRes, vcdRand, vcdCfg, 
                                          csSessionStore, csBallotStore, 
                                          csLatest, csDroppedBallot, csReqCnt, 
                                          csFreshnessStore, csCfg, 
                                          providerCertStore, provAuthSid, 
                                          provSignSid, signAuthChallenge, 
                                          authPhone, signChallenge, signPhone, 
                                          regStore, regNextIdx, regOcspStore, 
                                          regNextOCSPIdx, regDroppedLogEntry, 
                                          vvdSidCS, vvdVid, vvdRand, vvdChoice, 
                                          vvdAccepted, vvdRejected, vvdCfg >>

Provider_RecvSignSignature == /\ pc[ProviderPid] = "Provider_RecvSignSignature"
                              /\ chSignToProvider.tag = "SignSignature"
                              /\ LET sid == ProviderSidForPhone(providerSessionStore, chSignToProvider.body.payload.phone, "Sign") IN
                                   LET entry == StoreLookup(providerSessionStore, sid) IN
                                     /\ Assert(sid # NoInt, 
                                               "Failure of assertion at line 634, column 7.")
                                     /\ Assert(entry # Empty, 
                                               "Failure of assertion at line 635, column 7.")
                                     /\ Assert(chSignToProvider.body.payload.phone = entry.phone, 
                                               "Failure of assertion at line 636, column 7.")
                                     /\ providerSessionStore' = StorePut(providerSessionStore,
                                                                                   sid,
                                                                                   [entry EXCEPT !.sig = chSignToProvider.body.payload.sig])
                                     /\ chSignToProvider' = NoMsg
                              /\ pc' = [pc EXCEPT ![ProviderPid] = "Provider_RecvSignStatusReq"]
                              /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                              chVCDToCS, chCSToVCD, 
                                              chCSToProvider, chProviderToCS, 
                                              chProviderToSign, chSignToVoter, 
                                              chVoterToSign, chCSToReg, 
                                              chRegToCS, chVCDToVVD, chVVDToCS, 
                                              chCSToVVD, chVVDToVoter, 
                                              voterPhase, voterChoice, 
                                              authStarted, signStarted, 
                                              verifyStarted, accepted, 
                                              voterAccept, verifiedBDOCs, 
                                              vcdCtx, vcdChoice, vcdVoteBDOC, 
                                              vcdVoteReq, vcdVoteRes, vcdRand, 
                                              vcdCfg, csSessionStore, 
                                              csBallotStore, csLatest, 
                                              csDroppedBallot, csReqCnt, 
                                              csFreshnessStore, csCfg, 
                                              providerCertStore, provAuthSid, 
                                              provSignSid, signAuthChallenge, 
                                              authPhone, signChallenge, 
                                              signPhone, regStore, regNextIdx, 
                                              regOcspStore, regNextOCSPIdx, 
                                              regDroppedLogEntry, vvdSidCS, 
                                              vvdVid, vvdRand, vvdChoice, 
                                              vvdAccepted, vvdRejected, vvdCfg >>

Provider_RecvSignStatusReq == /\ pc[ProviderPid] = "Provider_RecvSignStatusReq"
                              /\ chCSToProvider.tag = "SignStatusReq"
                              /\ LET entry == StoreLookup(providerSessionStore, chCSToProvider.body.sidProv) IN
                                   /\ Assert(entry # Empty, 
                                             "Failure of assertion at line 646, column 7.")
                                   /\ Assert(chCSToProvider.body.sidProv = entry.sidProv, 
                                             "Failure of assertion at line 647, column 7.")
                                   /\ Assert(entry.sig # Empty, 
                                             "Failure of assertion at line 648, column 7.")
                                   /\ chProviderToCS' = ProviderToCS("SignStatusRes", chCSToProvider.body.sidCS, entry.sidProv, entry.sig)
                                   /\ chCSToProvider' = NoMsg
                              /\ pc' = [pc EXCEPT ![ProviderPid] = "Provider_Done"]
                              /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                              chVCDToCS, chCSToVCD, 
                                              chProviderToSign, 
                                              chSignToProvider, chSignToVoter, 
                                              chVoterToSign, chCSToReg, 
                                              chRegToCS, chVCDToVVD, chVVDToCS, 
                                              chCSToVVD, chVVDToVoter, 
                                              voterPhase, voterChoice, 
                                              authStarted, signStarted, 
                                              verifyStarted, accepted, 
                                              voterAccept, verifiedBDOCs, 
                                              vcdCtx, vcdChoice, vcdVoteBDOC, 
                                              vcdVoteReq, vcdVoteRes, vcdRand, 
                                              vcdCfg, csSessionStore, 
                                              csBallotStore, csLatest, 
                                              csDroppedBallot, csReqCnt, 
                                              csFreshnessStore, csCfg, 
                                              providerSessionStore, 
                                              providerCertStore, provAuthSid, 
                                              provSignSid, signAuthChallenge, 
                                              authPhone, signChallenge, 
                                              signPhone, regStore, regNextIdx, 
                                              regOcspStore, regNextOCSPIdx, 
                                              regDroppedLogEntry, vvdSidCS, 
                                              vvdVid, vvdRand, vvdChoice, 
                                              vvdAccepted, vvdRejected, vvdCfg >>

Provider_Done == /\ pc[ProviderPid] = "Provider_Done"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT ![ProviderPid] = "Done"]
                 /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, chVCDToCS, 
                                 chCSToVCD, chCSToProvider, chProviderToCS, 
                                 chProviderToSign, chSignToProvider, 
                                 chSignToVoter, chVoterToSign, chCSToReg, 
                                 chRegToCS, chVCDToVVD, chVVDToCS, chCSToVVD, 
                                 chVVDToVoter, voterPhase, voterChoice, 
                                 authStarted, signStarted, verifyStarted, 
                                 accepted, voterAccept, verifiedBDOCs, vcdCtx, 
                                 vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                 vcdVoteRes, vcdRand, vcdCfg, csSessionStore, 
                                 csBallotStore, csLatest, csDroppedBallot, 
                                 csReqCnt, csFreshnessStore, csCfg, 
                                 providerSessionStore, providerCertStore, 
                                 provAuthSid, provSignSid, signAuthChallenge, 
                                 authPhone, signChallenge, signPhone, regStore, 
                                 regNextIdx, regOcspStore, regNextOCSPIdx, 
                                 regDroppedLogEntry, vvdSidCS, vvdVid, vvdRand, 
                                 vvdChoice, vvdAccepted, vvdRejected, vvdCfg >>

ProviderProc == Provider_RecvAuthStart \/ Provider_RecvAuthSignature
                   \/ Provider_RecvAuthStatusReq \/ Provider_RecvGetCertReq
                   \/ Provider_RecvSignStart \/ Provider_RecvSignSignature
                   \/ Provider_RecvSignStatusReq \/ Provider_Done

Sign_RecvAuthChallenge == /\ pc[SignPid] = "Sign_RecvAuthChallenge"
                          /\ chProviderToSign.tag = "AuthChallenge"
                          /\ signAuthChallenge' = chProviderToSign.body.payload.challenge
                          /\ authPhone' = chProviderToSign.body.payload.phone
                          /\ chSignToVoter' = SignToVoter("AuthChallengeDisplay", chProviderToSign.body.payload)
                          /\ chProviderToSign' = NoMsg
                          /\ pc' = [pc EXCEPT ![SignPid] = "Sign_RecvAuthApproval"]
                          /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                          chVCDToCS, chCSToVCD, chCSToProvider, 
                                          chProviderToCS, chSignToProvider, 
                                          chVoterToSign, chCSToReg, chRegToCS, 
                                          chVCDToVVD, chVVDToCS, chCSToVVD, 
                                          chVVDToVoter, voterPhase, 
                                          voterChoice, authStarted, 
                                          signStarted, verifyStarted, accepted, 
                                          voterAccept, verifiedBDOCs, vcdCtx, 
                                          vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                          vcdVoteRes, vcdRand, vcdCfg, 
                                          csSessionStore, csBallotStore, 
                                          csLatest, csDroppedBallot, csReqCnt, 
                                          csFreshnessStore, csCfg, 
                                          providerSessionStore, 
                                          providerCertStore, provAuthSid, 
                                          provSignSid, signChallenge, 
                                          signPhone, regStore, regNextIdx, 
                                          regOcspStore, regNextOCSPIdx, 
                                          regDroppedLogEntry, vvdSidCS, vvdVid, 
                                          vvdRand, vvdChoice, vvdAccepted, 
                                          vvdRejected, vvdCfg >>

Sign_RecvAuthApproval == /\ pc[SignPid] = "Sign_RecvAuthApproval"
                         /\ chVoterToSign.tag = "ApproveAuth"
                         /\ chSignToProvider' = SignToProvider("AuthSignature", [phone |-> authPhone, sig |-> Sign(SimSK, signAuthChallenge)])
                         /\ chVoterToSign' = NoMsg
                         /\ signAuthChallenge' = Empty
                         /\ authPhone' = NoStr
                         /\ pc' = [pc EXCEPT ![SignPid] = "Sign_RecvSignChallenge"]
                         /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                         chVCDToCS, chCSToVCD, chCSToProvider, 
                                         chProviderToCS, chProviderToSign, 
                                         chSignToVoter, chCSToReg, chRegToCS, 
                                         chVCDToVVD, chVVDToCS, chCSToVVD, 
                                         chVVDToVoter, voterPhase, voterChoice, 
                                         authStarted, signStarted, 
                                         verifyStarted, accepted, voterAccept, 
                                         verifiedBDOCs, vcdCtx, vcdChoice, 
                                         vcdVoteBDOC, vcdVoteReq, vcdVoteRes, 
                                         vcdRand, vcdCfg, csSessionStore, 
                                         csBallotStore, csLatest, 
                                         csDroppedBallot, csReqCnt, 
                                         csFreshnessStore, csCfg, 
                                         providerSessionStore, 
                                         providerCertStore, provAuthSid, 
                                         provSignSid, signChallenge, signPhone, 
                                         regStore, regNextIdx, regOcspStore, 
                                         regNextOCSPIdx, regDroppedLogEntry, 
                                         vvdSidCS, vvdVid, vvdRand, vvdChoice, 
                                         vvdAccepted, vvdRejected, vvdCfg >>

Sign_RecvSignChallenge == /\ pc[SignPid] = "Sign_RecvSignChallenge"
                          /\ chProviderToSign.tag = "SignChallenge"
                          /\ signChallenge' = chProviderToSign.body.payload.challenge
                          /\ signPhone' = chProviderToSign.body.payload.phone
                          /\ chSignToVoter' = SignToVoter("SignChallengeDisplay", chProviderToSign.body.payload)
                          /\ chProviderToSign' = NoMsg
                          /\ pc' = [pc EXCEPT ![SignPid] = "Sign_RecvSignApproval"]
                          /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                          chVCDToCS, chCSToVCD, chCSToProvider, 
                                          chProviderToCS, chSignToProvider, 
                                          chVoterToSign, chCSToReg, chRegToCS, 
                                          chVCDToVVD, chVVDToCS, chCSToVVD, 
                                          chVVDToVoter, voterPhase, 
                                          voterChoice, authStarted, 
                                          signStarted, verifyStarted, accepted, 
                                          voterAccept, verifiedBDOCs, vcdCtx, 
                                          vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                          vcdVoteRes, vcdRand, vcdCfg, 
                                          csSessionStore, csBallotStore, 
                                          csLatest, csDroppedBallot, csReqCnt, 
                                          csFreshnessStore, csCfg, 
                                          providerSessionStore, 
                                          providerCertStore, provAuthSid, 
                                          provSignSid, signAuthChallenge, 
                                          authPhone, regStore, regNextIdx, 
                                          regOcspStore, regNextOCSPIdx, 
                                          regDroppedLogEntry, vvdSidCS, vvdVid, 
                                          vvdRand, vvdChoice, vvdAccepted, 
                                          vvdRejected, vvdCfg >>

Sign_RecvSignApproval == /\ pc[SignPid] = "Sign_RecvSignApproval"
                         /\ chVoterToSign.tag = "ApproveSign"
                         /\ chSignToProvider' = SignToProvider("SignSignature", [phone |-> signPhone, sig |-> Sign(SimSK, signChallenge)])
                         /\ chVoterToSign' = NoMsg
                         /\ signChallenge' = Empty
                         /\ signPhone' = NoStr
                         /\ pc' = [pc EXCEPT ![SignPid] = "Sign_Done"]
                         /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                         chVCDToCS, chCSToVCD, chCSToProvider, 
                                         chProviderToCS, chProviderToSign, 
                                         chSignToVoter, chCSToReg, chRegToCS, 
                                         chVCDToVVD, chVVDToCS, chCSToVVD, 
                                         chVVDToVoter, voterPhase, voterChoice, 
                                         authStarted, signStarted, 
                                         verifyStarted, accepted, voterAccept, 
                                         verifiedBDOCs, vcdCtx, vcdChoice, 
                                         vcdVoteBDOC, vcdVoteReq, vcdVoteRes, 
                                         vcdRand, vcdCfg, csSessionStore, 
                                         csBallotStore, csLatest, 
                                         csDroppedBallot, csReqCnt, 
                                         csFreshnessStore, csCfg, 
                                         providerSessionStore, 
                                         providerCertStore, provAuthSid, 
                                         provSignSid, signAuthChallenge, 
                                         authPhone, regStore, regNextIdx, 
                                         regOcspStore, regNextOCSPIdx, 
                                         regDroppedLogEntry, vvdSidCS, vvdVid, 
                                         vvdRand, vvdChoice, vvdAccepted, 
                                         vvdRejected, vvdCfg >>

Sign_Done == /\ pc[SignPid] = "Sign_Done"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![SignPid] = "Done"]
             /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, chVCDToCS, 
                             chCSToVCD, chCSToProvider, chProviderToCS, 
                             chProviderToSign, chSignToProvider, chSignToVoter, 
                             chVoterToSign, chCSToReg, chRegToCS, chVCDToVVD, 
                             chVVDToCS, chCSToVVD, chVVDToVoter, voterPhase, 
                             voterChoice, authStarted, signStarted, 
                             verifyStarted, accepted, voterAccept, 
                             verifiedBDOCs, vcdCtx, vcdChoice, vcdVoteBDOC, 
                             vcdVoteReq, vcdVoteRes, vcdRand, vcdCfg, 
                             csSessionStore, csBallotStore, csLatest, 
                             csDroppedBallot, csReqCnt, csFreshnessStore, 
                             csCfg, providerSessionStore, providerCertStore, 
                             provAuthSid, provSignSid, signAuthChallenge, 
                             authPhone, signChallenge, signPhone, regStore, 
                             regNextIdx, regOcspStore, regNextOCSPIdx, 
                             regDroppedLogEntry, vvdSidCS, vvdVid, vvdRand, 
                             vvdChoice, vvdAccepted, vvdRejected, vvdCfg >>

SignProc == Sign_RecvAuthChallenge \/ Sign_RecvAuthApproval
               \/ Sign_RecvSignChallenge \/ Sign_RecvSignApproval
               \/ Sign_Done

Reg_RecvTSPReq == /\ pc[RegPid] = "Reg_RecvTSPReq"
                  /\ chCSToReg.tag = "TSPReq"
                  /\ LET p == chCSToReg.body.payload IN
                       /\ LET tsp == TSPRes(p.m, p.n, now, TSPRegCert, Sign(TSPRegSK, <<p.m, p.n, now>>)) IN
                            /\ regStore' = StorePut(regStore, regNextIdx, RegLogEntry(p, tsp))
                            /\ regNextIdx' = regNextIdx + 1
                            /\ chRegToCS' = RegToCS("TSPRes", tsp)
                       /\ chCSToReg' = NoMsg
                  /\ pc' = [pc EXCEPT ![RegPid] = "Reg_RecvOCSPReq"]
                  /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, chVCDToCS, 
                                  chCSToVCD, chCSToProvider, chProviderToCS, 
                                  chProviderToSign, chSignToProvider, 
                                  chSignToVoter, chVoterToSign, chVCDToVVD, 
                                  chVVDToCS, chCSToVVD, chVVDToVoter, 
                                  voterPhase, voterChoice, authStarted, 
                                  signStarted, verifyStarted, accepted, 
                                  voterAccept, verifiedBDOCs, vcdCtx, 
                                  vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                  vcdVoteRes, vcdRand, vcdCfg, csSessionStore, 
                                  csBallotStore, csLatest, csDroppedBallot, 
                                  csReqCnt, csFreshnessStore, csCfg, 
                                  providerSessionStore, providerCertStore, 
                                  provAuthSid, provSignSid, signAuthChallenge, 
                                  authPhone, signChallenge, signPhone, 
                                  regOcspStore, regNextOCSPIdx, 
                                  regDroppedLogEntry, vvdSidCS, vvdVid, 
                                  vvdRand, vvdChoice, vvdAccepted, vvdRejected, 
                                  vvdCfg >>

Reg_RecvOCSPReq == /\ pc[RegPid] = "Reg_RecvOCSPReq"
                   /\ chCSToReg.tag = "OCSPReq"
                   /\ LET p == chCSToReg.body.payload IN
                        /\ LET ocsp == OCSPRes(p, TRUE, now, OCSPCert, Sign(OCSPSK, <<p, TRUE, now>>)) IN
                             /\ regOcspStore' = StorePut(regOcspStore, regNextOCSPIdx, ocsp)
                             /\ regNextOCSPIdx' = regNextOCSPIdx + 1
                             /\ chRegToCS' = RegToCS("OCSPRes", ocsp)
                        /\ chCSToReg' = NoMsg
                   /\ pc' = [pc EXCEPT ![RegPid] = "Reg_DropLogEntry"]
                   /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, chVCDToCS, 
                                   chCSToVCD, chCSToProvider, chProviderToCS, 
                                   chProviderToSign, chSignToProvider, 
                                   chSignToVoter, chVoterToSign, chVCDToVVD, 
                                   chVVDToCS, chCSToVVD, chVVDToVoter, 
                                   voterPhase, voterChoice, authStarted, 
                                   signStarted, verifyStarted, accepted, 
                                   voterAccept, verifiedBDOCs, vcdCtx, 
                                   vcdChoice, vcdVoteBDOC, vcdVoteReq, 
                                   vcdVoteRes, vcdRand, vcdCfg, csSessionStore, 
                                   csBallotStore, csLatest, csDroppedBallot, 
                                   csReqCnt, csFreshnessStore, csCfg, 
                                   providerSessionStore, providerCertStore, 
                                   provAuthSid, provSignSid, signAuthChallenge, 
                                   authPhone, signChallenge, signPhone, 
                                   regStore, regNextIdx, regDroppedLogEntry, 
                                   vvdSidCS, vvdVid, vvdRand, vvdChoice, 
                                   vvdAccepted, vvdRejected, vvdCfg >>

Reg_DropLogEntry == /\ pc[RegPid] = "Reg_DropLogEntry"
                    /\ \/ /\ TRUE
                          /\ UNCHANGED <<regStore, regDroppedLogEntry>>
                       \/ /\ IF DOMAIN regStore # {}
                                THEN /\ LET idx == CHOOSE i \in DOMAIN regStore : TRUE IN
                                          /\ regStore' = StoreDelete(regStore, idx)
                                          /\ regDroppedLogEntry' = TRUE
                                ELSE /\ TRUE
                                     /\ UNCHANGED << regStore, 
                                                     regDroppedLogEntry >>
                    /\ pc' = [pc EXCEPT ![RegPid] = "Reg_Done"]
                    /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, chVCDToCS, 
                                    chCSToVCD, chCSToProvider, chProviderToCS, 
                                    chProviderToSign, chSignToProvider, 
                                    chSignToVoter, chVoterToSign, chCSToReg, 
                                    chRegToCS, chVCDToVVD, chVVDToCS, 
                                    chCSToVVD, chVVDToVoter, voterPhase, 
                                    voterChoice, authStarted, signStarted, 
                                    verifyStarted, accepted, voterAccept, 
                                    verifiedBDOCs, vcdCtx, vcdChoice, 
                                    vcdVoteBDOC, vcdVoteReq, vcdVoteRes, 
                                    vcdRand, vcdCfg, csSessionStore, 
                                    csBallotStore, csLatest, csDroppedBallot, 
                                    csReqCnt, csFreshnessStore, csCfg, 
                                    providerSessionStore, providerCertStore, 
                                    provAuthSid, provSignSid, 
                                    signAuthChallenge, authPhone, 
                                    signChallenge, signPhone, regNextIdx, 
                                    regOcspStore, regNextOCSPIdx, vvdSidCS, 
                                    vvdVid, vvdRand, vvdChoice, vvdAccepted, 
                                    vvdRejected, vvdCfg >>

Reg_Done == /\ pc[RegPid] = "Reg_Done"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![RegPid] = "Done"]
            /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, chVCDToCS, 
                            chCSToVCD, chCSToProvider, chProviderToCS, 
                            chProviderToSign, chSignToProvider, chSignToVoter, 
                            chVoterToSign, chCSToReg, chRegToCS, chVCDToVVD, 
                            chVVDToCS, chCSToVVD, chVVDToVoter, voterPhase, 
                            voterChoice, authStarted, signStarted, 
                            verifyStarted, accepted, voterAccept, 
                            verifiedBDOCs, vcdCtx, vcdChoice, vcdVoteBDOC, 
                            vcdVoteReq, vcdVoteRes, vcdRand, vcdCfg, 
                            csSessionStore, csBallotStore, csLatest, 
                            csDroppedBallot, csReqCnt, csFreshnessStore, csCfg, 
                            providerSessionStore, providerCertStore, 
                            provAuthSid, provSignSid, signAuthChallenge, 
                            authPhone, signChallenge, signPhone, regStore, 
                            regNextIdx, regOcspStore, regNextOCSPIdx, 
                            regDroppedLogEntry, vvdSidCS, vvdVid, vvdRand, 
                            vvdChoice, vvdAccepted, vvdRejected, vvdCfg >>

RegProc == Reg_RecvTSPReq \/ Reg_RecvOCSPReq \/ Reg_DropLogEntry
              \/ Reg_Done

VVD_RecvQR == /\ pc[VVDPid] = "VVD_RecvQR"
              /\ chVCDToVVD.tag = "VerifyQR"
              /\ vvdRand' = chVCDToVVD.body.r
              /\ vvdVid' = chVCDToVVD.body.vid
              /\ vvdSidCS' = chVCDToVVD.body.sidCS
              /\ chVVDToCS' = VVDToCS("VerifyReq", vvdSidCS', vvdVid')
              /\ chVCDToVVD' = NoMsg
              /\ pc' = [pc EXCEPT ![VVDPid] = "VVD_RecvVerifyRes"]
              /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, chVCDToCS, 
                              chCSToVCD, chCSToProvider, chProviderToCS, 
                              chProviderToSign, chSignToProvider, 
                              chSignToVoter, chVoterToSign, chCSToReg, 
                              chRegToCS, chCSToVVD, chVVDToVoter, voterPhase, 
                              voterChoice, authStarted, signStarted, 
                              verifyStarted, accepted, voterAccept, 
                              verifiedBDOCs, vcdCtx, vcdChoice, vcdVoteBDOC, 
                              vcdVoteReq, vcdVoteRes, vcdRand, vcdCfg, 
                              csSessionStore, csBallotStore, csLatest, 
                              csDroppedBallot, csReqCnt, csFreshnessStore, 
                              csCfg, providerSessionStore, providerCertStore, 
                              provAuthSid, provSignSid, signAuthChallenge, 
                              authPhone, signChallenge, signPhone, regStore, 
                              regNextIdx, regOcspStore, regNextOCSPIdx, 
                              regDroppedLogEntry, vvdChoice, vvdAccepted, 
                              vvdRejected, vvdCfg >>

VVD_RecvVerifyRes == /\ pc[VVDPid] = "VVD_RecvVerifyRes"
                     /\ chCSToVVD.tag = "VerifyRes"
                     /\ LET p == chCSToVVD.body.payload IN
                          /\ IF /\ ValidateBallot(vvdCfg, p.bdoc, p.tsp, p.ocsp, p.choices) /\ RecoverChoiceByRand(vvdCfg, vvdRand, p.bdoc.ct, p.choices) # NoStr
                                THEN /\ vvdChoice' = RecoverChoiceByRand(vvdCfg, vvdRand, p.bdoc.ct, p.choices)
                                     /\ vvdAccepted' = TRUE
                                     /\ chVVDToVoter' = VVDToVoter("VerifyDisplay", [choice |-> vvdChoice', bdoc |-> p.bdoc])
                                     /\ UNCHANGED vvdRejected
                                ELSE /\ vvdRejected' = TRUE
                                     /\ chVVDToVoter' = VVDToVoter("VerifyFailed", NoBody)
                                     /\ UNCHANGED << vvdChoice, vvdAccepted >>
                          /\ chCSToVVD' = NoMsg
                     /\ pc' = [pc EXCEPT ![VVDPid] = "VVD_Done"]
                     /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, 
                                     chVCDToCS, chCSToVCD, chCSToProvider, 
                                     chProviderToCS, chProviderToSign, 
                                     chSignToProvider, chSignToVoter, 
                                     chVoterToSign, chCSToReg, chRegToCS, 
                                     chVCDToVVD, chVVDToCS, voterPhase, 
                                     voterChoice, authStarted, signStarted, 
                                     verifyStarted, accepted, voterAccept, 
                                     verifiedBDOCs, vcdCtx, vcdChoice, 
                                     vcdVoteBDOC, vcdVoteReq, vcdVoteRes, 
                                     vcdRand, vcdCfg, csSessionStore, 
                                     csBallotStore, csLatest, csDroppedBallot, 
                                     csReqCnt, csFreshnessStore, csCfg, 
                                     providerSessionStore, providerCertStore, 
                                     provAuthSid, provSignSid, 
                                     signAuthChallenge, authPhone, 
                                     signChallenge, signPhone, regStore, 
                                     regNextIdx, regOcspStore, regNextOCSPIdx, 
                                     regDroppedLogEntry, vvdSidCS, vvdVid, 
                                     vvdRand, vvdCfg >>

VVD_Done == /\ pc[VVDPid] = "VVD_Done"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![VVDPid] = "Done"]
            /\ UNCHANGED << now, chVoterToVCD, chVCDToVoter, chVCDToCS, 
                            chCSToVCD, chCSToProvider, chProviderToCS, 
                            chProviderToSign, chSignToProvider, chSignToVoter, 
                            chVoterToSign, chCSToReg, chRegToCS, chVCDToVVD, 
                            chVVDToCS, chCSToVVD, chVVDToVoter, voterPhase, 
                            voterChoice, authStarted, signStarted, 
                            verifyStarted, accepted, voterAccept, 
                            verifiedBDOCs, vcdCtx, vcdChoice, vcdVoteBDOC, 
                            vcdVoteReq, vcdVoteRes, vcdRand, vcdCfg, 
                            csSessionStore, csBallotStore, csLatest, 
                            csDroppedBallot, csReqCnt, csFreshnessStore, csCfg, 
                            providerSessionStore, providerCertStore, 
                            provAuthSid, provSignSid, signAuthChallenge, 
                            authPhone, signChallenge, signPhone, regStore, 
                            regNextIdx, regOcspStore, regNextOCSPIdx, 
                            regDroppedLogEntry, vvdSidCS, vvdVid, vvdRand, 
                            vvdChoice, vvdAccepted, vvdRejected, vvdCfg >>

VVDProc == VVD_RecvQR \/ VVD_RecvVerifyRes \/ VVD_Done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == VoterProc \/ VCDProc \/ CSProc \/ ProviderProc \/ SignProc
           \/ RegProc \/ VVDProc
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(VoterProc)
        /\ WF_vars(VCDProc)
        /\ WF_vars(CSProc)
        /\ WF_vars(ProviderProc)
        /\ WF_vars(SignProc)
        /\ WF_vars(RegProc)
        /\ WF_vars(VVDProc)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* vvd accepts the latest ballot while CS still retains the latest-vote record
Inv_VVDAcceptsLatestVote == (vvdAccepted /\ ~csDroppedBallot) => vvdVid = csLatest.vid

\* if CS and Reg did not both delete local evidence, an individually verified ballot
\* still has a local record in either CS or Reg
Inv_VoterVerifiedImpliesLocalRecord == 
	~(csDroppedBallot /\ regDroppedLogEntry) 
	=> \A bdoc \in verifiedBDOCs : CSHasBallot(bdoc, csBallotStore) \/ RegHasTSPFor(bdoc, regStore)

=============================================================================
