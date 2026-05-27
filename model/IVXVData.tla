------------------------------ MODULE IVXVData ------------------------------
EXTENDS  Integers
NoInt == -1
NoStr == ""
Empty == <<>>
EmptyStore == [i \in {} |-> Empty]

OCSPReq(signerCert) == [ signerCert |-> signerCert ]
NoOCSPReq == OCSPReq(Empty)
OCSPRes(req, status, t, cert, sig) == [ req |-> req,  status |-> status, t |-> t, cert |-> cert, sig |-> sig ]
NoOCSPRes == OCSPRes(NoOCSPReq, FALSE, NoInt, Empty, Empty)

TSPReq(m, n) == [ m |-> m, n |-> n ]
NoTSPReq == TSPReq(Empty, Empty)
TSPRes(m, n, t, cert, sig) == [ m |-> m, n |-> n, t |-> t, cert |-> cert, sig |-> sig ]
NoTSPRes == TSPRes(Empty, Empty, NoInt, Empty, Empty)

VoterRef(voterId, phone) == [voterId |-> voterId, phone |-> phone]
NoVoterRef == VoterRef(NoStr, NoStr)

BDOC(ct, signerCert, sig, tbs) == [ ct |-> ct, signerCert |-> signerCert, sig |-> sig, tbs |-> tbs ]
EmptyBDOC == BDOC(Empty, Empty, Empty, Empty)

SessionCtx(authChallenge, authTokNonce, issuedVid, signDigest, voteVid, submitted, bdoc, tspReq, ocspReq, tspRes, ocspRes, clientId) ==
  [ authChallenge |-> authChallenge,
    authTokNonce  |-> authTokNonce,
    issuedVid     |-> issuedVid,
    signDigest    |-> signDigest,
    voteVid       |-> voteVid,
    submitted     |-> submitted,
    bdoc          |-> bdoc,
    tspReq        |-> tspReq,
    ocspReq       |-> ocspReq,
    tspRes        |-> tspRes,
    ocspRes       |-> ocspRes,
    clientId      |-> clientId ]
EmptySessionCtx == SessionCtx(Empty, Empty, NoInt, Empty, NoInt, NoInt, EmptyBDOC, NoTSPReq, NoOCSPReq, NoTSPRes, NoOCSPRes, NoInt)

SessionData(sid, phase, voterId, phone, tok, exp, ctx) ==
  [ sid     |-> sid,
    phase   |-> phase,
    voterId |-> voterId,
    phone   |-> phone,
    tok     |-> tok,
    exp     |-> exp,
    ctx     |-> ctx ]
NoSession == SessionData(NoInt, NoStr, NoStr, NoStr, Empty, NoInt, EmptySessionCtx)
EmptySession(voterId, phone) == SessionData(NoInt, NoStr, voterId, phone, Empty, NoInt, EmptySessionCtx)

\* SessionStore: id -> SessionData
EmptySessionStore == [sid \in {} |-> NoSession]

RegisteredBallot(vid, voterId, submitted, registered, bdoc, tsp, ocsp, verCount, isTestVote) ==
  [ vid       |-> vid,
    voterId   |-> voterId,
    submitted |-> submitted,
    registered |-> registered,
    bdoc      |-> bdoc,
    tsp       |-> tsp,
    ocsp      |-> ocsp,
    verCount  |-> verCount,
    isTestVote |-> isTestVote ]
EmptyRegisteredBallot == RegisteredBallot(NoInt, NoStr, NoInt, NoInt, EmptyBDOC, NoTSPRes, NoOCSPRes, 0, FALSE)
EmptyCSBallotStore == [vid \in {} |-> EmptyRegisteredBallot]

EGParams == "EG"
RSAParams == "RSA"

SmartCardData(holderId, decShare, sigShare) == [ holderId |-> holderId, decShare |-> decShare, sigShare |-> sigShare ]
EmptySmartCardData(holderId) == SmartCardData(holderId, Empty, Empty)
EmptySmartCardStore(ids) == [i \in ids |-> SmartCardData(i, Empty, Empty)]

CryptoParams(dec, sig) == [ dec |-> dec, sig |-> sig ]

PublicElectionConfig(electionId, question, choices, decCert, sigCert, rootCACert, tspClientPK, tspRegCert, ocspCert, cryptoParams) ==
  [ electionId  	|-> electionId,
    question 			|-> question,
    choices 			|-> choices,
    decCert				|-> decCert,
    sigCert    		|-> sigCert,
    rootCACert    |-> rootCACert,
    tspClientPK 	|-> tspClientPK,
    tspRegCert  	|-> tspRegCert,
    ocspCert    	|-> ocspCert, 
		cryptoParams	|-> cryptoParams ]

CSConfig(electionConfig, stageTTL, verifyWindow, verifyCountLimit, tSPPastSlack, tSPFutureSlack, voterList) ==
  [ cfg								|-> electionConfig,
	  stageTTL					|-> stageTTL,
		verifyWindow			|-> verifyWindow,
		verifyCountLimit	|-> verifyCountLimit,
		tSPPastSlack			|-> tSPPastSlack,
		tSPFutureSlack		|-> tSPFutureSlack,
		voterList					|-> voterList ]

EmptyPublicElectionConfig == PublicElectionConfig(NoStr, NoStr, {}, Empty, Empty, Empty, Empty, Empty, Empty, Empty)
\* CheckBallotResult
INVALID_BALLOT_SIGNATURE == "INVALID_BALLOT_SIGNATURE" \* checked
MISSING_VOTER_SIGNATURE == "MISSING_VOTER_SIGNATURE" \* checked
VOTER_NOT_FOUND == "VOTER_NOT_FOUND" \* checked
TIME_BEFORE_START == "TIME_BEFORE_START" \* checked
REG_REQ_NOT_UNIQUE == "REG_REQ_NOT_UNIQUE" \* checked
REG_RESP_NOT_UNIQUE == "REG_RESP_NOT_UNIQUE" \* checked
REG_RESP_INVALID == "REG_RESP_INVALID" \* checked
REG_NONCE_SIG_INVALID == "REG_NONCE_SIG_INVALID" \* checked
REG_REQ_WITHOUT_BALLOT == "REG_REQ_WITHOUT_BALLOT" \* checked
BALLOT_WITHOUT_REG_REQ == "BALLOT_WITHOUT_REG_REQ" \* checked
REG_RESP_REQ_UNMATCH == "REG_RESP_REQ_UNMATCH" \* checked
UNKNOWN_FILE_IN_VOTE_CONTAINER == "UNKNOWN_FILE_IN_VOTE_CONTAINER" \* omitted
INVALID_BDOC == "INVALID_BDOC" \* extra case to represent any BDOC-level loading failure
OK == "OK"

Voter(voterId, d, p) == [ voterId |-> voterId, d |-> d, p |-> p ]
NoVoter == Voter(NoStr, NoStr, NoStr)

Ballot(id, t, voter, votes) == [ id |-> id, t |-> t, voter |-> voter, votes |-> votes ]
EmptyBallot == Ballot(NoInt, NoInt, NoVoter, {})

VoterBallot(voterId, ballots, isRevoked) == [ voterId |-> voterId, ballots |-> ballots, isRevoked |-> isRevoked ]
EmptyVoterBallot == VoterBallot(NoStr, {}, FALSE)

BallotResponse(ballot, req, resp) == [ ballot |-> ballot, req |-> req, resp |-> resp ]
EmptyBallotResponse == BallotResponse(EmptyBallot, NoTSPReq, NoTSPRes)

PALogEntry(t, h, voterId) == [ t |-> t, h |-> h, voterId |-> voterId ]

PAErrorLogEntry(voterId, ballotId, err) == [ voterId |-> voterId, ballotId |-> ballotId, err |-> err ]

RawBallotEntry(ballotId, voterId, c) == [ ballotId |-> ballotId, voterId |-> voterId, c |-> c ]

DecryptedVote(d, p, q, ct, dp) == [ d |-> d, p |-> p, q |-> q, ct |-> ct, dp |-> dp ]

TallyRow(d, p, q, choice, count) ==
  [ d      |-> d,
    p      |-> p,
    q      |-> q,
    choice |-> choice,
    count  |-> count ]

ElectionResult(tally, plain, proofs, invalid, sigTally, sigPlain) ==
  [ tally    |-> tally,
    plain    |-> plain,
    proofs   |-> proofs,
    invalid  |-> invalid,
    sigTally |-> sigTally,
    sigPlain |-> sigPlain ]

EmptyElectionResult == ElectionResult({}, {}, {}, {}, Empty, Empty)

\* TODO
ShuffleProof(pk, in, out) == [ pk |-> pk, in |-> in, out |-> out ]
EmptyShuffleProof == ShuffleProof(Empty, {}, {})

\* Extra, not in spec but useful for model
VoterVerifyRecord(accepted, choice) == [ accepted |-> accepted, choice |-> choice ]
EmptyVoterVerifyRecord == VoterVerifyRecord(FALSE, NoStr)

EmptyVCDCtx ==
  [ sidCS   |-> Empty,
    sidAuth |-> NoInt,
    sidSign |-> NoInt,
    tok     |-> Empty,
    r       |-> Empty,
    choices |-> {},
    bdoc    |-> EmptyBDOC ]

ProviderEntry(sidProv, phone, kind, challenge, sig) ==
  [ sidProv    |-> sidProv,
    phone      |-> phone,
    kind       |-> kind,
    challenge  |-> challenge,
    sig        |-> sig ]

EmptyProviderEntry == ProviderEntry(NoInt, NoStr, NoStr, Empty, Empty)
EmptyProviderSessionStore == [sid \in {} |-> EmptyProviderEntry]

RegLogEntry(req, resp) == [ req |-> req, resp |-> resp ]
NoRegLogEntry == RegLogEntry(NoTSPReq, NoTSPRes)
EmptyRegStore == [idx \in {} |-> NoRegLogEntry]
EmptyOCSPStore == [idx \in {} |-> NoOCSPRes]

AnonVote(d, p, q, ct) == [ d |-> d, p |-> p, q |-> q, ct |-> ct ]

PlainVote(d, p, q, choice) == [ d |-> d, p |-> p, q |-> q, choice |-> choice ]

=============================================================================
