---- MODULE IVXVHelper ----
EXTENDS IVXVData

StoreLookup(store, key) == IF key \in DOMAIN store THEN store[key] ELSE Empty

StorePut(store, key, value) ==
  [ x \in DOMAIN store \cup { key } |-> IF x = key THEN value ELSE store[x] ]

StoreDelete(store, key) == [x \in DOMAIN store \ { key } |-> store[x]]
StoreValues(store) == {StoreLookup(store, k): k \in DOMAIN store}
DigestOf(ct, cert) == Hash(<< ct, cert >>)
SignedBDOC(c, cert, sig) == BDOC(c, cert, sig, DigestOf(c, cert))
UnsignedBDOC(c, cert) == BDOC(c, cert, Empty, DigestOf(c, cert))

\* Setup
DecThresholdParamsFromCrypto(cryptoParams) ==
  ThresholdParams(cryptoParams.decParams, cryptoParams.t, cryptoParams.n)
SigThresholdParamsFromCrypto(cryptoParams) ==
  ThresholdParams(cryptoParams.sigParams, cryptoParams.t, cryptoParams.n)
DecThresholdParamsFromConfig(cfg) ==
  DecThresholdParamsFromCrypto(cfg.cryptoParams)
SigThresholdParamsFromConfig(cfg) ==
  SigThresholdParamsFromCrypto(cfg.cryptoParams)
ThresholdShareStoreValues(shares) == {shares[i]: i \in DOMAIN shares}
ThresholdShareStorePK(shares) ==
  LET vals == ThresholdShareStoreValues(shares)
  IN IF vals # {} THEN PubKey(( CHOOSE s \in vals: TRUE ).sk) ELSE Empty

RecoverKeyFromShares(params, pk, shares) ==
  RecoverThresholdKey(params, pk, ThresholdShareStoreValues(shares))
DecryptShareStore(cardStore) ==
  [i \in DOMAIN cardStore |-> cardStore[i].decShare
  ]
SignShareStore(cardStore) == [i \in DOMAIN cardStore |-> cardStore[i].sigShare]

\* Voting
CSHasBallot(bdoc, ballotStore) ==
  \E v \in DOMAIN ballotStore: ballotStore[v].bdoc = bdoc
RegHasTSPFor(bdoc, regStore) ==
  \E i \in DOMAIN regStore: regStore[i].resp.m = Hash(bdoc.sig)
CreateAuthToken(k, cert, vid, nonce) == AEADEnc(k, << cert, vid >>, nonce)
OpenAuthToken(k, tok) == AEADDec(k, tok)
VerifyTrustedX509Cert(rootCACert, cert) ==
  VerifyX509Cert(cert) /\ cert.issuerCert = rootCACert

VoteVidsForVoter(ballotStore, voterId) ==
  {v \in DOMAIN ballotStore: ballotStore[v].voterId = voterId}

ProviderSidsForPhone(store, phone, kind) ==
  {sid \in DOMAIN store: /\ store[sid].phone = phone /\ store[sid].kind = kind}

ProviderSidForPhone(store, phone, kind) ==
  IF ProviderSidsForPhone(store, phone, kind) # {}
  THEN CHOOSE sid \in ProviderSidsForPhone(store, phone, kind): TRUE
  ELSE NoInt

\* Tally
Elems(store) == {store[v]: v \in DOMAIN store}
BallotHash(b) == Hash(<< b.id, b.t, b.votes >>)
ExtractTSPReqFromResp(res) == TSPReq(res.m, res.n)
RegReqs(regExport) == {regExport[i].req: i \in DOMAIN regExport}
RegIdxsForReq(req, regExport) ==
  {i \in DOMAIN regExport: regExport[i].req = req}

BallotsByVoterId(voterId, checkedBB) ==
  {br.ballot:
    br \in {x \in checkedBB: x.ballot.voter.voterId = voterId}
  }

BallotRespIdxsForResp(resp, brMap) == {i \in DOMAIN brMap: brMap[i].resp = resp}

KeepEarliestBallotResp(i, brMap) ==
  \A j \in BallotRespIdxsForResp(brMap[i].resp, brMap):
    \/ brMap[i].ballot.t < brMap[j].ballot.t
    \/ /\ brMap[i].ballot.t = brMap[j].ballot.t
       /\ i <= j

LatestBallot(ballots) ==
  IF ballots # {}
  THEN CHOOSE b \in ballots: \A other \in ballots: b.t >= other.t
  ELSE EmptyBallot

\* IsValidChoice
ValidDecVotes(cfg, bb) == {v \in bb: v.dp.m \in cfg.choices}
InvalidDecVotes(cfg, bb) == bb \ ValidDecVotes(cfg, bb)
TallyKeys(cfg, bb) ==
  {[ d |-> v.d, p |-> v.p, q |-> v.q ]:
    v \in ValidDecVotes(cfg, bb)
  }
VotesForTallyKeys(cfg, bb, tk) ==
  {v \in ValidDecVotes(cfg, bb): /\ v.d = tk.d /\ v.p = tk.p /\ v.q = tk.q}
CountVotesForChoice(cfg, bb, tk, choice) ==
  Cardinality({v \in VotesForTallyKeys(cfg, bb, tk): v.dp.m = choice})

BuildTally(cfg, bbDec) ==
  {TallyRow(tk.d, tk.p, tk.q, choice, CountVotesForChoice(cfg, bbDec, tk, choice)):
    tk \in TallyKeys(cfg, bbDec),
    choice \in cfg.choices
  }

BuildPlainBB(cfg, bbDec) ==
  {PlainVote(v.d, v.p, v.q, v.dp.m):
    v \in ValidDecVotes(cfg, bbDec)
  }

\* Audit
ERValidProofs(er) == er.proofs
ERInvalidVotes(er) == er.invalid
ERInvalidProofs(er) == {v.dp: v \in ERInvalidVotes(er)}
BallotboxCiphertexts(bb) == {a.ct: a \in bb}
ProofCiphertexts(proofs) == {dp.c: dp \in proofs}
ProofsUniqueByCiphertext(proofs) ==
  Cardinality(ProofCiphertexts(proofs)) = Cardinality(proofs)

====
