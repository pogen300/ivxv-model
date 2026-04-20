------------------------------ MODULE IVXVPrimitive ------------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets, IVXVData


\* pk
PubKey(sk) == << "pk", sk >>

\* hash
Hash(m) == << "hash", m >>

\* signature
Sign(sk, m) == [ type |-> "sig", pk |-> PubKey(sk), m |-> m ]

Verify(pk, m, sig) ==
  /\ sig.type = "sig"
  /\ sig.pk = pk
  /\ sig.m = m

\* certificate
Cert(pk) == [ type |-> "cert", pk |-> pk ]
CertPK(cert) == 
	IF cert.type = "cert"
  THEN cert.pk
  ELSE Empty

X509Cert(pk, pnoee, issuerCert, sig) == 
	[ type |-> "x509cert", pk |-> pk, pnoee |-> pnoee, issuerCert |-> issuerCert, sig |-> sig ]

X509CertTBS(c) == Hash(<< c.pk, c.pnoee >>)
IssueX509Cert(issuerSK, pk, pnoee) == 
  LET issuerCert == Cert(PubKey(issuerSK))
      sig == Sign(issuerSK, Hash(<< pk, pnoee >>))
  IN X509Cert(pk, pnoee, issuerCert, sig)
VerifyX509Cert(c) == Verify(CertPK(c.issuerCert), X509CertTBS(c), c.sig)

\* sym enc
AEADEnc(k, m, n) == [ type |-> "aead", k |-> k, m |-> m, n |-> n ]
	
AEADDec(k, c) ==
  IF /\ c.type = "aead"
     /\ c.k = k
  THEN c.m
  ELSE Empty

\* asym enc
EGEnc(pk, m, r) == [ type |-> "eg", pk |-> pk, m |-> m, r |-> r ]
	
EGCheckRandomness(c, r) == /\ c.type = "eg" /\ c.r = r

\* Abstract ciphertext validity check
IsValidEGCiphertext(pk, c) == /\ c.type = "eg" /\ c.pk = pk

EGDec(sk, c) ==
  IF	/\ IsValidEGCiphertext(PubKey(sk), c)
  THEN c.m
  ELSE Empty

DecryptionProof(witness, c, m) ==  [ witness |-> witness, c |-> c, m |-> m ]
VerifyDecryptionProof(pk, dp) == 
	/\ IsValidEGCiphertext(pk, dp.c)
	/\ pk = PubKey(dp.witness) 
	/\ EGDec(dp.witness, dp.c) = dp.m

\* ideal threshold keys, kind: e.g., "EG"
ThresholdParams(kind, t, n) == [ kind |-> kind, t |-> t, n |-> n ]

ThresholdShare(holderId, params, witness) ==
  [ holderId |-> holderId,
    params   |-> params,
    witness  |-> witness ]
ThresholdShareStore(ids, params, witness) == [ i \in ids |-> ThresholdShare(i, params, witness) ]
SameThresholdParams(shares) ==
  \A s1 \in shares, s2 \in shares : s1.params = s2.params /\ s1.witness = s2.witness

DistinctShareHolders(shares) == Cardinality({ s.holderId : s \in shares }) = Cardinality(shares)

ValidThresholdShareSet(params, pk, shares) ==
  /\ Cardinality(shares) >= params.t
  /\ Cardinality(shares) <= params.n
  /\ DistinctShareHolders(shares)
  /\ \A s \in shares : s.params = params /\ PubKey(s.witness) = pk
  /\ SameThresholdParams(shares)

RecoverThresholdKey(params, pk, shares) ==
  IF ValidThresholdShareSet(params, pk, shares)
  THEN (CHOOSE s \in shares : TRUE).witness
  ELSE NoStr

ShoupSign(params, pk, shares, m) ==
	LET witness == RecoverThresholdKey(params, pk, shares)
	IN IF witness # NoStr THEN Sign(witness, m) ELSE Empty

IdealMix(X) == X

=============================================================================
