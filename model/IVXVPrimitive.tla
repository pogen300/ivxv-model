------------------------------ MODULE IVXVPrimitive ------------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets
NoInt == -1
NoStr == ""
Empty == <<>>

\* pk
PubKey(sk) == << "pk", sk >>


\* hash
Hash(m) == << "hash", m >>

\* signature
Sign(sk, m) == << "sig", PubKey(sk), m >>
Verify(pk, m, sig) ==
  /\ sig # Empty
  /\ Len(sig) = 3
  /\ sig[1] = "sig"
  /\ sig[2] = pk
  /\ sig[3] = m

\* certificate
Cert(pk) == << "cert", pk >>
CertPK(cert) == cert[2]

X509Cert(pk, pnoee, issuerCert, sig) == [ pk |-> pk, pnoee |-> pnoee, issuerCert |-> issuerCert, sig |-> sig ]
X509CertTBS(c) == Hash(<< c.pk, c.pnoee >>)
IssueX509Cert(issuerSK, pk, pnoee) == 
  LET issuerCert == Cert(PubKey(issuerSK))
      sig == Sign(issuerSK, Hash(<< pk, pnoee >>))
  IN X509Cert(pk, pnoee, issuerCert, sig)
VerifyX509Cert(c) == Verify(CertPK(c.issuerCert), X509CertTBS(c), c.sig)

\* sym enc
AEADEnc(k, m, n) == << "aead", k, m, n >>

AEADDec(k, c) ==
  IF /\ c # Empty
     /\ Len(c) = 4
     /\ c[1] = "aead"
     /\ c[2] = k
  THEN c[3]
  ELSE Empty

\* asym enc
EGEnc(pk, m, r) == << "eg", pk, m, r >>

EGCheckRandomness(c, r) ==
  /\ c # Empty
  /\ Len(c) = 4
  /\ c[1] = "eg"
  /\ c[4] = r

\* Abstract ciphertext validity check
IsValidEGCiphertext(pk, c) ==
  /\ c # Empty
  /\ Len(c) = 4
  /\ c[1] = "eg"
  /\ c[2] = pk

EGDec(sk, c) ==
  IF	/\ IsValidEGCiphertext(PubKey(sk), c)
  THEN c[3]
  ELSE Empty

DecryptionProof(sk,c, m) ==  [ sk |-> sk, c |-> c, m |-> m ]
VerifyDecryptionProof(pk, dp) == 
	/\ IsValidEGCiphertext(pk, dp.c)
	/\ pk = PubKey(dp.sk) 
	/\ EGDec(dp.sk, dp.c) = dp.m

\* ideal threshold keys
ThresholdParams(kind, t, n) == [ kind |-> kind, t |-> t, n |-> n ]
ThresholdShare(holderId, params, sk) ==
  [ holderId |-> holderId,
    params   |-> params,
    sk       |-> sk ]
ThresholdShareStore(ids, params, sk) == [ i \in ids |-> ThresholdShare(i, params, sk) ]
SameThresholdParams(shares) ==
  \A s1 \in shares, s2 \in shares : s1.params = s2.params /\ s1.sk = s2.sk

DistinctShareHolders(shares) == 
Cardinality({ s.holderId : s \in shares }) = Cardinality(shares)
ValidThresholdShareSet(params, pk, shares) ==
  /\ shares # {}
  /\ Cardinality(shares) >= params.t
  /\ Cardinality(shares) <= params.n
  /\ DistinctShareHolders(shares)
  /\ \A s \in shares : s.params = params /\ PubKey(s.sk) = pk
  /\ SameThresholdParams(shares)

RecoverThresholdKey(params, pk, shares) ==
  IF ValidThresholdShareSet(params, pk, shares)
  THEN (CHOOSE s \in shares : TRUE).sk
  ELSE NoStr

ShoupSign(params, pk, shares, m) ==
	LET sk == RecoverThresholdKey(params, pk, shares)
	IN IF sk # NoStr THEN Sign(sk, m) ELSE Empty

IdealMix(X) == X

=============================================================================
