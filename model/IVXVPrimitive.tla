------------------------------ MODULE IVXVPrimitive ------------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANTS SecretKeys, Messages

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

Sign_Corr == \A sk \in SecretKeys, m \in Messages :
    Verify(PubKey(sk), m, Sign(sk, m))

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

IsEGCiphertextFor(pk, c) ==
  /\ c # Empty
  /\ Len(c) = 4
  /\ c[1] = "eg"
  /\ c[2] = pk

EGDec(sk, c) ==
  IF /\ c # Empty
     /\ Len(c) = 4
     /\ c[1] = "eg"
     /\ c[2] = PubKey(sk)
  THEN c[3]
  ELSE Empty

VerifyDecryptionProof(pk, dp) ==
  /\ IsEGCiphertextFor(pk, dp.c)
  /\ dp.m = dp.c[3]

\* ideal threshold keys
ThresholdParams(kind, t, n) == [ kind |-> kind, t |-> t, n |-> n ]
ThresholdKey(params, sk) == [ params |-> params, sk |-> sk, pk |-> PubKey(sk) ]
ThresholdShare(key, holderId) ==
  [ holderId |-> holderId,
    params   |-> key.params,
    pk       |-> key.pk,
    sk       |-> key.sk ]

EmptyThresholdShares(ids) == [ i \in ids |-> Empty ]
ThresholdShareStore(key, holderIds) == [ i \in holderIds |-> ThresholdShare(key, i) ]

SameThresholdKey(shares) ==
  \A s1 \in shares, s2 \in shares :
  	s1.params = s2.params /\ s1.pk = s2.pk /\ s1.sk = s2.sk
DistinctShareHolders(shares) == Cardinality({ s.holderId : s \in shares }) = Cardinality(shares)
EnoughThresholdShares(params, shares) == Cardinality(shares) >= params.t

ValidThresholdShareSet(params, pk, shares) ==
  /\ shares # {}
  /\ EnoughThresholdShares(params, shares)
  /\ Cardinality(shares) <= params.n
  /\ DistinctShareHolders(shares)
  /\ \A s \in shares : s.params = params /\ s.pk = pk
  /\ SameThresholdKey(shares)

RecoverThresholdKey(params, pk, shares) ==
  IF ValidThresholdShareSet(params, pk, shares)
  THEN (CHOOSE s \in shares : TRUE).sk
  ELSE Empty

ShoupSign(params, pk, shares, m) ==
  IF ValidThresholdShareSet(params, pk, shares)
  THEN Sign(RecoverThresholdKey(params, pk, shares), m)
  ELSE Empty

IdealMix(X) == X

=============================================================================
