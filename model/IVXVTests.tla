---- MODULE IVXVTests ----
EXTENDS TLC, IVXVHelper

CONSTANTS SecretKeys, Messages, Nonces, PublicKeys, Keys, Values

Sign_Corr == \A sk \in SecretKeys, m \in Messages : Verify(PubKey(sk), m, Sign(sk, m))
X509_IssuedCertVerifies == 
	\A issuerSK \in SecretKeys, subjectPK \in PublicKeys, subject \in Messages :
    VerifyX509Cert(IssueX509Cert(issuerSK, subjectPK, subject))

X509_TamperedSubjectPKRejected == 
	\A issuerSK \in SecretKeys, pk1 \in PublicKeys, pk2 \in PublicKeys, subject \in Messages :
    pk1 # pk2 => ~VerifyX509Cert([IssueX509Cert(issuerSK, pk1, subject) EXCEPT !.pk = pk2])

X509_TamperedSubjectRejected == 
	\A issuerSK \in SecretKeys, pk \in PublicKeys, s1 \in Messages, s2 \in Messages :
		s1 # s2 => ~VerifyX509Cert([IssueX509Cert(issuerSK, pk, s1) EXCEPT !.pnoee = s2])

AEADEnc_Corr == \A k \in SecretKeys, m \in Messages, n \in Nonces : 
	AEADDec(k, AEADEnc(k, m, n)) = m

DecProof_Corr == \A sk \in SecretKeys, m \in Messages, r \in Nonces :
	LET c == EGEnc(PubKey(sk), m, r)
	IN VerifyDecryptionProof(PubKey(sk), DecryptionProof(sk, c, EGDec(sk, c)))

Primitive_Corr ==
	/\ Sign_Corr
	/\ AEADEnc_Corr
	/\ X509_IssuedCertVerifies
	/\ X509_TamperedSubjectPKRejected
	/\ X509_TamperedSubjectRejected
	/\ DecProof_Corr

ASSUME Primitive_Corr

VARIABLES st1
vars == << st1 >>
Init ==
  /\ st1 = Empty 
Next == TRUE /\ UNCHANGED vars
Spec == Init /\ [][Next]_vars

Keystore_Corr ==
  \A k \in Keys, v \in Values: StoreLookup(StorePut(st1, k, v), k) = v

Keystore_Override ==
  \A k \in Keys, v1 \in Values, v2 \in Values: StoreLookup(StorePut(StorePut(st1, k, v1), k, v2), k) = v2  

====