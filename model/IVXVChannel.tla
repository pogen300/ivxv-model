------------------------------ MODULE IVXVChannel ------------------------------
EXTENDS IVXVData

NoBody == [ dummy |-> TRUE ]
Msg(tag, body) == [ tag |-> tag, body |-> body ]
NoMsg == Msg("None", NoBody)
VoteReq(choices, bdoc) == [choices |-> choices, bdoc |-> bdoc]
NoVoteReq == VoteReq({}, EmptyBDOC)
VoteRes(vid, tsp, ocsp) == [vid |-> vid, tsp |-> tsp, ocsp |-> ocsp]
NoVoteRes == VoteRes(NoInt, NoTSPRes, NoOCSPRes)
VerifyRes(bdoc, tsp, ocsp, choices) == [bdoc |-> bdoc, tsp |-> tsp, ocsp |-> ocsp, choices |-> choices]
VoterToVCD(kind, payload) == Msg(kind, [ payload |-> payload ])
VCDToVoter(kind, payload) == Msg(kind, [ payload |-> payload ])
VCDToCS(kind, sidCS, sidProv, tok, payload) == Msg(kind, [ sidCS |-> sidCS, sidProv |-> sidProv, tok |-> tok, payload |-> payload ])
CSToVCD(kind, sidCS, sidProv, payload) == Msg(kind, [ sidCS |-> sidCS, sidProv |-> sidProv, payload |-> payload ])
CSToProvider(kind, sidCS, sidProv, payload) == Msg(kind, [ sidCS |-> sidCS, sidProv |-> sidProv, payload |-> payload ])
ProviderToCS(kind, sidCS, sidProv, payload) == Msg(kind, [ sidCS |-> sidCS, sidProv |-> sidProv, payload |-> payload ])
ProviderToSign(kind, payload) == Msg(kind, [ payload |-> payload ])
SignToProvider(kind, payload) == Msg(kind, [ payload |-> payload ])
SignToVoter(kind, payload) == Msg(kind, [ payload |-> payload ])
VoterToSign(kind, payload) == Msg(kind, [ payload |-> payload ])
VoterToVVD(kind, payload) == Msg(kind, [ payload |-> payload ])
CSToReg(kind, payload) == Msg(kind, [ payload |-> payload ])
RegToCS(kind, payload) == Msg(kind, [ payload |-> payload ])
VCDToVVD(kind, r, vid, sidCS) == Msg(kind, [ r |-> r, vid |-> vid, sidCS |-> sidCS ])
VVDToCS(kind, sidCS, vid) == Msg(kind, [ sidCS |-> sidCS, vid   |-> vid ])
CSToVVD(kind, payload) == Msg(kind, [ payload |-> payload ])
VVDToVoter(kind, payload) == Msg(kind, [ payload |-> payload ])

CanAdvance(from, to) ==
  \/ /\ from = "Auth" /\ to = "AuthStatus"
  \/ /\ from = "AuthStatus" /\ to = "AuthStatus"
  \/ /\ from = "AuthStatus" /\ to = "Choices"
  \/ /\ from = "Choices" /\ to = "Cert"
  \/ /\ from = "Cert" /\ to = "Sign"
  \/ /\ from = "Sign" /\ to = "SignStatus"
  \/ /\ from = "SignStatus" /\ to = "SignStatus"
  \/ /\ from = "SignStatus" /\ to = "Vote"
  \/ /\ from = "Vote" /\ to = "Verify"
  \/ /\ from = "Verify" /\ to = "Verify"

VoterCanAdvance(from, to) ==
	\/ /\ from = "Idle" /\ to = "AuthPending"
	\/ /\ from = "AuthPending" /\ to = "ChoicePending"
	\/ /\ from = "ChoicePending" /\ to = "SignPending"
	\/ /\ from = "SignPending" /\ to = "VerifyPending"
	\/ /\ from = "VerifyPending" /\ to = "Verified"

=============================================================================
