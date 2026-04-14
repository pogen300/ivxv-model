---- MODULE SetupPhase ----
EXTENDS IVXVChannel, Integers, TLC, IVXVConfig

EAPid == 0
CSPid == 1
KAPid == 2
VCDPid == 3
VVDPid == 4
PAPid == 5
KHPids == KeyHolderIds

(*--algorithm SetupPhase {
  variables
    chCSToEA = NoMsg,
    chKAToEA = NoMsg,
    chEAToCS = NoMsg,
    chEAToKA = NoMsg,
    chEAToVCD = NoMsg,
    chEAToVVD = NoMsg,
    chEAToPA = NoMsg,
    chKAToKH = [i \in KeyHolderIds |-> NoMsg],
    khSmartCardStore = EmptySmartCardStore(KeyHolderIds);

  fair process (CSProc = CSPid)
  variables
  	csTspClientPK = TSPClientPK,
    csCfg = Empty;
	{
  CS_ShareTSPClientPK:
    chCSToEA := Msg("CSSetup", [ tspClientPK |-> csTspClientPK ]);

  CS_RecvCSConfig:
    await chEAToCS.tag = "CSConfig";
		csCfg := chEAToCS.body.cfg;
		chCSToEA := NoMsg;
  
	CS_Done:
    skip;
  }

  fair process (KAProc = KAPid)
  variables
    decShares = EmptyThresholdShares(KeyHolderIds),
    sigShares = EmptyThresholdShares(KeyHolderIds),
    certDec = Empty,
    certSig = Empty;
  {
  KA_KeyAppInit:
    await chEAToKA.tag = "StartSetup";
    with (decParams = DecThresholdParamsFromCrypto(chEAToKA.body.cryptoParams),
          sigParams = SigThresholdParamsFromCrypto(chEAToKA.body.cryptoParams)) {
      with (newDecShares = GenerateKeyShares(chEAToKA.body.cryptoParams.decParams, KeyHolderIds, chEAToKA.body.cryptoParams.t, chEAToKA.body.cryptoParams.n),
            newSigShares = GenerateSignKeyShares(chEAToKA.body.cryptoParams.sigParams, KeyHolderIds, chEAToKA.body.cryptoParams.t, chEAToKA.body.cryptoParams.n)) {
        decShares := newDecShares;
        sigShares := newSigShares;
        with (decPK = ThresholdShareStorePK(newDecShares), sigPK = ThresholdShareStorePK(newSigShares)) {
          with (decSK = RecoverKeyFromShares(decParams, decPK, newDecShares),
                sigSK = RecoverKeyFromShares(sigParams, sigPK, newSigShares)) {
            with (sigShareSet = ThresholdShareStoreValues(newSigShares)) {
              certDec := X509Cert(decPK, NoStr, Cert(sigPK), ShoupSign(sigParams, sigPK, sigShareSet, Hash(<< decPK, NoStr >>)));
              certSig := X509Cert(sigPK, NoStr, Cert(sigPK), ShoupSign(sigParams, sigPK, sigShareSet, Hash(<< sigPK, NoStr >>)));
              assert PubKey(decSK) = decPK;
              assert PubKey(sigSK) = sigPK;
              chKAToEA := Msg("KASetup", [ decCert |-> certDec, sigCert |-> certSig ]);
              chKAToKH := [ i \in KeyHolderIds |-> Msg("KASetup", [ decShare |-> newDecShares[i], sigShare |-> newSigShares[i] ]) ];
            };
          };
        };
      };
		};
    chEAToKA := NoMsg;

  KA_Done:
    skip;
  }

	  fair process (EAProc = EAPid)
	  variables
	  	cryptoParams = CryptoParams(Threshold, ThresholdN, EGParams, RSAParams),
	    eaPublicCfg = PublicElectionConfig(ElectionId, Question1, CandidateList, Empty, Empty, RootCACert, Empty, TSPRegCert, OCSPCert, cryptoParams);
  {
  EA_SendCryptoParams:
    chEAToKA := Msg("StartSetup", [ cryptoParams |-> cryptoParams ]);

  EA_RecvElectionPK:
    await chKAToEA.tag = "KASetup";
    assert VerifyX509Cert(chKAToEA.body.decCert);
    assert VerifyX509Cert(chKAToEA.body.sigCert);
    eaPublicCfg := [ eaPublicCfg EXCEPT !.decCert = chKAToEA.body.decCert, !.sigCert = chKAToEA.body.sigCert ];
    chKAToEA := NoMsg;

  EA_RecvTSPClientPK:
    await chCSToEA.tag = "CSSetup";
    eaPublicCfg := [ eaPublicCfg EXCEPT !.tspClientPK = chCSToEA.body.tspClientPK ];
    chCSToEA := NoMsg;

  EA_ShareConfig:
    chEAToCS := Msg("CSConfig", [ cfg |-> CSConfig(eaPublicCfg, StageTTL, VerifyWindow, VerifyCountLimit, TSPPastSlack, TSPFutureSlack, VoterList) ]);
    chEAToVCD := Msg("PublicConfig", [ cfg |-> eaPublicCfg ]);
    chEAToVVD := Msg("PublicConfig", [ cfg |-> eaPublicCfg ]);
    chEAToPA := Msg("PublicConfig", [ cfg |-> eaPublicCfg ]);

  EA_Done:
    skip;
  }

  fair process (VCDProc = VCDPid)
  variables
    vcdPublicCfg = EmptyPublicElectionConfig;
  {
  VCD_RecvPublicConfig:
    await chEAToVCD.tag = "PublicConfig";
    vcdPublicCfg := chEAToVCD.body.cfg;
    chEAToVCD := NoMsg;

  VCD_Done:
    skip;
  }

  fair process (VVDProc = VVDPid)
  variables
    vvdPublicCfg = EmptyPublicElectionConfig;
  {
  VVD_RecvPublicConfig:
    await chEAToVVD.tag = "PublicConfig";
    vvdPublicCfg := chEAToVVD.body.cfg;
    chEAToVVD := NoMsg;

  VVD_Done:
    skip;
  }

  fair process (PAProc = PAPid)
  variables
    paPublicCfg = EmptyPublicElectionConfig;
  {
  PA_RecvPublicConfig:
    await chEAToPA.tag = "PublicConfig";
    paPublicCfg := chEAToPA.body.cfg;
    chEAToPA := NoMsg;

  PA_Done:
    skip;
  }

  fair process (KHProc \in KHPids)
  {
  KH_RecvShare:
    await chKAToKH[self].tag = "KASetup";
    khSmartCardStore := [khSmartCardStore EXCEPT ![self].decShare = chKAToKH[self].body.decShare, ![self].sigShare = chKAToKH[self].body.sigShare];
    chKAToKH := [chKAToKH EXCEPT ![self] = NoMsg];

  KH_Done:
    skip;
  }
}
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "40419c5b" /\ chksum(tla) = "758fb329")
VARIABLES pc, chCSToEA, chKAToEA, chEAToCS, chEAToKA, chEAToVCD, chEAToVVD, 
          chEAToPA, chKAToKH, khSmartCardStore, csTspClientPK, csCfg, 
          decShares, sigShares, certDec, certSig, cryptoParams, eaPublicCfg, 
          vcdPublicCfg, vvdPublicCfg, paPublicCfg

vars == << pc, chCSToEA, chKAToEA, chEAToCS, chEAToKA, chEAToVCD, chEAToVVD, 
           chEAToPA, chKAToKH, khSmartCardStore, csTspClientPK, csCfg, 
           decShares, sigShares, certDec, certSig, cryptoParams, eaPublicCfg, 
           vcdPublicCfg, vvdPublicCfg, paPublicCfg >>

ProcSet == {CSPid} \cup {KAPid} \cup {EAPid} \cup {VCDPid} \cup {VVDPid} \cup {PAPid} \cup (KHPids)

Init == (* Global variables *)
        /\ chCSToEA = NoMsg
        /\ chKAToEA = NoMsg
        /\ chEAToCS = NoMsg
        /\ chEAToKA = NoMsg
        /\ chEAToVCD = NoMsg
        /\ chEAToVVD = NoMsg
        /\ chEAToPA = NoMsg
        /\ chKAToKH = [i \in KeyHolderIds |-> NoMsg]
        /\ khSmartCardStore = EmptySmartCardStore(KeyHolderIds)
        (* Process CSProc *)
        /\ csTspClientPK = TSPClientPK
        /\ csCfg = Empty
        (* Process KAProc *)
        /\ decShares = EmptyThresholdShares(KeyHolderIds)
        /\ sigShares = EmptyThresholdShares(KeyHolderIds)
        /\ certDec = Empty
        /\ certSig = Empty
        (* Process EAProc *)
        /\ cryptoParams = CryptoParams(Threshold, ThresholdN, EGParams, RSAParams)
        /\ eaPublicCfg = PublicElectionConfig(ElectionId, Question1, CandidateList, Empty, Empty, RootCACert, Empty, TSPRegCert, OCSPCert, cryptoParams)
        (* Process VCDProc *)
        /\ vcdPublicCfg = EmptyPublicElectionConfig
        (* Process VVDProc *)
        /\ vvdPublicCfg = EmptyPublicElectionConfig
        (* Process PAProc *)
        /\ paPublicCfg = EmptyPublicElectionConfig
        /\ pc = [self \in ProcSet |-> CASE self = CSPid -> "CS_ShareTSPClientPK"
                                        [] self = KAPid -> "KA_KeyAppInit"
                                        [] self = EAPid -> "EA_SendCryptoParams"
                                        [] self = VCDPid -> "VCD_RecvPublicConfig"
                                        [] self = VVDPid -> "VVD_RecvPublicConfig"
                                        [] self = PAPid -> "PA_RecvPublicConfig"
                                        [] self \in KHPids -> "KH_RecvShare"]

CS_ShareTSPClientPK == /\ pc[CSPid] = "CS_ShareTSPClientPK"
                       /\ chCSToEA' = Msg("CSSetup", [ tspClientPK |-> csTspClientPK ])
                       /\ pc' = [pc EXCEPT ![CSPid] = "CS_RecvCSConfig"]
                       /\ UNCHANGED << chKAToEA, chEAToCS, chEAToKA, chEAToVCD, 
                                       chEAToVVD, chEAToPA, chKAToKH, 
                                       khSmartCardStore, csTspClientPK, csCfg, 
                                       decShares, sigShares, certDec, certSig, 
                                       cryptoParams, eaPublicCfg, vcdPublicCfg, 
                                       vvdPublicCfg, paPublicCfg >>

CS_RecvCSConfig == /\ pc[CSPid] = "CS_RecvCSConfig"
                   /\ chEAToCS.tag = "CSConfig"
                   /\ csCfg' = chEAToCS.body.cfg
                   /\ chCSToEA' = NoMsg
                   /\ pc' = [pc EXCEPT ![CSPid] = "CS_Done"]
                   /\ UNCHANGED << chKAToEA, chEAToCS, chEAToKA, chEAToVCD, 
                                   chEAToVVD, chEAToPA, chKAToKH, 
                                   khSmartCardStore, csTspClientPK, decShares, 
                                   sigShares, certDec, certSig, cryptoParams, 
                                   eaPublicCfg, vcdPublicCfg, vvdPublicCfg, 
                                   paPublicCfg >>

CS_Done == /\ pc[CSPid] = "CS_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![CSPid] = "Done"]
           /\ UNCHANGED << chCSToEA, chKAToEA, chEAToCS, chEAToKA, chEAToVCD, 
                           chEAToVVD, chEAToPA, chKAToKH, khSmartCardStore, 
                           csTspClientPK, csCfg, decShares, sigShares, certDec, 
                           certSig, cryptoParams, eaPublicCfg, vcdPublicCfg, 
                           vvdPublicCfg, paPublicCfg >>

CSProc == CS_ShareTSPClientPK \/ CS_RecvCSConfig \/ CS_Done

KA_KeyAppInit == /\ pc[KAPid] = "KA_KeyAppInit"
                 /\ chEAToKA.tag = "StartSetup"
                 /\ LET decParams == DecThresholdParamsFromCrypto(chEAToKA.body.cryptoParams) IN
                      LET sigParams == SigThresholdParamsFromCrypto(chEAToKA.body.cryptoParams) IN
                        LET newDecShares == GenerateKeyShares(chEAToKA.body.cryptoParams.decParams, KeyHolderIds, chEAToKA.body.cryptoParams.t, chEAToKA.body.cryptoParams.n) IN
                          LET newSigShares == GenerateSignKeyShares(chEAToKA.body.cryptoParams.sigParams, KeyHolderIds, chEAToKA.body.cryptoParams.t, chEAToKA.body.cryptoParams.n) IN
                            /\ decShares' = newDecShares
                            /\ sigShares' = newSigShares
                            /\ LET decPK == ThresholdShareStorePK(newDecShares) IN
                                 LET sigPK == ThresholdShareStorePK(newSigShares) IN
                                   LET decSK == RecoverKeyFromShares(decParams, decPK, newDecShares) IN
                                     LET sigSK == RecoverKeyFromShares(sigParams, sigPK, newSigShares) IN
                                       LET sigShareSet == ThresholdShareStoreValues(newSigShares) IN
                                         /\ certDec' = X509Cert(decPK, NoStr, Cert(sigPK), ShoupSign(sigParams, sigPK, sigShareSet, Hash(<< decPK, NoStr >>)))
                                         /\ certSig' = X509Cert(sigPK, NoStr, Cert(sigPK), ShoupSign(sigParams, sigPK, sigShareSet, Hash(<< sigPK, NoStr >>)))
                                         /\ Assert(PubKey(decSK) = decPK, 
                                                   "Failure of assertion at line 62, column 15.")
                                         /\ Assert(PubKey(sigSK) = sigPK, 
                                                   "Failure of assertion at line 63, column 15.")
                                         /\ chKAToEA' = Msg("KASetup", [ decCert |-> certDec', sigCert |-> certSig' ])
                                         /\ chKAToKH' = [ i \in KeyHolderIds |-> Msg("KASetup", [ decShare |-> newDecShares[i], sigShare |-> newSigShares[i] ]) ]
                 /\ chEAToKA' = NoMsg
                 /\ pc' = [pc EXCEPT ![KAPid] = "KA_Done"]
                 /\ UNCHANGED << chCSToEA, chEAToCS, chEAToVCD, chEAToVVD, 
                                 chEAToPA, khSmartCardStore, csTspClientPK, 
                                 csCfg, cryptoParams, eaPublicCfg, 
                                 vcdPublicCfg, vvdPublicCfg, paPublicCfg >>

KA_Done == /\ pc[KAPid] = "KA_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![KAPid] = "Done"]
           /\ UNCHANGED << chCSToEA, chKAToEA, chEAToCS, chEAToKA, chEAToVCD, 
                           chEAToVVD, chEAToPA, chKAToKH, khSmartCardStore, 
                           csTspClientPK, csCfg, decShares, sigShares, certDec, 
                           certSig, cryptoParams, eaPublicCfg, vcdPublicCfg, 
                           vvdPublicCfg, paPublicCfg >>

KAProc == KA_KeyAppInit \/ KA_Done

EA_SendCryptoParams == /\ pc[EAPid] = "EA_SendCryptoParams"
                       /\ chEAToKA' = Msg("StartSetup", [ cryptoParams |-> cryptoParams ])
                       /\ pc' = [pc EXCEPT ![EAPid] = "EA_RecvElectionPK"]
                       /\ UNCHANGED << chCSToEA, chKAToEA, chEAToCS, chEAToVCD, 
                                       chEAToVVD, chEAToPA, chKAToKH, 
                                       khSmartCardStore, csTspClientPK, csCfg, 
                                       decShares, sigShares, certDec, certSig, 
                                       cryptoParams, eaPublicCfg, vcdPublicCfg, 
                                       vvdPublicCfg, paPublicCfg >>

EA_RecvElectionPK == /\ pc[EAPid] = "EA_RecvElectionPK"
                     /\ chKAToEA.tag = "KASetup"
                     /\ Assert(VerifyX509Cert(chKAToEA.body.decCert), 
                               "Failure of assertion at line 87, column 5.")
                     /\ Assert(VerifyX509Cert(chKAToEA.body.sigCert), 
                               "Failure of assertion at line 88, column 5.")
                     /\ eaPublicCfg' = [ eaPublicCfg EXCEPT !.decCert = chKAToEA.body.decCert, !.sigCert = chKAToEA.body.sigCert ]
                     /\ chKAToEA' = NoMsg
                     /\ pc' = [pc EXCEPT ![EAPid] = "EA_RecvTSPClientPK"]
                     /\ UNCHANGED << chCSToEA, chEAToCS, chEAToKA, chEAToVCD, 
                                     chEAToVVD, chEAToPA, chKAToKH, 
                                     khSmartCardStore, csTspClientPK, csCfg, 
                                     decShares, sigShares, certDec, certSig, 
                                     cryptoParams, vcdPublicCfg, vvdPublicCfg, 
                                     paPublicCfg >>

EA_RecvTSPClientPK == /\ pc[EAPid] = "EA_RecvTSPClientPK"
                      /\ chCSToEA.tag = "CSSetup"
                      /\ eaPublicCfg' = [ eaPublicCfg EXCEPT !.tspClientPK = chCSToEA.body.tspClientPK ]
                      /\ chCSToEA' = NoMsg
                      /\ pc' = [pc EXCEPT ![EAPid] = "EA_ShareConfig"]
                      /\ UNCHANGED << chKAToEA, chEAToCS, chEAToKA, chEAToVCD, 
                                      chEAToVVD, chEAToPA, chKAToKH, 
                                      khSmartCardStore, csTspClientPK, csCfg, 
                                      decShares, sigShares, certDec, certSig, 
                                      cryptoParams, vcdPublicCfg, vvdPublicCfg, 
                                      paPublicCfg >>

EA_ShareConfig == /\ pc[EAPid] = "EA_ShareConfig"
                  /\ chEAToCS' = Msg("CSConfig", [ cfg |-> CSConfig(eaPublicCfg, StageTTL, VerifyWindow, VerifyCountLimit, TSPPastSlack, TSPFutureSlack, VoterList) ])
                  /\ chEAToVCD' = Msg("PublicConfig", [ cfg |-> eaPublicCfg ])
                  /\ chEAToVVD' = Msg("PublicConfig", [ cfg |-> eaPublicCfg ])
                  /\ chEAToPA' = Msg("PublicConfig", [ cfg |-> eaPublicCfg ])
                  /\ pc' = [pc EXCEPT ![EAPid] = "EA_Done"]
                  /\ UNCHANGED << chCSToEA, chKAToEA, chEAToKA, chKAToKH, 
                                  khSmartCardStore, csTspClientPK, csCfg, 
                                  decShares, sigShares, certDec, certSig, 
                                  cryptoParams, eaPublicCfg, vcdPublicCfg, 
                                  vvdPublicCfg, paPublicCfg >>

EA_Done == /\ pc[EAPid] = "EA_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![EAPid] = "Done"]
           /\ UNCHANGED << chCSToEA, chKAToEA, chEAToCS, chEAToKA, chEAToVCD, 
                           chEAToVVD, chEAToPA, chKAToKH, khSmartCardStore, 
                           csTspClientPK, csCfg, decShares, sigShares, certDec, 
                           certSig, cryptoParams, eaPublicCfg, vcdPublicCfg, 
                           vvdPublicCfg, paPublicCfg >>

EAProc == EA_SendCryptoParams \/ EA_RecvElectionPK \/ EA_RecvTSPClientPK
             \/ EA_ShareConfig \/ EA_Done

VCD_RecvPublicConfig == /\ pc[VCDPid] = "VCD_RecvPublicConfig"
                        /\ chEAToVCD.tag = "PublicConfig"
                        /\ vcdPublicCfg' = chEAToVCD.body.cfg
                        /\ chEAToVCD' = NoMsg
                        /\ pc' = [pc EXCEPT ![VCDPid] = "VCD_Done"]
                        /\ UNCHANGED << chCSToEA, chKAToEA, chEAToCS, chEAToKA, 
                                        chEAToVVD, chEAToPA, chKAToKH, 
                                        khSmartCardStore, csTspClientPK, csCfg, 
                                        decShares, sigShares, certDec, certSig, 
                                        cryptoParams, eaPublicCfg, 
                                        vvdPublicCfg, paPublicCfg >>

VCD_Done == /\ pc[VCDPid] = "VCD_Done"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![VCDPid] = "Done"]
            /\ UNCHANGED << chCSToEA, chKAToEA, chEAToCS, chEAToKA, chEAToVCD, 
                            chEAToVVD, chEAToPA, chKAToKH, khSmartCardStore, 
                            csTspClientPK, csCfg, decShares, sigShares, 
                            certDec, certSig, cryptoParams, eaPublicCfg, 
                            vcdPublicCfg, vvdPublicCfg, paPublicCfg >>

VCDProc == VCD_RecvPublicConfig \/ VCD_Done

VVD_RecvPublicConfig == /\ pc[VVDPid] = "VVD_RecvPublicConfig"
                        /\ chEAToVVD.tag = "PublicConfig"
                        /\ vvdPublicCfg' = chEAToVVD.body.cfg
                        /\ chEAToVVD' = NoMsg
                        /\ pc' = [pc EXCEPT ![VVDPid] = "VVD_Done"]
                        /\ UNCHANGED << chCSToEA, chKAToEA, chEAToCS, chEAToKA, 
                                        chEAToVCD, chEAToPA, chKAToKH, 
                                        khSmartCardStore, csTspClientPK, csCfg, 
                                        decShares, sigShares, certDec, certSig, 
                                        cryptoParams, eaPublicCfg, 
                                        vcdPublicCfg, paPublicCfg >>

VVD_Done == /\ pc[VVDPid] = "VVD_Done"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![VVDPid] = "Done"]
            /\ UNCHANGED << chCSToEA, chKAToEA, chEAToCS, chEAToKA, chEAToVCD, 
                            chEAToVVD, chEAToPA, chKAToKH, khSmartCardStore, 
                            csTspClientPK, csCfg, decShares, sigShares, 
                            certDec, certSig, cryptoParams, eaPublicCfg, 
                            vcdPublicCfg, vvdPublicCfg, paPublicCfg >>

VVDProc == VVD_RecvPublicConfig \/ VVD_Done

PA_RecvPublicConfig == /\ pc[PAPid] = "PA_RecvPublicConfig"
                       /\ chEAToPA.tag = "PublicConfig"
                       /\ paPublicCfg' = chEAToPA.body.cfg
                       /\ chEAToPA' = NoMsg
                       /\ pc' = [pc EXCEPT ![PAPid] = "PA_Done"]
                       /\ UNCHANGED << chCSToEA, chKAToEA, chEAToCS, chEAToKA, 
                                       chEAToVCD, chEAToVVD, chKAToKH, 
                                       khSmartCardStore, csTspClientPK, csCfg, 
                                       decShares, sigShares, certDec, certSig, 
                                       cryptoParams, eaPublicCfg, vcdPublicCfg, 
                                       vvdPublicCfg >>

PA_Done == /\ pc[PAPid] = "PA_Done"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![PAPid] = "Done"]
           /\ UNCHANGED << chCSToEA, chKAToEA, chEAToCS, chEAToKA, chEAToVCD, 
                           chEAToVVD, chEAToPA, chKAToKH, khSmartCardStore, 
                           csTspClientPK, csCfg, decShares, sigShares, certDec, 
                           certSig, cryptoParams, eaPublicCfg, vcdPublicCfg, 
                           vvdPublicCfg, paPublicCfg >>

PAProc == PA_RecvPublicConfig \/ PA_Done

KH_RecvShare(self) == /\ pc[self] = "KH_RecvShare"
                      /\ chKAToKH[self].tag = "KASetup"
                      /\ khSmartCardStore' = [khSmartCardStore EXCEPT ![self].decShare = chKAToKH[self].body.decShare, ![self].sigShare = chKAToKH[self].body.sigShare]
                      /\ chKAToKH' = [chKAToKH EXCEPT ![self] = NoMsg]
                      /\ pc' = [pc EXCEPT ![self] = "KH_Done"]
                      /\ UNCHANGED << chCSToEA, chKAToEA, chEAToCS, chEAToKA, 
                                      chEAToVCD, chEAToVVD, chEAToPA, 
                                      csTspClientPK, csCfg, decShares, 
                                      sigShares, certDec, certSig, 
                                      cryptoParams, eaPublicCfg, vcdPublicCfg, 
                                      vvdPublicCfg, paPublicCfg >>

KH_Done(self) == /\ pc[self] = "KH_Done"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << chCSToEA, chKAToEA, chEAToCS, chEAToKA, 
                                 chEAToVCD, chEAToVVD, chEAToPA, chKAToKH, 
                                 khSmartCardStore, csTspClientPK, csCfg, 
                                 decShares, sigShares, certDec, certSig, 
                                 cryptoParams, eaPublicCfg, vcdPublicCfg, 
                                 vvdPublicCfg, paPublicCfg >>

KHProc(self) == KH_RecvShare(self) \/ KH_Done(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == CSProc \/ KAProc \/ EAProc \/ VCDProc \/ VVDProc \/ PAProc
           \/ (\E self \in KHPids: KHProc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(CSProc)
        /\ WF_vars(KAProc)
        /\ WF_vars(EAProc)
        /\ WF_vars(VCDProc)
        /\ WF_vars(VVDProc)
        /\ WF_vars(PAProc)
        /\ \A self \in KHPids : WF_vars(KHProc(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

SetupComplete == \A self \in ProcSet: pc[self] = "Done"

Inv_EAConfigBuiltFromInputs ==
  SetupComplete =>
    /\ eaPublicCfg.decCert = ExpectedElectionCert
    /\ eaPublicCfg.sigCert = ExpectedSignCert
    /\ eaPublicCfg.rootCACert = RootCACert
    /\ VerifyX509Cert(eaPublicCfg.decCert)
    /\ VerifyX509Cert(eaPublicCfg.sigCert)
    /\ eaPublicCfg.decCert.pk = ExpectedElectionPK
    /\ eaPublicCfg.sigCert.pk = ExpectedSignPK
    /\ eaPublicCfg.tspClientPK = TSPClientPK
    /\ eaPublicCfg = ExpectedPublicConfig

Inv_AllConfigValid ==
  SetupComplete =>
    /\ vcdPublicCfg = ExpectedPublicConfig 
		/\ vvdPublicCfg = ExpectedPublicConfig 
		/\ paPublicCfg = ExpectedPublicConfig
		/\ csCfg = ExpectedCSConfig

Inv_DecryptSharesRecoverElectionSK ==
  SetupComplete =>
    /\ RecoverKeyFromShares(ExpectedDecThresholdParams, ExpectedElectionPK, ExpectedDecShares) = ElectionSK
    /\ RecoverKeyFromShares(ExpectedDecThresholdParams, ExpectedElectionPK, DecryptShareStore(khSmartCardStore)) = ElectionSK
    /\ RecoverKeyFromShares(ExpectedSigThresholdParams, ExpectedSignPK, ExpectedSigShares) = ElectionSignSK
    /\ RecoverKeyFromShares(ExpectedSigThresholdParams, ExpectedSignPK, SignShareStore(khSmartCardStore)) = ElectionSignSK
=============================================================================
