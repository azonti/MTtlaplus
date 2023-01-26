-------------------------- MODULE ScriptSemantics --------------------------

LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE CryptoObjs
LOCAL INSTANCE Scripts

RECURSIVE ArithSemantics(_,_), PredSemantics(_,_,_,_,_,_,_)

ArithSemantics(wit,aic) ==
CASE /\ aic.A.type = "Arith_const"
     /\ TRUE
        /\ aic.stackSize <=  999 -> [isIntNaN |-> FALSE,
                                     int |-> aic.A.int,
                                     stackSize |-> aic.stackSize + 1]
  [] /\ aic.A.type = "Arith_const"
     /\ FALSE
        \/ aic.stackSize >= 1000 -> [isIntNaN |-> TRUE,
                                     int |-> 0,
                                     stackSize |-> aic.stackSize]
  [] /\ aic.A.type = "Arith_size_wit"
     /\ TRUE
        /\ aic.A.i < Len(wit)
        /\ aic.stackSize <=  998 -> [isIntNaN |-> FALSE,
                                     int |-> nBytes_for_CryptoObj(wit[aic.A.i + 1]),
                                     stackSize |-> aic.stackSize + 1]
  [] /\ aic.A.type = "Arith_size_wit"
     /\ FALSE
        \/ aic.A.i >= Len(wit)
        \/ aic.stackSize >=  999 -> [isIntNaN |-> TRUE,
                                     int |-> 0,
                                     stackSize |-> aic.stackSize]
  [] /\ aic.A.type = "Arith_neg" ->
     LET atc == ArithSemantics(wit,[A |-> aic.A.A, stackSize |-> aic.stackSize]) IN
     [isIntNaN |-> atc.isIntNaN,
      int |-> -atc.int,
      stackSize |-> atc.stackSize]
  [] /\ aic.A.type = "Arith_abs" ->
     LET atc == ArithSemantics(wit,[A |-> aic.A.A, stackSize |-> aic.stackSize]) IN
     [isIntNaN |-> atc.isIntNaN,
      int |-> abs(atc.int),
      stackSize |-> atc.stackSize]
  [] /\ aic.A.type = "Arith_add" ->
     LET atc1 == ArithSemantics(wit,[A |-> aic.A.A1, stackSize |-> aic.stackSize]) IN
     LET atc2 == ArithSemantics(wit,[A |-> aic.A.A2, stackSize |-> atc1.stackSize]) IN
     [isIntNaN |-> atc1.isIntNaN \/ atc2.isIntNaN,
      int |-> atc1.int + atc2.int,
      stackSize |-> atc2.stackSize - 1]
  [] /\ aic.A.type = "Arith_sub" ->
     LET atc1 == ArithSemantics(wit,[A |-> aic.A.A1, stackSize |-> aic.stackSize]) IN
     LET atc2 == ArithSemantics(wit,[A |-> aic.A.A2, stackSize |-> atc1.stackSize]) IN
     [isIntNaN |-> atc1.isIntNaN \/ atc2.isIntNaN,
      int |-> atc1.int - atc2.int,
      stackSize |-> atc2.stackSize - 1]
  [] /\ aic.A.type = "Arith_max" ->
     LET atc1 == ArithSemantics(wit,[A |-> aic.A.A1, stackSize |-> aic.stackSize]) IN
     LET atc2 == ArithSemantics(wit,[A |-> aic.A.A2, stackSize |-> atc1.stackSize]) IN
     [isIntNaN |-> atc1.isIntNaN \/ atc2.isIntNaN,
      int |-> max(atc1.int,atc2.int),
      stackSize |-> atc2.stackSize - 1]
  [] /\ aic.A.type = "Arith_min" ->
     LET atc1 == ArithSemantics(wit,[A |-> aic.A.A1, stackSize |-> aic.stackSize]) IN
     LET atc2 == ArithSemantics(wit,[A |-> aic.A.A2, stackSize |-> atc1.stackSize]) IN
     [isIntNaN |-> atc1.isIntNaN \/ atc2.isIntNaN,
      int |-> min(atc1.int,atc2.int),
      stackSize |-> atc2.stackSize - 1]

checksig(serializedTx,txInIdx,serializedPrevTx,sig,pubKey) ==
\/ sig.type = "CryptoObj_Sig71"
   /\ sig = Sig71(sig.actorIdx,sig.idx,serializedTx,txInIdx,serializedPrevTx)
   /\ pubKey = PubKey33(sig.actorIdx,sig.idx)
\/ sig.type = "CryptoObj_Sig72"
   /\ sig = Sig72(sig.actorIdx,sig.idx,serializedTx,txInIdx,serializedPrevTx)
   /\ pubKey = PubKey33(sig.actorIdx,sig.idx)

checkmultisig00(serializedTx,txInIdx,serializedPrevTx,sig,pubKey) ==
TRUE

checkmultisig01(serializedTx,txInIdx,serializedPrevTx,sig,pubKey) ==
TRUE

checkmultisig02(serializedTx,txInIdx,serializedPrevTx,sig,pubKey) ==
TRUE

checkmultisig10(serializedTx,txInIdx,serializedPrevTx,sig,pubKey) ==
FALSE

checkmultisig11(serializedTx,txInIdx,serializedPrevTx,sig,pubKey) ==
IF checksig(serializedTx,txInIdx,serializedPrevTx,sig[1],pubKey[1]) THEN
checkmultisig00(serializedTx,txInIdx,serializedPrevTx,sig,pubKey)
ELSE
checkmultisig10(serializedTx,txInIdx,serializedPrevTx,sig,pubKey)

checkmultisig12(serializedTx,txInIdx,serializedPrevTx,sig,pubKey) ==
IF checksig(serializedTx,txInIdx,serializedPrevTx,sig[1],pubKey[2]) THEN
checkmultisig01(serializedTx,txInIdx,serializedPrevTx,sig,pubKey)
ELSE
checkmultisig11(serializedTx,txInIdx,serializedPrevTx,sig,pubKey)

checkmultisig21(serializedTx,txInIdx,serializedPrevTx,sig,pubKey) ==
FALSE

checkmultisig22(serializedTx,txInIdx,serializedPrevTx,sig,pubKey) ==
IF checksig(serializedTx,txInIdx,serializedPrevTx,sig[2],pubKey[2]) THEN
checkmultisig11(serializedTx,txInIdx,serializedPrevTx,sig,pubKey)
ELSE
checkmultisig21(serializedTx,txInIdx,serializedPrevTx,sig,pubKey)

PredSemantics(wit,serializedTx,txInIdx,serializedPrevTx,ageLock,heightLock,pic) ==
CASE /\ pic.P.type = "Pred_and" ->
     LET ptc1 == PredSemantics(wit,serializedTx,txInIdx,serializedPrevTx,ageLock,heightLock,[P |-> pic.P.P1, stackSize |-> pic.stackSize]) IN
     LET ptc2 == PredSemantics(wit,serializedTx,txInIdx,serializedPrevTx,ageLock,heightLock,[P |-> pic.P.P2, stackSize |-> ptc1.stackSize]) IN
     [bool |-> ptc1.bool /\ ptc2.bool,
      stackSize |-> ptc2.stackSize]
  [] /\ pic.P.type = "Pred_eq" ->
     LET atc1 == ArithSemantics(wit,[A |-> pic.P.A1, stackSize |-> pic.stackSize]) IN
     LET atc2 == ArithSemantics(wit,[A |-> pic.P.A2, stackSize |-> atc1.stackSize]) IN
     [bool |-> ~atc1.isIntNaN /\ ~atc2.isIntNaN /\ atc1.int = atc2.int,
      stackSize |-> atc2.stackSize - 2]
  [] /\ pic.P.type = "Pred_neq" ->
     LET atc1 == ArithSemantics(wit,[A |-> pic.P.A1, stackSize |-> pic.stackSize]) IN
     LET atc2 == ArithSemantics(wit,[A |-> pic.P.A2, stackSize |-> atc1.stackSize]) IN
     [bool |-> ~atc1.isIntNaN /\ ~atc2.isIntNaN /\ atc1.int # atc2.int,
      stackSize |-> atc2.stackSize - 2]
  [] /\ pic.P.type = "Pred_lt" ->
     LET atc1 == ArithSemantics(wit,[A |-> pic.P.A1, stackSize |-> pic.stackSize]) IN
     LET atc2 == ArithSemantics(wit,[A |-> pic.P.A2, stackSize |-> atc1.stackSize]) IN
     [bool |-> ~atc1.isIntNaN /\ ~atc2.isIntNaN /\ atc1.int < atc2.int,
      stackSize |-> atc2.stackSize - 2]
  [] /\ pic.P.type = "Pred_gt" ->
     LET atc1 == ArithSemantics(wit,[A |-> pic.P.A1, stackSize |-> pic.stackSize]) IN
     LET atc2 == ArithSemantics(wit,[A |-> pic.P.A2, stackSize |-> atc1.stackSize]) IN
     [bool |-> ~atc1.isIntNaN /\ ~atc2.isIntNaN /\ atc1.int > atc2.int,
      stackSize |-> atc2.stackSize - 2]
  [] /\ pic.P.type = "Pred_lte" ->
     LET atc1 == ArithSemantics(wit,[A |-> pic.P.A1, stackSize |-> pic.stackSize]) IN
     LET atc2 == ArithSemantics(wit,[A |-> pic.P.A2, stackSize |-> atc1.stackSize]) IN
     [bool |-> ~atc1.isIntNaN /\ ~atc2.isIntNaN /\ atc1.int <= atc2.int,
      stackSize |-> atc2.stackSize - 2]
  [] /\ pic.P.type = "Pred_gte" ->
     LET atc1 == ArithSemantics(wit,[A |-> pic.P.A1, stackSize |-> pic.stackSize]) IN
     LET atc2 == ArithSemantics(wit,[A |-> pic.P.A2, stackSize |-> atc1.stackSize]) IN
     [bool |-> ~atc1.isIntNaN /\ ~atc2.isIntNaN /\ atc1.int >= atc2.int,
      stackSize |-> atc2.stackSize - 2]
  [] /\ pic.P.type = "Pred_eq_hash20_wit"
     /\ TRUE
        /\ pic.P.i < Len(wit)
        /\ pic.stackSize <=  998 -> [bool |-> Hash20(wit[pic.P.i + 1]) = pic.P.C,
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_eq_hash20_wit"
     /\ FALSE
        \/ pic.P.i >= Len(wit)
        \/ pic.stackSize >=  999 -> [bool |-> FALSE,
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checksig_wit"
     /\ TRUE
        /\ pic.P.i < Len(wit)
        /\ pic.stackSize <=  998 -> [bool |-> checksig(serializedTx,txInIdx,serializedPrevTx,wit[pic.P.i + 1],pic.P.C),
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checksig_wit"
     /\ FALSE
        \/ pic.P.i >= Len(wit)
        \/ pic.stackSize >=  999 -> [bool |-> FALSE,
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig00_wits"
     /\ TRUE
        /\ pic.stackSize <=  997 -> [bool |-> checkmultisig00(serializedTx,txInIdx,serializedPrevTx,<<>>,<<>>),
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig00_wits"
     /\ FALSE
        \/ pic.stackSize >=  998 -> [bool |-> FALSE,
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig01_wits"
     /\ TRUE
        /\ pic.stackSize <=  996 -> [bool |-> checkmultisig01(serializedTx,txInIdx,serializedPrevTx,<<>>,<<pic.P.C1>>),
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig01_wits"
     /\ FALSE
        \/ pic.stackSize >=  997 -> [bool |-> FALSE,
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig02_wits"
     /\ TRUE
        /\ pic.stackSize <=  995 -> [bool |-> checkmultisig02(serializedTx,txInIdx,serializedPrevTx,<<>>,<<pic.P.C1,pic.P.C2>>),
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig02_wits"
     /\ FALSE
        \/ pic.stackSize >=  996 -> [bool |-> FALSE,
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig11_wits"
     /\ TRUE
        /\ pic.P.i0 < Len(wit)
        /\ pic.stackSize <=  995 -> [bool |-> checkmultisig11(serializedTx,txInIdx,serializedPrevTx,<<wit[pic.P.i0 + 1]>>,<<pic.P.C1>>),
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig11_wits"
     /\ FALSE
        \/ pic.P.i0 >= Len(wit)
        \/ pic.stackSize >=  996 -> [bool |-> FALSE,
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig12_wits"
     /\ TRUE
        /\ pic.P.i0 < Len(wit)
        /\ pic.stackSize <=  994 -> [bool |-> checkmultisig12(serializedTx,txInIdx,serializedPrevTx,<<wit[pic.P.i0 + 1]>>,<<pic.P.C1,pic.P.C2>>),
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig12_wits"
     /\ FALSE
        \/ pic.P.i0 >= Len(wit)
        \/ pic.stackSize >=  995 -> [bool |-> FALSE,
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig22_wits"
     /\ TRUE
        /\ pic.P.i0 < Len(wit)
        /\ pic.P.i1 < Len(wit)
        /\ pic.stackSize <=  993 -> [bool |-> checkmultisig22(serializedTx,txInIdx,serializedPrevTx,<<wit[pic.P.i0 + 1],wit[pic.P.i1 + 1]>>,<<pic.P.C1,pic.P.C2>>),
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig22_wits"
     /\ FALSE
        \/ pic.P.i0 >= Len(wit)
        \/ pic.P.i1 >= Len(wit)
        \/ pic.stackSize >=  994 -> [bool |-> FALSE,
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_gte_ageLock"
     /\ TRUE
        /\ pic.stackSize <=  999 -> [bool |-> ageLock >= pic.P.minAge,
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_gte_ageLock"
     /\ FALSE
        \/ pic.stackSize >= 1000 -> [bool |-> FALSE,
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_gte_heightLock"
     /\ TRUE
        /\ pic.stackSize <=  999 -> [bool |-> heightLock >= pic.P.minHeight,
                                     stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_gte_heightLock"
     /\ FALSE
        \/ pic.stackSize >= 1000 -> [bool |-> FALSE,
                                     stackSize |-> pic.stackSize]

=============================================================================
\* Modification History
\* Last modified Sat Jan 14 02:56:47 JST 2023 by azon
\* Created Sun Nov 06 10:12:57 JST 2022 by azon
