------------------------------- MODULE Cheats -------------------------------

LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE CryptoObjs
LOCAL INSTANCE Scripts
LOCAL INSTANCE Txs
LOCAL INSTANCE WitnessedTxs
LOCAL INSTANCE States

RECURSIVE IsKnownCryptoObj_a_cheated(_,_,_,_), IsSeq_of_KnownCryptoObj_a_cheated(_,_,_,_), IsSeq_of_WitnessedTxIn_cheated(_), IsSeq_of_WellKnownCoin_a_cheated(_,_,_,_,_,_), PredSemantics_cheated(_,_,_,_,_,_,_,_,_), HasValidWitness_cheated(_,_,_,_,_,_,_,_,_,_), AWitnessedTxIn(_,_,_,_,_), Sum_of_Set(_)

IsKnownCryptoObj_a_cheated(BK,SubActor,KnownSerializedTx,C) ==
\/ C \in UNION {BK[a] : a \in SubActor}
\/ CASE C.type = "CryptoObj_Rand"      -> /\ C.actorIdx \in SubActor
                                          /\ C.nBytes \in 20..80
                                          /\ C.idx \in Nat
     [] C.type = "CryptoObj_PrivKey32" -> /\ C.actorIdx \in SubActor
                                          /\ C.idx \in Nat
     [] C.type = "CryptoObj_PubKey33"  -> /\ IsKnownCryptoObj_a_cheated(BK,SubActor,KnownSerializedTx,PrivKey32(C.actorIdx,C.idx))
     [] C.type = "CryptoObj_Sig71"     -> /\ IsKnownCryptoObj_a_cheated(BK,SubActor,KnownSerializedTx,PrivKey32(C.actorIdx,C.idx))
                                          /\ C.serializedTx \in UNION {KnownSerializedTx[a] : a \in SubActor}
                                          /\ C.txInIdx \in 0..16
                                          /\ C.serializedPrevTx \in UNION {KnownSerializedTx[a] : a \in SubActor}
     [] C.type = "CryptoObj_Sig72"     -> /\ IsKnownCryptoObj_a_cheated(BK,SubActor,KnownSerializedTx,PrivKey32(C.actorIdx,C.idx))
                                          /\ C.serializedTx \in UNION {KnownSerializedTx[a] : a \in SubActor}
                                          /\ C.txInIdx \in 0..16
                                          /\ C.serializedPrevTx \in UNION {KnownSerializedTx[a] : a \in SubActor}
     [] C.type = "CryptoObj_TxID"      -> /\ C.serializedTx \in UNION {KnownSerializedTx[a] : a \in SubActor}
     [] C.type = "CryptoObj_Hash20"    -> /\ IsKnownCryptoObj_a_cheated(BK,SubActor,KnownSerializedTx,C.C)
     [] OTHER                          -> /\ FALSE

IsSeq_of_KnownCryptoObj_a_cheated(BK,SubActor,KnownSerializedTx,seq) ==
IF Len(seq) = 0 THEN TRUE ELSE
/\ IsKnownCryptoObj_a_cheated(BK,SubActor,KnownSerializedTx,Head(seq))
/\ IsSeq_of_KnownCryptoObj_a_cheated(BK,SubActor,KnownSerializedTx,Tail(seq))

creatable_cheated(BK,SubActor,KnownSerializedTx,tx) ==
/\ IsSeq_of_KnownCryptoObj_a_cheated(BK,SubActor,KnownSerializedTx,[k \in 1..tx.nTxIn |-> tx.txIn[k].prevTxID])
/\ FALSE \notin {IsKnownCryptoObj_a_cheated(BK,SubActor,KnownSerializedTx,C) : C \in Arg_for_Tx(tx)}

IsWitnessedTxIn_cheated(witnessedTxIn) ==
/\ IsCryptoObj(witnessedTxIn.prevTxID)
/\ nBytes_for_CryptoObj(witnessedTxIn.prevTxID) = 32
/\ witnessedTxIn.prevTxOutIdx \in 0..16
/\ witnessedTxIn.prevTxOutPredIdx \in 0..16
/\ witnessedTxIn.nWit \in 0..83
/\ Len(witnessedTxIn.wit) = 0
/\ IsSeq_of_CryptoObj(witnessedTxIn.wit)
/\ witnessedTxIn.ageLock \in 0..65535
/\ witnessedTxIn.ageLock % 144 = 0

IsSeq_of_WitnessedTxIn_cheated(seq) ==
IF Len(seq) = 0 THEN TRUE ELSE
/\ IsWitnessedTxIn_cheated(Head(seq))
/\ IsSeq_of_WitnessedTxIn_cheated(Tail(seq))

IsWitnessedTx_cheated(witnessedTx) ==
/\ witnessedTx.nTxIn \in 1..17
/\ Len(witnessedTx.txIn) = witnessedTx.nTxIn
/\ IsSeq_of_WitnessedTxIn_cheated(witnessedTx.txIn)
/\ witnessedTx.nTxOut \in 1..17
/\ Len(witnessedTx.txOut) = witnessedTx.nTxOut
/\ IsSeq_of_TxOut(witnessedTx.txOut)
/\ witnessedTx.heightLock \in 0..49999999
/\ witnessedTx.heightLock % 144 = 0

IsSeq_of_WellKnownCoin_a_cheated(unserialized,BK,SubActor,KnownSerializedTx,seq1,seq2) ==
IF Len(seq1) = 0 THEN TRUE ELSE
/\ Head(seq1).type = "CryptoObj_TxID"
/\ Head(seq1).serializedTx \in UNION {KnownSerializedTx[a] : a \in SubActor}
/\ Head(seq2) \in 0..(unserialized[Head(seq1).serializedTx].nTxOut - 1)
/\ IsSeq_of_WellKnownCoin_a_cheated(unserialized,BK,SubActor,KnownSerializedTx,Tail(seq1),Tail(seq2))

sendable_cheated(unserialized,BK,SubActor,KnownSerializedTx,witnessedTx) ==
/\ IsSeq_of_WellKnownCoin_a_cheated(unserialized,BK,SubActor,KnownSerializedTx,[k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxID],
                                                                               [k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxOutIdx])
/\ FALSE \notin {IsKnownCryptoObj_a_cheated(BK,SubActor,KnownSerializedTx,C) : C \in Wit_for_WitnessedTx(witnessedTx)}
/\ FALSE \notin {IsKnownCryptoObj_a_cheated(BK,SubActor,KnownSerializedTx,C) : C \in Arg_for_Tx(witnessedTx)}

checksig_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey) ==
\/ pubKey.type = "CryptoObj_PubKey33"
   /\ IsKnownCryptoObj_a_cheated(BK,SubActor,KnownSerializedTx,Sig71(pubKey.actorIdx,pubKey.idx,serializedTx,txInIdx,serializedPrevTx))
\/ pubKey.type = "CryptoObj_PubKey33"
   /\ IsKnownCryptoObj_a_cheated(BK,SubActor,KnownSerializedTx,Sig72(pubKey.actorIdx,pubKey.idx,serializedTx,txInIdx,serializedPrevTx))

checkmultisig00_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey) ==
TRUE

checkmultisig01_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey) ==
TRUE

checkmultisig02_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey) ==
TRUE

checkmultisig10_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey) ==
FALSE

checkmultisig11_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey) ==
IF checksig_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey[1]) THEN
checkmultisig00_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey)
ELSE
checkmultisig10_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey)

checkmultisig12_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey) ==
IF checksig_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey[2]) THEN
checkmultisig01_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey)
ELSE
checkmultisig11_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey)

checkmultisig21_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey) ==
FALSE

checkmultisig22_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey) ==
IF checksig_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey[2]) THEN
checkmultisig11_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey)
ELSE
checkmultisig21_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pubKey)

PredSemantics_cheated(BK,SubActor,KnownSerializedTx,serializedTx,txInIdx,serializedPrevTx,ageLock,heightLock,pic) ==
CASE /\ pic.P.type = "Pred_and" ->
     LET ptc1 == PredSemantics_cheated(BK,SubActor,KnownSerializedTx,serializedTx,txInIdx,serializedPrevTx,ageLock,heightLock,[P |-> pic.P.P1, stackSize |-> pic.stackSize]) IN
     LET ptc2 == PredSemantics_cheated(BK,SubActor,KnownSerializedTx,serializedTx,txInIdx,serializedPrevTx,ageLock,heightLock,[P |-> pic.P.P2, stackSize |-> ptc1.stackSize]) IN
     [bool |-> ptc1.bool /\ ptc2.bool,
      stackSize |-> ptc2.stackSize]
  [] /\ pic.P.type = "Pred_eq" ->
     [bool |-> TRUE,
      stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_neq" ->
     [bool |-> TRUE,
      stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_lt" ->
     [bool |-> TRUE,
      stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_gt" ->
     [bool |-> TRUE,
      stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_lte" ->
     [bool |-> TRUE,
      stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_gte" ->
     [bool |-> TRUE,
      stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_eq_hash20_wit"
     /\ TRUE
        /\ pic.stackSize <= 998 -> [bool |-> \/ pic.P.C.type = "CryptoObj_Hash20"
                                                /\ IsKnownCryptoObj_a_cheated(BK,SubActor,KnownSerializedTx,pic.P.C.C),
                                    stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_eq_hash20_wit"
     /\ FALSE
        \/ pic.stackSize >= 999 -> [bool |-> FALSE,
                                    stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checksig_wit"
     /\ TRUE
        /\ pic.stackSize <= 998 -> [bool |-> checksig_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,pic.P.C),
                                    stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checksig_wit"
     /\ FALSE
        \/ pic.stackSize >= 999 -> [bool |-> FALSE,
                                    stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig00_wits"
     /\ TRUE
        /\ pic.stackSize <= 997 -> [bool |-> checkmultisig00_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,<<>>),
                                    stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig00_wits"
     /\ FALSE
        \/ pic.stackSize >= 998 -> [bool |-> FALSE,
                                    stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig01_wits"
     /\ TRUE
        /\ pic.stackSize <= 996 -> [bool |-> checkmultisig01_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,<<pic.P.C1>>),
                                    stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig01_wits"
     /\ FALSE
        \/ pic.stackSize >= 997 -> [bool |-> FALSE,
                                    stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig02_wits"
     /\ TRUE
        /\ pic.stackSize <= 995 -> [bool |-> checkmultisig02_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,<<pic.P.C1,pic.P.C2>>),
                                    stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig02_wits"
     /\ FALSE
        \/ pic.stackSize >= 996 -> [bool |-> FALSE,
                                    stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig11_wits"
     /\ TRUE
        /\ pic.stackSize <= 995 -> [bool |-> checkmultisig11_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,<<pic.P.C1>>),
                                    stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig11_wits"
     /\ FALSE
        \/ pic.stackSize >= 996 -> [bool |-> FALSE,
                                    stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig12_wits"
     /\ TRUE
        /\ pic.stackSize <= 994 -> [bool |-> checkmultisig12_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,<<pic.P.C1,pic.P.C2>>),
                                    stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig12_wits"
     /\ FALSE
        \/ pic.stackSize >= 995 -> [bool |-> FALSE,
                                    stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig22_wits"
     /\ TRUE
        /\ pic.stackSize <= 993 -> [bool |-> checkmultisig22_cheated(serializedTx,txInIdx,serializedPrevTx,BK,SubActor,KnownSerializedTx,<<pic.P.C1,pic.P.C2>>),
                                    stackSize |-> pic.stackSize]
  [] /\ pic.P.type = "Pred_checkmultisig22_wits"
     /\ FALSE
        \/ pic.stackSize >= 994 -> [bool |-> FALSE,
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

HasValidWitness_cheated(unserialized,serialized,BK,SubActor,KnownSerializedTx,seq1,seq2,seq3,witnessedTx,k) ==
IF k = witnessedTx.nTxIn THEN TRUE ELSE
/\ witnessedTx.txIn[k + 1].nWit = unserialized[Head(seq1).serializedTx].txOut[Head(seq2) + 1].nWit[Head(seq3) + 1]
/\ PredSemantics_cheated(BK,
                         SubActor,
                         KnownSerializedTx,
                         serialized[unwitnessed_for_WitnessedTx(witnessedTx)],
                         k,
                         Head(seq1).serializedTx,
                         witnessedTx.txIn[k + 1].ageLock,
                         witnessedTx.heightLock,
                         [P |-> unserialized[Head(seq1).serializedTx].txOut[Head(seq2) + 1].pred[Head(seq3) + 1],
                          stackSize |-> witnessedTx.txIn[k + 1].nWit])
                       = [bool |-> TRUE,
                          stackSize |-> witnessedTx.txIn[k + 1].nWit]
/\ HasValidWitness_cheated(unserialized,serialized,BK,SubActor,KnownSerializedTx,Tail(seq1),Tail(seq2),Tail(seq3),witnessedTx,k + 1)

receivable_cheated(unserialized,serialized,BK,SubActor,KnownSerializedTx,Coin,SpentCoin,age,height,witnessedTx) ==
/\ IsSeq_of_UnspentExecPath(unserialized,Coin,SpentCoin,[k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxID],
                                                        [k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxOutIdx],
                                                        [k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxOutPredIdx])
/\ HasValidWitness_cheated(unserialized,serialized,BK,SubActor,KnownSerializedTx,[k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxID],
                                                                                 [k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxOutIdx],
                                                                                 [k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxOutPredIdx],witnessedTx,0)
/\ HasValidTimelock(unserialized,age,height,[k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxID],
                                            [k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxOutIdx],
                                            [k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxOutPredIdx],witnessedTx,0)

aTx(unserialized,a,age,height,coin) ==
[
  nTxIn |-> 1,
  txIn |-> <<[
    prevTxID |-> coin[1],
    prevTxOutIdx |-> coin[2],
    ageLock |-> age[coin]
  ]>>,
  nTxOut |-> 1,
  txOut |-> <<[
    value |-> unserialized[coin[1].serializedTx].txOut[coin[2] + 1].value,
    nPred |-> 1,
    nWit |-> <<
      1
    >>,
    pred |-> <<
      checksig_wit(0,PubKey33(a,0))
    >>
  ]>>,
  heightLock |-> height
]

AWitnessedTxIn(unserialized,aTx2,age,height,k) ==
IF aTx2.nTxIn = 1 THEN
{<<[
  prevTxID |-> aTx2.txIn[k].prevTxID,
  prevTxOutIdx |-> aTx2.txIn[k].prevTxOutIdx,
  prevTxOutPredIdx |-> l,
  nWit |-> unserialized[aTx2.txIn[k].prevTxID.serializedTx].txOut[aTx2.txIn[k].prevTxOutIdx + 1].nWit[l + 1],
  wit |-> <<>>,
  ageLock |-> aTx2.txIn[k].ageLock
]>> : l \in 0..(unserialized[aTx2.txIn[k].prevTxID.serializedTx].txOut[aTx2.txIn[k].prevTxOutIdx + 1].nPred - 1)}
ELSE IF k = aTx2.nTxIn THEN
{[
  prevTxID |-> aTx2.txIn[k].prevTxID,
  prevTxOutIdx |-> aTx2.txIn[k].prevTxOutIdx,
  prevTxOutPredIdx |-> l,
  nWit |-> unserialized[aTx2.txIn[k].prevTxID.serializedTx].txOut[aTx2.txIn[k].prevTxOutIdx + 1].nWit[l + 1],
  wit |-> <<>>,
  ageLock |-> aTx2.txIn[k].ageLock
] : l \in 0..(unserialized[aTx2.txIn[k].prevTxID.serializedTx].txOut[aTx2.txIn[k].prevTxOutIdx + 1].nPred - 1)}
ELSE
{[
  prevTxID |-> aTx2.txIn[k].prevTxID,
  prevTxOutIdx |-> aTx2.txIn[k].prevTxOutIdx,
  prevTxOutPredIdx |-> l,
  nWit |-> unserialized[aTx2.txIn[k].prevTxID.serializedTx].txOut[aTx2.txIn[k].prevTxOutIdx + 1].nWit[l + 1],
  wit |-> <<>>,
  ageLock |-> aTx2.txIn[k].ageLock
] : l \in 0..(unserialized[aTx2.txIn[k].prevTxID.serializedTx].txOut[aTx2.txIn[k].prevTxOutIdx + 1].nPred - 1)} \X AWitnessedTxIn(unserialized,aTx2,age,height,k + 1)

AWitnessedTx(unserialized2,aTx2,age,height) ==
{[
  nTxIn |-> aTx2.nTxIn,
  txIn |-> aWitnessedTxIn,
  nTxOut |-> aTx2.nTxOut,
  txOut |-> aTx2.txOut,
  heightLock |-> aTx2.heightLock
] : aWitnessedTxIn \in AWitnessedTxIn(unserialized2,aTx2,age,height,1)}

IsSpendable_cheated(unserialized,serialized,BK,SubActor,KnownSerializedTx,Coin,SpentCoin,age,height,coin) ==
IF SubActor = {} THEN FALSE ELSE
LET subActor == CHOOSE subActor \in SubActor : TRUE IN
LET subActorTx == aTx(unserialized,subActor,age,height,coin) IN
IF ~IsTx(subActorTx) \/ ~creatable_cheated(BK,SubActor,KnownSerializedTx,subActorTx) THEN FALSE ELSE
LET serialized2 == [
  x \in DOMAIN serialized
    \cup {subActorTx}
  |-> IF x \in DOMAIN serialized THEN serialized[x] ELSE
      Cardinality(DOMAIN serialized)
] IN
LET unserialized2 == [
  x \in DOMAIN unserialized
    \cup {serialized2[subActorTx]}
  |-> IF x \in DOMAIN unserialized THEN unserialized[x] ELSE
      subActorTx
] IN
LET KnownSerializedTx2 == [
  x \in DOMAIN KnownSerializedTx |-> KnownSerializedTx[x] \cup {serialized2[subActorTx]}
] IN
{witnessedTx \in AWitnessedTx(unserialized2,subActorTx,age,height) : /\ IsWitnessedTx_cheated(witnessedTx)
                                                                     /\ sendable_cheated(unserialized2,BK,SubActor,KnownSerializedTx2,witnessedTx)
                                                                     /\ receivable_cheated(unserialized2,serialized2,BK,SubActor,KnownSerializedTx2,Coin,SpentCoin,age,height,witnessedTx)} # {}

IsMine_cheated(unserialized,serialized,BK,Actor,a,KnownSerializedTx,Coin,SpentCoin,age,height,coin) ==
/\ IsSpendable_cheated(unserialized,serialized,BK,{a},KnownSerializedTx,Coin,SpentCoin,age,height,coin)
/\ ~IsSpendable_cheated(unserialized,serialized,BK,Actor \ {a},KnownSerializedTx,Coin,SpentCoin,age,height,coin)

Sum_of_Set(set) ==
IF set = {} THEN 0 ELSE
LET x == CHOOSE x \in set : TRUE IN
x + Sum_of_Set(set \ {x})

confirmedValue_cheated(unserialized,serialized,BK,Actor,a,KnownSerializedTx,Coin,ConfirmedCoin,SpentCoin,age,height) ==
Sum_of_Set({unserialized[coin[1].serializedTx].txOut[coin[2] + 1].value : coin \in {coin \in ConfirmedCoin \ SpentCoin : IsMine_cheated(unserialized,serialized,BK,Actor,a,KnownSerializedTx,Coin,SpentCoin,age,height,coin)}})

=============================================================================
\* Modification History
\* Last modified Sat Jan 14 11:38:34 JST 2023 by azon
\* Created Wed Nov 30 10:29:37 JST 2022 by azon
