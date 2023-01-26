------------------------------- MODULE States -------------------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE CryptoObjs
LOCAL INSTANCE Txs
LOCAL INSTANCE WitnessedTxs
LOCAL INSTANCE ScriptSemantics

RECURSIVE IsKnownCryptoObj_a(_,_,_,_), IsSeq_of_KnownCryptoObj_a(_,_,_,_), IsSeq_of_WellKnownCoin_a(_,_,_,_,_,_), IsSeq_of_UnspentExecPath(_,_,_,_,_,_), HasValidWitness(_,_,_,_,_,_,_), HasValidTimelock(_,_,_,_,_,_,_,_), confirm(_,_,_,_,_)

IsKnownCryptoObj_a(BK_a,a,KnownSerializedTx_a,C) ==
\/ C \in BK_a
\/ CASE C.type = "CryptoObj_Rand"      -> /\ C.actorIdx = a
                                          /\ C.nBytes \in 20..80
                                          /\ C.idx \in Nat
     [] C.type = "CryptoObj_PrivKey32" -> /\ C.actorIdx = a
                                          /\ C.idx \in Nat
     [] C.type = "CryptoObj_PubKey33"  -> /\ IsKnownCryptoObj_a(BK_a,a,KnownSerializedTx_a,PrivKey32(C.actorIdx,C.idx))
     [] C.type = "CryptoObj_Sig71"     -> /\ IsKnownCryptoObj_a(BK_a,a,KnownSerializedTx_a,PrivKey32(C.actorIdx,C.idx))
                                          /\ C.serializedTx \in KnownSerializedTx_a
                                          /\ C.txInIdx \in 0..16
                                          /\ C.serializedPrevTx \in KnownSerializedTx_a
     [] C.type = "CryptoObj_Sig72"     -> /\ IsKnownCryptoObj_a(BK_a,a,KnownSerializedTx_a,PrivKey32(C.actorIdx,C.idx))
                                          /\ C.serializedTx \in KnownSerializedTx_a
                                          /\ C.txInIdx \in 0..16
                                          /\ C.serializedPrevTx \in KnownSerializedTx_a
     [] C.type = "CryptoObj_TxID"      -> /\ C.serializedTx \in KnownSerializedTx_a
     [] C.type = "CryptoObj_Hash20"    -> /\ IsKnownCryptoObj_a(BK_a,a,KnownSerializedTx_a,C.C)
     [] OTHER                          -> /\ FALSE

initBK_a(serialized,InitTx) ==
UNION {Arg_for_Tx(initTx) : initTx \in InitTx}

initKnownSerializedTx_a(serialized,InitTx) ==
UNION {{serialized[initTx]} : initTx \in InitTx}

initCoin(serialized,InitTx) ==
UNION {{<<TxID(serialized[initTx]),k>> : k \in 0..(initTx.nTxOut - 1)} : initTx \in InitTx}

initConfirmedCoin(serialized,InitTx) ==
UNION {{<<TxID(serialized[initTx]),k>> : k \in 0..(initTx.nTxOut - 1)} : initTx \in InitTx}

initSpentCoin(serialized,InitTx) ==
UNION {{} : initTx \in InitTx}

IsSeq_of_KnownCryptoObj_a(BK_a,a,KnownSerializedTx_a,seq) ==
IF Len(seq) = 0 THEN TRUE ELSE
/\ IsKnownCryptoObj_a(BK_a,a,KnownSerializedTx_a,Head(seq))
/\ IsSeq_of_KnownCryptoObj_a(BK_a,a,KnownSerializedTx_a,Tail(seq))

creatable(BK_a,a,KnownSerializedTx_a,tx) ==
/\ IsSeq_of_KnownCryptoObj_a(BK_a,a,KnownSerializedTx_a,[k \in 1..tx.nTxIn |-> tx.txIn[k].prevTxID])
/\ FALSE \notin {IsKnownCryptoObj_a(BK_a,a,KnownSerializedTx_a,C) : C \in Arg_for_Tx(tx)}

IsSeq_of_WellKnownCoin_a(unserialized,BK_a,a,KnownSerializedTx_a,seq1,seq2) ==
IF Len(seq1) = 0 THEN TRUE ELSE
/\ Head(seq1).type = "CryptoObj_TxID"
/\ Head(seq1).serializedTx \in KnownSerializedTx_a
/\ Head(seq2) \in 0..(unserialized[Head(seq1).serializedTx].nTxOut - 1)
/\ IsSeq_of_WellKnownCoin_a(unserialized,BK_a,a,KnownSerializedTx_a,Tail(seq1),Tail(seq2))

sendable(unserialized,BK_a,a,KnownSerializedTx_a,witnessedTx) ==
/\ IsSeq_of_WellKnownCoin_a(unserialized,BK_a,a,KnownSerializedTx_a,[k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxID],
                                                                    [k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxOutIdx])
/\ FALSE \notin {IsKnownCryptoObj_a(BK_a,a,KnownSerializedTx_a,C) : C \in Wit_for_WitnessedTx(witnessedTx)}
/\ FALSE \notin {IsKnownCryptoObj_a(BK_a,a,KnownSerializedTx_a,C) : C \in Arg_for_Tx(witnessedTx)}

IsSeq_of_UnspentExecPath(unserialized,Coin,SpentCoin,seq1,seq2,seq3) ==
IF Len(seq1) = 0 THEN TRUE ELSE
/\ Head(seq1).type = "CryptoObj_TxID"
/\ <<Head(seq1),Head(seq2)>> \in Coin \ SpentCoin
/\ Head(seq2) \in 0..(unserialized[Head(seq1).serializedTx].nTxOut - 1)
/\ Head(seq3) \in 0..(unserialized[Head(seq1).serializedTx].txOut[Head(seq2) + 1].nPred - 1)
/\ IsSeq_of_UnspentExecPath(unserialized,Coin,SpentCoin,Tail(seq1),Tail(seq2),Tail(seq3))

HasValidWitness(unserialized,serialized,seq1,seq2,seq3,witnessedTx,k) ==
IF k = witnessedTx.nTxIn THEN TRUE ELSE
/\ witnessedTx.txIn[k + 1].nWit = unserialized[Head(seq1).serializedTx].txOut[Head(seq2) + 1].nWit[Head(seq3) + 1]
/\ PredSemantics(witnessedTx.txIn[k + 1].wit,
                 serialized[unwitnessed_for_WitnessedTx(witnessedTx)],
                 k,
                 Head(seq1).serializedTx,
                 witnessedTx.txIn[k + 1].ageLock,
                 witnessedTx.heightLock,
                 [P |-> unserialized[Head(seq1).serializedTx].txOut[Head(seq2) + 1].pred[Head(seq3) + 1],
                  stackSize |-> witnessedTx.txIn[k + 1].nWit])
               = [bool |-> TRUE,
                  stackSize |-> witnessedTx.txIn[k + 1].nWit]
/\ HasValidWitness(unserialized,serialized,Tail(seq1),Tail(seq2),Tail(seq3),witnessedTx,k + 1)

HasValidTimelock(unserialized,age,height,seq1,seq2,seq3,witnessedTx,k) ==
IF k = witnessedTx.nTxIn THEN TRUE ELSE
/\ witnessedTx.txIn[k + 1].ageLock <= age[<<Head(seq1),Head(seq2)>>]
/\ witnessedTx.heightLock <= height
/\ HasValidTimelock(unserialized,age,height,Tail(seq1),Tail(seq2),Tail(seq3),witnessedTx,k + 1)

receivable(unserialized,serialized,Coin,SpentCoin,age,height,witnessedTx) ==
/\ IsSeq_of_UnspentExecPath(unserialized,Coin,SpentCoin,[k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxID],
                                                        [k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxOutIdx],
                                                        [k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxOutPredIdx])
/\ HasValidWitness(unserialized,serialized,[k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxID],
                                           [k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxOutIdx],
                                           [k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxOutPredIdx],witnessedTx,0)
/\ HasValidTimelock(unserialized,age,height,[k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxID],
                                            [k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxOutIdx],
                                            [k \in 1..witnessedTx.nTxIn |-> witnessedTx.txIn[k].prevTxOutPredIdx],witnessedTx,0)

confirm(serialized,CCoin,SCoin,tx,k) ==
IF k = tx.nTxIn THEN TRUE ELSE
/\ <<tx.txIn[k + 1].prevTxID,tx.txIn[k + 1].prevTxOutIdx>> \in CCoin \ SCoin
/\ confirm(serialized,CCoin,SCoin \cup {<<tx.txIn[k + 1].prevTxID,tx.txIn[k + 1].prevTxOutIdx>>},tx,k + 1)

confirmable(serialized,ConfirmedCoin,SpentCoin,tx) ==
confirm(serialized,ConfirmedCoin,SpentCoin,tx,0)

=============================================================================
\* Modification History
\* Last modified Wed Dec 28 01:41:05 JST 2022 by azon
\* Created Fri Nov 11 20:40:10 JST 2022 by azon
