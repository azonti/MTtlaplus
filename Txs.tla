-------------------------------- MODULE Txs --------------------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE CryptoObjs
LOCAL INSTANCE Scripts

RECURSIVE IsSeq_of_0To83(_), IsSeq_of_Pred(_), Sum_eNBytes_for_Pred(_,_), Sum_eNOps_for_Pred(_,_), Bigcup_Arg_for_Pred(_), IsSeq_of_TxIn(_), IsSeq_of_TxOut(_), Bigcup_Arg_for_TxOut(_)

IsTxIn(txIn) ==
/\ IsCryptoObj(txIn.prevTxID)
/\ nBytes_for_CryptoObj(txIn.prevTxID) = 32
/\ txIn.prevTxOutIdx \in 0..16
/\ txIn.ageLock \in 0..65535
/\ txIn.ageLock % 144 = 0

IsSeq_of_0To83(seq) ==
IF Len(seq) = 0 THEN TRUE ELSE
/\ Head(seq) \in 0..83
/\ IsSeq_of_0To83(Tail(seq))

IsSeq_of_Pred(seq) ==
IF Len(seq) = 0 THEN TRUE ELSE
/\ IsPred(Head(seq))
/\ IsSeq_of_Pred(Tail(seq))

eNBytes_for_Pred(nWit,pred) ==
nWit + nBytes_for_Pred(nWit,pred)

Sum_eNBytes_for_Pred(seq1,seq2) ==
IF Len(seq1) = 0 THEN 0 ELSE
  eNBytes_for_Pred(Head(seq1),Head(seq2))
+ Sum_eNBytes_for_Pred(Tail(seq1),Tail(seq2))

scriptNBytes(txOut) ==
3 * txOut.nPred + 2 + Sum_eNBytes_for_Pred(txOut.nWit,txOut.pred)

eNOps_for_Pred(nWit,pred) ==
nWit + nOps_for_Pred(pred)

Sum_eNOps_for_Pred(seq1,seq2) ==
IF Len(seq1) = 0 THEN 0 ELSE
  eNOps_for_Pred(Head(seq1),Head(seq2))
+ Sum_eNOps_for_Pred(Tail(seq1),Tail(seq2))

scriptNOps(txOut) ==
3 * txOut.nPred + 1 + Sum_eNBytes_for_Pred(txOut.nWit,txOut.pred)

IsTxOut(txOut) ==
/\ txOut.value >= 330
/\ txOut.nPred \in 1..17
/\ Len(txOut.nWit) = txOut.nPred
/\ IsSeq_of_0To83(txOut.nWit)
/\ Len(txOut.pred) = txOut.nPred
/\ IsSeq_of_Pred(txOut.pred)
/\ scriptNBytes(txOut) <= 3600
/\ scriptNOps(txOut) <= 201

Bigcup_Arg_for_Pred(seq) ==
IF Len(seq) = 0 THEN {} ELSE
     Arg_for_Pred(Head(seq))
\cup Bigcup_Arg_for_Pred(Tail(seq))

Arg_for_TxOut(txOut) ==
Bigcup_Arg_for_Pred(txOut.pred)

IsSeq_of_TxIn(seq) ==
IF Len(seq) = 0 THEN TRUE ELSE
/\ IsTxIn(Head(seq))
/\ IsSeq_of_TxIn(Tail(seq))

IsSeq_of_TxOut(seq) ==
IF Len(seq) = 0 THEN TRUE ELSE
/\ IsTxOut(Head(seq))
/\ IsSeq_of_TxOut(Tail(seq))

IsTx(tx) ==
/\ tx.nTxIn \in 1..17
/\ Len(tx.txIn) = tx.nTxIn
/\ IsSeq_of_TxIn(tx.txIn)
/\ tx.nTxOut \in 1..17
/\ Len(tx.txOut) = tx.nTxOut
/\ IsSeq_of_TxOut(tx.txOut)
/\ tx.heightLock \in 0..49999999
/\ tx.heightLock % 144 = 0

Bigcup_Arg_for_TxOut(seq) ==
IF Len(seq) = 0 THEN {} ELSE
     Arg_for_TxOut(Head(seq))
\cup Bigcup_Arg_for_TxOut(Tail(seq))

Arg_for_Tx(tx) ==
Bigcup_Arg_for_TxOut(tx.txOut)

=============================================================================
\* Modification History
\* Last modified Wed Dec 28 01:36:48 JST 2022 by azon
\* Created Fri Nov 04 01:56:52 JST 2022 by azon
