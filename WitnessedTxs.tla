---------------------------- MODULE WitnessedTxs ----------------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE CryptoObjs
LOCAL INSTANCE Txs

RECURSIVE IsSeq_of_CryptoObj(_), Bigcup_Singleton(_), IsSeq_of_WitnessedTxIn(_), Bigcup_Wit_for_WitnessedTxIn(_)

IsSeq_of_CryptoObj(seq) ==
IF Len(seq) = 0 THEN TRUE ELSE
/\ IsCryptoObj(Head(seq))
/\ IsSeq_of_CryptoObj(Tail(seq))

IsWitnessedTxIn(witnessedTxIn) ==
/\ IsCryptoObj(witnessedTxIn.prevTxID)
/\ nBytes_for_CryptoObj(witnessedTxIn.prevTxID) = 32
/\ witnessedTxIn.prevTxOutIdx \in 0..16
/\ witnessedTxIn.prevTxOutPredIdx \in 0..16
/\ witnessedTxIn.nWit \in 0..83
/\ Len(witnessedTxIn.wit) = witnessedTxIn.nWit
/\ IsSeq_of_CryptoObj(witnessedTxIn.wit)
/\ witnessedTxIn.ageLock \in 0..65535
/\ witnessedTxIn.ageLock % 144 = 0

Bigcup_Singleton(seq) ==
IF Len(seq) = 0 THEN {} ELSE
     {Head(seq)}
\cup Bigcup_Singleton(Tail(seq))

Wit_for_WitnessedTxIn(witnessedTxIn) ==
Bigcup_Singleton(witnessedTxIn.wit)

unwitnessed_for_WitnessedTxIn(witnessedTxIn) ==
[prevTxID |-> witnessedTxIn.prevTxID,
 prevTxOutIdx |-> witnessedTxIn.prevTxOutIdx,
 ageLock |-> witnessedTxIn.ageLock]

IsSeq_of_WitnessedTxIn(seq) ==
IF Len(seq) = 0 THEN TRUE ELSE
/\ IsWitnessedTxIn(Head(seq))
/\ IsSeq_of_WitnessedTxIn(Tail(seq))

IsWitnessedTx(witnessedTx) ==
/\ witnessedTx.nTxIn \in 1..17
/\ Len(witnessedTx.txIn) = witnessedTx.nTxIn
/\ IsSeq_of_WitnessedTxIn(witnessedTx.txIn)
/\ witnessedTx.nTxOut \in 1..17
/\ Len(witnessedTx.txOut) = witnessedTx.nTxOut
/\ IsSeq_of_TxOut(witnessedTx.txOut)
/\ witnessedTx.heightLock \in 0..49999999
/\ witnessedTx.heightLock % 144 = 0

Bigcup_Wit_for_WitnessedTxIn(seq) ==
IF Len(seq) = 0 THEN {} ELSE
     Wit_for_WitnessedTxIn(Head(seq))
\cup Bigcup_Wit_for_WitnessedTxIn(Tail(seq))

Wit_for_WitnessedTx(witnessedTx) ==
Bigcup_Wit_for_WitnessedTxIn(witnessedTx.txIn)

unwitnessed_for_WitnessedTx(witnessedTx) ==
[nTxIn |-> witnessedTx.nTxIn,
 txIn |-> [k \in 1..witnessedTx.nTxIn |-> unwitnessed_for_WitnessedTxIn(witnessedTx.txIn[k])],
 nTxOut |-> witnessedTx.nTxOut,
 txOut |-> witnessedTx.txOut,
 heightLock |-> witnessedTx.heightLock]

=============================================================================
\* Modification History
\* Last modified Wed Dec 28 01:37:48 JST 2022 by azon
\* Created Fri Nov 04 06:39:50 JST 2022 by azon
