----------------------------- MODULE CryptoObjs -----------------------------

LOCAL INSTANCE Naturals

RECURSIVE IsCryptoObj(_)

IsCryptoObj(C) ==
CASE C.type = "CryptoObj_Rand"      -> /\ C.actorIdx \in Nat
                                       /\ C.nBytes \in 20..80
                                       /\ C.idx \in Nat
  [] C.type = "CryptoObj_PrivKey32" -> /\ C.actorIdx \in Nat
                                       /\ C.idx \in Nat
  [] C.type = "CryptoObj_PubKey33"  -> /\ C.actorIdx \in Nat
                                       /\ C.idx \in Nat
  [] C.type = "CryptoObj_Sig71"     -> /\ C.actorIdx \in Nat
                                       /\ C.idx \in Nat
                                       /\ C.serializedTx \in Nat
                                       /\ C.txInIdx \in 0..16
                                       /\ C.serializedPrevTx \in Nat
  [] C.type = "CryptoObj_Sig72"     -> /\ C.actorIdx \in Nat
                                       /\ C.idx \in Nat
                                       /\ C.serializedTx \in Nat
                                       /\ C.txInIdx \in 0..16
                                       /\ C.serializedPrevTx \in Nat
  [] C.type = "CryptoObj_TxID"      -> /\ C.serializedTx \in Nat
  [] C.type = "CryptoObj_Hash20"    -> /\ IsCryptoObj(C.C)
  [] OTHER                          -> /\ FALSE

Rand(actorIdx,
     nBytes,
     idx) ==
[type |-> "CryptoObj_Rand", actorIdx |-> actorIdx,
                            nBytes |-> nBytes,
                            idx |-> idx]

PrivKey32(actorIdx,
          idx) ==
[type |-> "CryptoObj_PrivKey32", actorIdx |-> actorIdx,
                                 idx |-> idx]

PubKey33(actorIdx,
         idx) ==
[type |-> "CryptoObj_PubKey33", actorIdx |-> actorIdx,
                                idx |-> idx]

Sig71(actorIdx,
      idx,
      serializedTx,
      txInIdx,
      serializedPrevTx) ==
[type |-> "CryptoObj_Sig71", actorIdx |-> actorIdx,
                             idx |-> idx,
                             serializedTx |-> serializedTx,
                             txInIdx |-> txInIdx,
                             serializedPrevTx |-> serializedPrevTx]

Sig72(actorIdx,
      idx,
      serializedTx,
      txInIdx,
      serializedPrevTx) ==
[type |-> "CryptoObj_Sig72", actorIdx |-> actorIdx,
                             idx |-> idx,
                             serializedTx |-> serializedTx,
                             txInIdx |-> txInIdx,
                             serializedPrevTx |-> serializedPrevTx]

TxID(serializedTx) ==
[type |-> "CryptoObj_TxID", serializedTx |-> serializedTx]

Hash20(C) ==
[type |-> "CryptoObj_Hash20", C |-> C]

nBytes_for_CryptoObj(C) ==
CASE C.type = "CryptoObj_Rand"      -> C.nBytes
  [] C.type = "CryptoObj_PrivKey32" -> 32
  [] C.type = "CryptoObj_PubKey33"  -> 33
  [] C.type = "CryptoObj_Sig71"     -> 71
  [] C.type = "CryptoObj_Sig72"     -> 72
  [] C.type = "CryptoObj_TxID"      -> 32
  [] C.type = "CryptoObj_Hash20"    -> 20

=============================================================================
\* Modification History
\* Last modified Wed Dec 28 01:35:29 JST 2022 by azon
\* Created Thu Nov 03 08:10:56 JST 2022 by azon
