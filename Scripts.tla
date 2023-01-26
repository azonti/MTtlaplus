------------------------------- MODULE Scripts ------------------------------

LOCAL INSTANCE Integers
LOCAL INSTANCE CryptoObjs

RECURSIVE IsArith(_), IsPred(_), Arg_for_Pred(_), nBytes_for_Arith(_,_), nBytes_for_Pred(_,_), nOps_for_Arith(_), nOps_for_Pred(_)

IsArith(A) ==
CASE A.type = "Arith_const"    -> /\ A.int \in -2147483647..2147483647
  [] A.type = "Arith_size_wit" -> /\ A.i \in 0..82
  [] A.type = "Arith_neg"      -> /\ IsArith(A.A)
  [] A.type = "Arith_abs"      -> /\ IsArith(A.A)
  [] A.type = "Arith_add"      -> /\ IsArith(A.A1)
                                  /\ IsArith(A.A2)
  [] A.type = "Arith_sub"      -> /\ IsArith(A.A1)
                                  /\ IsArith(A.A2)
  [] A.type = "Arith_min"      -> /\ IsArith(A.A1)
                                  /\ IsArith(A.A2)
  [] A.type = "Arith_max"      -> /\ IsArith(A.A1)
                                  /\ IsArith(A.A2)
  [] OTHER                     -> /\ FALSE

const(int) ==
[type |-> "Arith_const", int |-> int]

size_wit(i) ==
[type |-> "Arith_size_wit", i |-> i]

neg(A) ==
[type |-> "Arith_neg", A |-> A]

abs(A) ==
[type |-> "Arith_abs", A |-> A]

add(A1,
    A2) ==
[type |-> "Arith_add", A1 |-> A1,
                       A2 |-> A2]

sub(A1,
    A2) ==
[type |-> "Arith_sub", A1 |-> A1,
                       A2 |-> A2]

min(A1,
    A2) ==
[type |-> "Arith_min", A1 |-> A1,
                       A2 |-> A2]

max(A1,
    A2) ==
[type |-> "Arith_max", A1 |-> A1,
                       A2 |-> A2]

IsPred(P) ==
CASE P.type = "Pred_and"                  -> /\ IsPred(P.P1)
                                             /\ IsPred(P.P2)
  [] P.type = "Pred_eq"                   -> /\ IsArith(P.A1)
                                             /\ IsArith(P.A2)
  [] P.type = "Pred_neq"                  -> /\ IsArith(P.A1)
                                             /\ IsArith(P.A2)
  [] P.type = "Pred_lt"                   -> /\ IsArith(P.A1)
                                             /\ IsArith(P.A2)
  [] P.type = "Pred_gt"                   -> /\ IsArith(P.A1)
                                             /\ IsArith(P.A2)
  [] P.type = "Pred_lte"                  -> /\ IsArith(P.A1)
                                             /\ IsArith(P.A2)
  [] P.type = "Pred_gte"                  -> /\ IsArith(P.A1)
                                             /\ IsArith(P.A2)
  [] P.type = "Pred_eq_hash20_wit"        -> /\ P.i \in 0..82
                                             /\ IsCryptoObj(P.C)
  [] P.type = "Pred_checksig_wit"         -> /\ P.i \in 0..82
                                             /\ IsCryptoObj(P.C)
  [] P.type = "Pred_checkmultisig00_wits" -> /\ TRUE
  [] P.type = "Pred_checkmultisig01_wits" -> /\ TRUE
                                             /\ IsCryptoObj(P.C1)
  [] P.type = "Pred_checkmultisig02_wits" -> /\ TRUE
                                             /\ IsCryptoObj(P.C1)
                                             /\ IsCryptoObj(P.C2)
  [] P.type = "Pred_checkmultisig11_wits" -> /\ TRUE
                                             /\ P.i0 \in 0..82
                                             /\ IsCryptoObj(P.C1)
  [] P.type = "Pred_checkmultisig12_wits" -> /\ TRUE
                                             /\ P.i0 \in 0..82
                                             /\ IsCryptoObj(P.C1)
                                             /\ IsCryptoObj(P.C2)
  [] P.type = "Pred_checkmultisig22_wits" -> /\ TRUE
                                             /\ P.i0 \in 0..82
                                             /\ P.i1 \in 0..82
                                             /\ IsCryptoObj(P.C1)
                                             /\ IsCryptoObj(P.C2)
  [] P.type = "Pred_gte_ageLock"          -> /\ P.minAge \in 0..65535
                                             /\ P.minAge % 144 = 0
  [] P.type = "Pred_gte_heightLock"       -> /\ P.minHeight \in 0..49999999
                                             /\ P.minHeight % 144 = 0
  [] OTHER                                -> /\ FALSE

and(P1,
    P2) ==
[type |-> "Pred_and", P1 |-> P1,
                      P2 |-> P2]

eq(A1,
   A2) ==
[type |-> "Pred_eq", A1 |-> A1,
                     A2 |-> A2]

neq(A1,
    A2) ==
[type |-> "Pred_neq", A1 |-> A1,
                      A2 |-> A2]

lt(A1,
   A2) ==
[type |-> "Pred_lt", A1 |-> A1,
                     A2 |-> A2]

gt(A1,
   A2) ==
[type |-> "Pred_gt", A1 |-> A1,
                     A2 |-> A2]

lte(A1,
    A2) ==
[type |-> "Pred_lte", A1 |-> A1,
                      A2 |-> A2]

gte(A1,
    A2) ==
[type |-> "Pred_gte", A1 |-> A1,
                      A2 |-> A2]

eq_hash20_wit(i,
              C) ==
[type |-> "Pred_eq_hash20_wit", i |-> i,
                                C |-> C]

checksig_wit(i,
             C) ==
[type |-> "Pred_checksig_wit", i |-> i,
                               C |-> C]

checkmultisig00_wits(dummy) ==
[type |-> "Pred_checkmultisig00_wits"]

checkmultisig01_wits(dummy,
                     C1) ==
[type |-> "Pred_checkmultisig01_wits", C1 |-> C1]

checkmultisig02_wits(dummy,
                     C1,
                     C2) ==
[type |-> "Pred_checkmultisig02_wits", C1 |-> C1,
                                       C2 |-> C2]

checkmultisig11_wits(dummy,
                     i0,
                     C1) ==
[type |-> "Pred_checkmultisig11_wits", i0 |-> i0,
                                       C1 |-> C1]

checkmultisig12_wits(dummy,
                     i0,
                     C1,
                     C2) ==
[type |-> "Pred_checkmultisig12_wits", i0 |-> i0,
                                       C1 |-> C1,
                                       C2 |-> C2]

checkmultisig22_wits(dummy,
                     i0,
                     i1,
                     C1,
                     C2) ==
[type |-> "Pred_checkmultisig22_wits", i0 |-> i0,
                                       i1 |-> i1,
                                       C1 |-> C1,
                                       C2 |-> C2]

gte_ageLock(minAge) ==
[type |-> "Pred_gte_ageLock", minAge |-> minAge]

gte_heightLock(minHeight) ==
[type |-> "Pred_gte_heightLock", minHeight |-> minHeight]

eNBytes_for_Int(int) ==
CASE int \in -1..16                  -> 1
  [] int \in -127..127               -> 2
  [] int \in -32767..32767           -> 3
  [] int \in -8388607..8388607       -> 4
  [] int \in -2147483647..2147483647 -> 5

eNBytes_for_CryptoObj(C) ==
CASE nBytes_for_CryptoObj(C) <= 75 -> 1 + nBytes_for_CryptoObj(C)
  [] nBytes_for_CryptoObj(C) >= 76 -> 2 + nBytes_for_CryptoObj(C)

nBytes_for_Arith(nWit,A) ==
CASE A.type = "Arith_const"    -> eNBytes_for_Int(A.int)
  [] A.type = "Arith_size_wit" -> 5 + eNBytes_for_Int(nWit - A.i)
  [] A.type = "Arith_neg"      -> nBytes_for_Arith(nWit,A.A) + 1
  [] A.type = "Arith_abs"      -> nBytes_for_Arith(nWit,A.A) + 1
  [] A.type = "Arith_add"      -> nBytes_for_Arith(nWit,A.A1) + nBytes_for_Arith(nWit,A.A2) + 1
  [] A.type = "Arith_sub"      -> nBytes_for_Arith(nWit,A.A1) + nBytes_for_Arith(nWit,A.A2) + 1
  [] A.type = "Arith_min"      -> nBytes_for_Arith(nWit,A.A1) + nBytes_for_Arith(nWit,A.A2) + 1
  [] A.type = "Arith_max"      -> nBytes_for_Arith(nWit,A.A1) + nBytes_for_Arith(nWit,A.A2) + 1

nBytes_for_Pred(nWit,P) ==
CASE P.type = "Pred_and"                  -> nBytes_for_Pred(nWit,P.P1) + nBytes_for_Pred(nWit,P.P2)
  [] P.type = "Pred_eq"                   -> nBytes_for_Arith(nWit,P.A1) + nBytes_for_Arith(nWit,P.A2) + 1
  [] P.type = "Pred_neq"                  -> nBytes_for_Arith(nWit,P.A1) + nBytes_for_Arith(nWit,P.A2) + 2
  [] P.type = "Pred_lt"                   -> nBytes_for_Arith(nWit,P.A1) + nBytes_for_Arith(nWit,P.A2) + 2
  [] P.type = "Pred_gt"                   -> nBytes_for_Arith(nWit,P.A1) + nBytes_for_Arith(nWit,P.A2) + 2
  [] P.type = "Pred_lte"                  -> nBytes_for_Arith(nWit,P.A1) + nBytes_for_Arith(nWit,P.A2) + 2
  [] P.type = "Pred_gte"                  -> nBytes_for_Arith(nWit,P.A1) + nBytes_for_Arith(nWit,P.A2) + 2
  [] P.type = "Pred_eq_hash20_wit"        -> 5 + eNBytes_for_Int(nWit - P.i) + eNBytes_for_CryptoObj(P.C)
  [] P.type = "Pred_checksig_wit"         -> 4 + eNBytes_for_Int(nWit - P.i) + eNBytes_for_CryptoObj(P.C)
  [] P.type = "Pred_checkmultisig00_wits" ->  4
  [] P.type = "Pred_checkmultisig01_wits" ->  4                                                               + eNBytes_for_CryptoObj(P.C1)
  [] P.type = "Pred_checkmultisig02_wits" ->  4                                                               + eNBytes_for_CryptoObj(P.C1) + eNBytes_for_CryptoObj(P.C2)
  [] P.type = "Pred_checkmultisig11_wits" ->  7 + eNBytes_for_Int(nWit - P.i0)                                + eNBytes_for_CryptoObj(P.C1)
  [] P.type = "Pred_checkmultisig12_wits" ->  7 + eNBytes_for_Int(nWit - P.i0)                                + eNBytes_for_CryptoObj(P.C1) + eNBytes_for_CryptoObj(P.C2)
  [] P.type = "Pred_checkmultisig22_wits" -> 10 + eNBytes_for_Int(nWit - P.i0) + eNBytes_for_Int(nWit - P.i1) + eNBytes_for_CryptoObj(P.C1) + eNBytes_for_CryptoObj(P.C2)
  [] P.type = "Pred_gte_ageLock"          -> 1 + eNBytes_for_Int(P.minAge)
  [] P.type = "Pred_gte_heightLock"       -> 1 + eNBytes_for_Int(P.minHeight)

nOps_for_Arith(A) ==
CASE A.type = "Pred_const"    -> 0
  [] A.type = "Pred_size_wit" -> 5
  [] A.type = "Pred_neg"      -> nOps_for_Arith(A.A) + 1
  [] A.type = "Pred_abs"      -> nOps_for_Arith(A.A) + 1
  [] A.type = "Pred_add"      -> nOps_for_Arith(A.A1) + nOps_for_Arith(A.A2) + 1
  [] A.type = "Pred_sub"      -> nOps_for_Arith(A.A1) + nOps_for_Arith(A.A2) + 1
  [] A.type = "Pred_min"      -> nOps_for_Arith(A.A1) + nOps_for_Arith(A.A2) + 1
  [] A.type = "Pred_max"      -> nOps_for_Arith(A.A1) + nOps_for_Arith(A.A2) + 1

nOps_for_Pred(P) ==
CASE P.type = "Pred_and"                  -> nOps_for_Pred(P.P1) + nOps_for_Pred(P.P2)
  [] P.type = "Pred_eq"                   -> nOps_for_Arith(P.A1) + nOps_for_Arith(P.A2) + 1
  [] P.type = "Pred_neq"                  -> nOps_for_Arith(P.A1) + nOps_for_Arith(P.A2) + 2
  [] P.type = "Pred_lt"                   -> nOps_for_Arith(P.A1) + nOps_for_Arith(P.A2) + 2
  [] P.type = "Pred_gt"                   -> nOps_for_Arith(P.A1) + nOps_for_Arith(P.A2) + 2
  [] P.type = "Pred_lte"                  -> nOps_for_Arith(P.A1) + nOps_for_Arith(P.A2) + 2
  [] P.type = "Pred_gte"                  -> nOps_for_Arith(P.A1) + nOps_for_Arith(P.A2) + 2
  [] P.type = "Pred_eq_hash20_wit"        -> 5
  [] P.type = "Pred_checksig_wit"         -> 4
  [] P.type = "Pred_checkmultisig00_wits" -> 1
  [] P.type = "Pred_checkmultisig01_wits" -> 2
  [] P.type = "Pred_checkmultisig02_wits" -> 3
  [] P.type = "Pred_checkmultisig11_wits" -> 5
  [] P.type = "Pred_checkmultisig12_wits" -> 6
  [] P.type = "Pred_checkmultisig22_wits" -> 9
  [] P.type = "Pred_gte_ageLock"          -> 1
  [] P.type = "Pred_gte_heightLock"       -> 1

Arg_for_Pred(P) ==
CASE P.type = "Pred_and"                  -> Arg_for_Pred(P.P1) \cup Arg_for_Pred(P.P2)
  [] P.type = "Pred_eq"                   -> {}
  [] P.type = "Pred_neq"                  -> {}
  [] P.type = "Pred_lt"                   -> {}
  [] P.type = "Pred_gt"                   -> {}
  [] P.type = "Pred_lte"                  -> {}
  [] P.type = "Pred_gte"                  -> {}
  [] P.type = "Pred_eq_hash20_wit"        -> {P.C}
  [] P.type = "Pred_checksig_wit"         -> {P.C}
  [] P.type = "Pred_checkmultisig00_wits" -> {}
  [] P.type = "Pred_checkmultisig01_wits" -> {P.C1}
  [] P.type = "Pred_checkmultisig02_wits" -> {P.C1, P.C2}
  [] P.type = "Pred_checkmultisig11_wits" -> {P.C1}
  [] P.type = "Pred_checkmultisig12_wits" -> {P.C1, P.C2}
  [] P.type = "Pred_checkmultisig22_wits" -> {P.C1, P.C2}
  [] P.type = "Pred_gte_ageLock"          -> {}
  [] P.type = "Pred_gte_heightLock"       -> {}

=============================================================================
\* Modification History
\* Last modified Wed Dec 28 01:35:47 JST 2022 by azon
\* Created Thu Nov 03 08:26:58 JST 2022 by azon
