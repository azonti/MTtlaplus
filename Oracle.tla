------------------------------- MODULE Oracle -------------------------------

INSTANCE Integers
INSTANCE Sequences
INSTANCE FiniteSets
INSTANCE CryptoObjs
INSTANCE Scripts
INSTANCE Txs
INSTANCE WitnessedTxs
INSTANCE States
INSTANCE Cheats

CONSTANTS NULL, MAXHEIGHT

(* --algorithm oracle

variables depositor = 0,
          event = 1,
          oracle = 2,
          withdrawer = 3,
          network = 4,
          adversary = 5,
          Party = {depositor,oracle,withdrawer},
          ContractingParty = {depositor,withdrawer},
          FailedContractingParty \in SUBSET ContractingParty,
          eventHappened = FALSE,
          mailbox = [
            self \in Party |-> [from \in Party |-> <<>>]
          ],
          reachedFailablePoint = [
            self \in ContractingParty |-> FALSE
          ],

          depositorInitTx = [
            nTxIn |-> 1,
            txIn |-> <<[
              prevTxID |-> Rand(depositor,32,0),
              prevTxOutIdx |-> 0,
              ageLock |-> 0
            ]>>,
            nTxOut |-> 1,
            txOut |-> <<[
              value |-> 10000,
              nPred |-> 1,
              nWit |-> <<
                1
              >>,
              pred |-> <<
                checksig_wit(0,PubKey33(depositor,0))
              >>
            ]>>,
            heightLock |-> 0
          ],
          serialized = [
            tx \in {depositorInitTx} |-> CASE tx = depositorInitTx -> 0
          ],
          unserialized = [
            serializedTx \in {0} |-> CASE serializedTx = 0 -> depositorInitTx
          ],

          Actor = Party \cup {adversary},
          BK = [
            a \in Actor |-> initBK_a(serialized,{depositorInitTx})
          ],
          KnownSerializedTx = [
            a \in Actor |-> initKnownSerializedTx_a(serialized,{depositorInitTx})
          ],
          Coin = initCoin(serialized,{depositorInitTx}),
          ConfirmedCoin = initConfirmedCoin(serialized,{depositorInitTx}),
          SpentCoin = initSpentCoin(serialized,{depositorInitTx}),
          age = [
            coin \in Coin |-> CASE coin[1] = TxID(serialized[depositorInitTx]) -> 144
          ],
          height = 144;

define
  Safety == ~eventHappened
            => confirmedValue_cheated(unserialized,serialized,BK,Actor,withdrawer,KnownSerializedTx,Coin,ConfirmedCoin,SpentCoin,age,height)
             + confirmedValue_cheated(unserialized,serialized,BK,Actor,adversary,KnownSerializedTx,Coin,ConfirmedCoin,SpentCoin,age,height) <= 0
  Liveness == eventHappened
              ~> withdrawer \in FailedContractingParty
              \/ [](confirmedValue_cheated(unserialized,serialized,BK,Actor,withdrawer,KnownSerializedTx,Coin,ConfirmedCoin,SpentCoin,age,height) >= 10000)
end define;

macro SendCryptoObj(self,to,cryptoObj)
begin
  await /\ IsCryptoObj(cryptoObj)
        /\ IsKnownCryptoObj_a(BK[self],self,KnownSerializedTx[self],cryptoObj);

  mailbox[to][self] := mailbox[to][self] \o <<cryptoObj>>;

  BK[to] := BK[to] \cup {cryptoObj};
end macro;

macro CreateTx(self,tx)
begin
  await /\ IsTx(tx)
        /\ creatable(BK[self],self,KnownSerializedTx[self],tx);

  serialized := [
    x \in DOMAIN serialized
      \cup {tx}
    |-> IF x \in DOMAIN serialized THEN serialized[x] ELSE
        Cardinality(DOMAIN serialized)
  ];
  unserialized := [
    x \in DOMAIN unserialized
      \cup {serialized[tx]}
    |-> IF x \in DOMAIN unserialized THEN unserialized[x] ELSE
        tx
  ];

  KnownSerializedTx[self] := KnownSerializedTx[self] \cup {serialized[tx]};
end macro;

macro SendWitnessedTx(self,witnessedTx)
begin
  await /\ IsWitnessedTx(witnessedTx)
        /\ sendable(unserialized,BK[self],self,KnownSerializedTx[self],witnessedTx)
        /\ receivable(unserialized,serialized,Coin,SpentCoin,age,height,witnessedTx);

  serialized := [
    x \in DOMAIN serialized
      \cup {unwitnessed_for_WitnessedTx(witnessedTx)}
    |-> IF x \in DOMAIN serialized THEN serialized[x] ELSE
        Cardinality(DOMAIN serialized)
  ];
  unserialized := [
    x \in DOMAIN unserialized
      \cup {serialized[unwitnessed_for_WitnessedTx(witnessedTx)]}
    |-> IF x \in DOMAIN unserialized THEN unserialized[x] ELSE
        unwitnessed_for_WitnessedTx(witnessedTx)
  ];

  BK := [
    a \in Actor |-> BK[a] \cup Wit_for_WitnessedTx(witnessedTx) \cup Arg_for_Tx(witnessedTx)
  ];
  KnownSerializedTx := [
    a \in Actor |-> KnownSerializedTx[a] \cup {serialized[unwitnessed_for_WitnessedTx(witnessedTx)]}
  ];
  Coin := Coin \cup {<<TxID(serialized[unwitnessed_for_WitnessedTx(witnessedTx)]),k>> : k \in 0..(witnessedTx.nTxOut - 1)};
  age := [
    coin \in DOMAIN age
         \cup {<<TxID(serialized[unwitnessed_for_WitnessedTx(witnessedTx)]),k>> : k \in 0..(witnessedTx.nTxOut - 1)}
    |-> IF coin \in DOMAIN age THEN age[coin] ELSE
        0
  ];
end macro;

fair process Depositor = depositor
variables depositorTx = NULL, depositorWitnessedTx = NULL;
begin
  DepositorCreateTx:
    await /\ Len(mailbox[depositor][oracle]) >= 1
          /\ Len(mailbox[depositor][withdrawer]) >= 1;
    depositorTx := [
      nTxIn |-> 1,
      txIn |-> <<[
        prevTxID |-> TxID(serialized[depositorInitTx]),
        prevTxOutIdx |-> 0,
        ageLock |-> 0
      ]>>,
      nTxOut |-> 1,
      txOut |-> <<[
        value |-> 10000,
        nPred |-> 1,
        nWit |-> <<
          2
        >>,
        pred |-> <<
          and(
            eq_hash20_wit(0,mailbox[depositor][oracle][1]),
            checksig_wit(1,mailbox[depositor][withdrawer][1])
          )
        >>
      ]>>,
      heightLock |-> 0
    ];
    CreateTx(depositor,depositorTx);

  DepositorSendWitnessedTx:
    depositorWitnessedTx := [
      nTxIn |-> 1,
      txIn |-> <<[
        prevTxID |-> TxID(serialized[depositorInitTx]),
        prevTxOutIdx |-> 0,
        prevTxOutPredIdx |-> 0,
        nWit |-> 1,
        wit |-> <<
          Sig71(depositor,0,serialized[depositorTx],0,serialized[depositorInitTx])
        >>,
        ageLock |-> 0
      ]>>,
      nTxOut |-> 1,
      txOut |-> <<[
        value |-> 10000,
        nPred |-> 1,
        nWit |-> <<
          2
        >>,
        pred |-> <<
          and(
            eq_hash20_wit(0,mailbox[depositor][oracle][1]),
            checksig_wit(1,mailbox[depositor][withdrawer][1])
          )
        >>
      ]>>,
      heightLock |-> 0
    ];
    SendWitnessedTx(depositor,depositorWitnessedTx);

  DepositorWaitForNetworkToConfirmTx:
    await <<TxID(serialized[depositorTx]),0>> \in ConfirmedCoin;
    reachedFailablePoint[depositor] := TRUE;
end process;

process Event = event
begin
  EventHappen:
    eventHappened := TRUE;
end process;

fair process Oracle = oracle
begin
  OracleSendHashToDepositor:
    SendCryptoObj(oracle,depositor,Hash20(Rand(oracle,20,0)));

  OracleWaitForEventToHappen:
    await eventHappened = TRUE;

  OracleSendPreimageToWithdrawer:
    SendCryptoObj(oracle,withdrawer,Rand(oracle,20,0));
end process;

fair process Withdrawer = withdrawer
begin
  WithdrawerSendingPubKeyToDepositor:
    SendCryptoObj(withdrawer,depositor,PubKey33(withdrawer,0));
    reachedFailablePoint[withdrawer] := TRUE;
end process;

fair process Network = network
begin
  NetworkWorking:
    while TRUE do
      either
        with tx \in {tx \in {unserialized[coin[1].serializedTx] : coin \in Coin \ ConfirmedCoin} : confirmable(serialized,ConfirmedCoin,SpentCoin,tx)}; do
          ConfirmedCoin := ConfirmedCoin \cup {<<TxID(serialized[tx]),k>> : k \in 0..(tx.nTxOut - 1)};
          SpentCoin := SpentCoin \cup {<<tx.txIn[k + 1].prevTxID,tx.txIn[k + 1].prevTxOutIdx>> : k \in 0..(tx.nTxIn - 1)};
        end with;
      or
        await {tx \in {unserialized[coin[1].serializedTx] : coin \in Coin \ ConfirmedCoin} : confirmable(serialized,ConfirmedCoin,SpentCoin,tx)} = {};
        age := [coin \in DOMAIN age |-> age[coin] + 144];
        height := height + 144;
        await /\ ~ ENABLED Depositor
              /\ ~ ENABLED Oracle
              /\ ~ ENABLED Withdrawer;
        await height <= MAXHEIGHT;
      end either;
    end while;
end process;

process Adversary = adversary
variables AdversaryTx = NULL, AdversaryWitnessedTx = NULL;
begin
  AdversaryWorking:
    while TRUE do
      AdversaryTx := {tx \in {aTx(unserialized,
                              adversary,
                              age,
                              height,
                              coin) : coin \in {coin \in Coin \ SpentCoin : ~IsMine_cheated(unserialized,serialized,BK,Actor,adversary,KnownSerializedTx,Coin,SpentCoin,age,height,coin)}} \cup (DOMAIN serialized \ {unserialized[coin[1].serializedTx] : coin \in Coin})
                                    : /\ IsTx(tx)
                                      /\ creatable_cheated(BK,{adversary} \cup {p \in FailedContractingParty : reachedFailablePoint[p]},KnownSerializedTx,tx)};
      with adversaryTx \in AdversaryTx; do
        serialized := [
          x \in DOMAIN serialized
            \cup {adversaryTx}
          |-> IF x \in DOMAIN serialized THEN serialized[x] ELSE
              Cardinality(DOMAIN serialized)
        ];
        unserialized := [
          x \in DOMAIN unserialized
            \cup {serialized[adversaryTx]}
          |-> IF x \in DOMAIN unserialized THEN unserialized[x] ELSE
              adversaryTx
        ];
        KnownSerializedTx := [
          x \in DOMAIN KnownSerializedTx |-> KnownSerializedTx[x] \cup {serialized[adversaryTx]}
        ];
        AdversaryWitnessedTx := {witnessedTx \in AWitnessedTx(unserialized,
                                                              adversaryTx,
                                                              age,
                                                              height) : /\ IsWitnessedTx_cheated(witnessedTx)
                                                                        /\ sendable_cheated(unserialized,BK,{adversary} \cup {p \in FailedContractingParty : reachedFailablePoint[p]},KnownSerializedTx,witnessedTx)
                                                                        /\ receivable_cheated(unserialized,serialized,BK,{adversary} \cup {p \in FailedContractingParty : reachedFailablePoint[p]},KnownSerializedTx,Coin,SpentCoin,age,height,witnessedTx)};
        with adversaryWitnessedTx \in AdversaryWitnessedTx; do
          BK := [
            a \in Actor |-> BK[a] \cup Wit_for_WitnessedTx(adversaryWitnessedTx) \cup Arg_for_Tx(adversaryWitnessedTx)
          ];
          Coin := Coin \cup {<<TxID(serialized[unwitnessed_for_WitnessedTx(adversaryWitnessedTx)]),k>> : k \in 0..(adversaryWitnessedTx.nTxOut - 1)};
          age := [
            coin \in DOMAIN age
                 \cup {<<TxID(serialized[unwitnessed_for_WitnessedTx(adversaryWitnessedTx)]),k>> : k \in 0..(adversaryWitnessedTx.nTxOut - 1)}
            |-> IF coin \in DOMAIN age THEN age[coin] ELSE
                0
          ];
        end with;
      end with;
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "10b6e8e5" /\ chksum(tla) = "f5c1dc00")
VARIABLES depositor, event, oracle, withdrawer, network, adversary, Party, 
          ContractingParty, FailedContractingParty, eventHappened, mailbox, 
          reachedFailablePoint, depositorInitTx, serialized, unserialized, 
          Actor, BK, KnownSerializedTx, Coin, ConfirmedCoin, SpentCoin, age, 
          height, pc

(* define statement *)
Safety == ~eventHappened
          => confirmedValue_cheated(unserialized,serialized,BK,Actor,withdrawer,KnownSerializedTx,Coin,ConfirmedCoin,SpentCoin,age,height)
           + confirmedValue_cheated(unserialized,serialized,BK,Actor,adversary,KnownSerializedTx,Coin,ConfirmedCoin,SpentCoin,age,height) <= 0
Liveness == eventHappened
            ~> withdrawer \in FailedContractingParty
            \/ [](confirmedValue_cheated(unserialized,serialized,BK,Actor,withdrawer,KnownSerializedTx,Coin,ConfirmedCoin,SpentCoin,age,height) >= 10000)

VARIABLES depositorTx, depositorWitnessedTx, AdversaryTx, 
          AdversaryWitnessedTx

vars == << depositor, event, oracle, withdrawer, network, adversary, Party, 
           ContractingParty, FailedContractingParty, eventHappened, mailbox, 
           reachedFailablePoint, depositorInitTx, serialized, unserialized, 
           Actor, BK, KnownSerializedTx, Coin, ConfirmedCoin, SpentCoin, age, 
           height, pc, depositorTx, depositorWitnessedTx, AdversaryTx, 
           AdversaryWitnessedTx >>

ProcSet == {depositor} \cup {event} \cup {oracle} \cup {withdrawer} \cup {network} \cup {adversary}

Init == (* Global variables *)
        /\ depositor = 0
        /\ event = 1
        /\ oracle = 2
        /\ withdrawer = 3
        /\ network = 4
        /\ adversary = 5
        /\ Party = {depositor,oracle,withdrawer}
        /\ ContractingParty = {depositor,withdrawer}
        /\ FailedContractingParty \in SUBSET ContractingParty
        /\ eventHappened = FALSE
        /\ mailbox =           [
                       self \in Party |-> [from \in Party |-> <<>>]
                     ]
        /\ reachedFailablePoint =                        [
                                    self \in ContractingParty |-> FALSE
                                  ]
        /\ depositorInitTx =                   [
                               nTxIn |-> 1,
                               txIn |-> <<[
                                 prevTxID |-> Rand(depositor,32,0),
                                 prevTxOutIdx |-> 0,
                                 ageLock |-> 0
                               ]>>,
                               nTxOut |-> 1,
                               txOut |-> <<[
                                 value |-> 10000,
                                 nPred |-> 1,
                                 nWit |-> <<
                                   1
                                 >>,
                                 pred |-> <<
                                   checksig_wit(0,PubKey33(depositor,0))
                                 >>
                               ]>>,
                               heightLock |-> 0
                             ]
        /\ serialized =              [
                          tx \in {depositorInitTx} |-> CASE tx = depositorInitTx -> 0
                        ]
        /\ unserialized =                [
                            serializedTx \in {0} |-> CASE serializedTx = 0 -> depositorInitTx
                          ]
        /\ Actor = (Party \cup {adversary})
        /\ BK =      [
                  a \in Actor |-> initBK_a(serialized,{depositorInitTx})
                ]
        /\ KnownSerializedTx =                     [
                                 a \in Actor |-> initKnownSerializedTx_a(serialized,{depositorInitTx})
                               ]
        /\ Coin = initCoin(serialized,{depositorInitTx})
        /\ ConfirmedCoin = initConfirmedCoin(serialized,{depositorInitTx})
        /\ SpentCoin = initSpentCoin(serialized,{depositorInitTx})
        /\ age =       [
                   coin \in Coin |-> CASE coin[1] = TxID(serialized[depositorInitTx]) -> 144
                 ]
        /\ height = 144
        (* Process Depositor *)
        /\ depositorTx = NULL
        /\ depositorWitnessedTx = NULL
        (* Process Adversary *)
        /\ AdversaryTx = NULL
        /\ AdversaryWitnessedTx = NULL
        /\ pc = [self \in ProcSet |-> CASE self = depositor -> "DepositorCreateTx"
                                        [] self = event -> "EventHappen"
                                        [] self = oracle -> "OracleSendHashToDepositor"
                                        [] self = withdrawer -> "WithdrawerSendingPubKeyToDepositor"
                                        [] self = network -> "NetworkWorking"
                                        [] self = adversary -> "AdversaryWorking"]

DepositorCreateTx == /\ pc[depositor] = "DepositorCreateTx"
                     /\ /\ Len(mailbox[depositor][oracle]) >= 1
                        /\ Len(mailbox[depositor][withdrawer]) >= 1
                     /\ depositorTx' =                [
                                         nTxIn |-> 1,
                                         txIn |-> <<[
                                           prevTxID |-> TxID(serialized[depositorInitTx]),
                                           prevTxOutIdx |-> 0,
                                           ageLock |-> 0
                                         ]>>,
                                         nTxOut |-> 1,
                                         txOut |-> <<[
                                           value |-> 10000,
                                           nPred |-> 1,
                                           nWit |-> <<
                                             2
                                           >>,
                                           pred |-> <<
                                             and(
                                               eq_hash20_wit(0,mailbox[depositor][oracle][1]),
                                               checksig_wit(1,mailbox[depositor][withdrawer][1])
                                             )
                                           >>
                                         ]>>,
                                         heightLock |-> 0
                                       ]
                     /\ /\ IsTx(depositorTx')
                        /\ creatable(BK[depositor],depositor,KnownSerializedTx[depositor],depositorTx')
                     /\ serialized' =               [
                                        x \in DOMAIN serialized
                                          \cup {depositorTx'}
                                        |-> IF x \in DOMAIN serialized THEN serialized[x] ELSE
                                            Cardinality(DOMAIN serialized)
                                      ]
                     /\ unserialized' =                 [
                                          x \in DOMAIN unserialized
                                            \cup {serialized'[depositorTx']}
                                          |-> IF x \in DOMAIN unserialized THEN unserialized[x] ELSE
                                              depositorTx'
                                        ]
                     /\ KnownSerializedTx' = [KnownSerializedTx EXCEPT ![depositor] = KnownSerializedTx[depositor] \cup {serialized'[depositorTx']}]
                     /\ pc' = [pc EXCEPT ![depositor] = "DepositorSendWitnessedTx"]
                     /\ UNCHANGED << depositor, event, oracle, withdrawer, 
                                     network, adversary, Party, 
                                     ContractingParty, FailedContractingParty, 
                                     eventHappened, mailbox, 
                                     reachedFailablePoint, depositorInitTx, 
                                     Actor, BK, Coin, ConfirmedCoin, SpentCoin, 
                                     age, height, depositorWitnessedTx, 
                                     AdversaryTx, AdversaryWitnessedTx >>

DepositorSendWitnessedTx == /\ pc[depositor] = "DepositorSendWitnessedTx"
                            /\ depositorWitnessedTx' =                         [
                                                         nTxIn |-> 1,
                                                         txIn |-> <<[
                                                           prevTxID |-> TxID(serialized[depositorInitTx]),
                                                           prevTxOutIdx |-> 0,
                                                           prevTxOutPredIdx |-> 0,
                                                           nWit |-> 1,
                                                           wit |-> <<
                                                             Sig71(depositor,0,serialized[depositorTx],0,serialized[depositorInitTx])
                                                           >>,
                                                           ageLock |-> 0
                                                         ]>>,
                                                         nTxOut |-> 1,
                                                         txOut |-> <<[
                                                           value |-> 10000,
                                                           nPred |-> 1,
                                                           nWit |-> <<
                                                             2
                                                           >>,
                                                           pred |-> <<
                                                             and(
                                                               eq_hash20_wit(0,mailbox[depositor][oracle][1]),
                                                               checksig_wit(1,mailbox[depositor][withdrawer][1])
                                                             )
                                                           >>
                                                         ]>>,
                                                         heightLock |-> 0
                                                       ]
                            /\ /\ IsWitnessedTx(depositorWitnessedTx')
                               /\ sendable(unserialized,BK[depositor],depositor,KnownSerializedTx[depositor],depositorWitnessedTx')
                               /\ receivable(unserialized,serialized,Coin,SpentCoin,age,height,depositorWitnessedTx')
                            /\ serialized' =               [
                                               x \in DOMAIN serialized
                                                 \cup {unwitnessed_for_WitnessedTx(depositorWitnessedTx')}
                                               |-> IF x \in DOMAIN serialized THEN serialized[x] ELSE
                                                   Cardinality(DOMAIN serialized)
                                             ]
                            /\ unserialized' =                 [
                                                 x \in DOMAIN unserialized
                                                   \cup {serialized'[unwitnessed_for_WitnessedTx(depositorWitnessedTx')]}
                                                 |-> IF x \in DOMAIN unserialized THEN unserialized[x] ELSE
                                                     unwitnessed_for_WitnessedTx(depositorWitnessedTx')
                                               ]
                            /\ BK' =       [
                                       a \in Actor |-> BK[a] \cup Wit_for_WitnessedTx(depositorWitnessedTx') \cup Arg_for_Tx(depositorWitnessedTx')
                                     ]
                            /\ KnownSerializedTx' =                      [
                                                      a \in Actor |-> KnownSerializedTx[a] \cup {serialized'[unwitnessed_for_WitnessedTx(depositorWitnessedTx')]}
                                                    ]
                            /\ Coin' = (Coin \cup {<<TxID(serialized'[unwitnessed_for_WitnessedTx(depositorWitnessedTx')]),k>> : k \in 0..(depositorWitnessedTx'.nTxOut - 1)})
                            /\ age' =        [
                                        coin \in DOMAIN age
                                             \cup {<<TxID(serialized'[unwitnessed_for_WitnessedTx(depositorWitnessedTx')]),k>> : k \in 0..(depositorWitnessedTx'.nTxOut - 1)}
                                        |-> IF coin \in DOMAIN age THEN age[coin] ELSE
                                            0
                                      ]
                            /\ pc' = [pc EXCEPT ![depositor] = "DepositorWaitForNetworkToConfirmTx"]
                            /\ UNCHANGED << depositor, event, oracle, 
                                            withdrawer, network, adversary, 
                                            Party, ContractingParty, 
                                            FailedContractingParty, 
                                            eventHappened, mailbox, 
                                            reachedFailablePoint, 
                                            depositorInitTx, Actor, 
                                            ConfirmedCoin, SpentCoin, height, 
                                            depositorTx, AdversaryTx, 
                                            AdversaryWitnessedTx >>

DepositorWaitForNetworkToConfirmTx == /\ pc[depositor] = "DepositorWaitForNetworkToConfirmTx"
                                      /\ <<TxID(serialized[depositorTx]),0>> \in ConfirmedCoin
                                      /\ reachedFailablePoint' = [reachedFailablePoint EXCEPT ![depositor] = TRUE]
                                      /\ pc' = [pc EXCEPT ![depositor] = "Done"]
                                      /\ UNCHANGED << depositor, event, oracle, 
                                                      withdrawer, network, 
                                                      adversary, Party, 
                                                      ContractingParty, 
                                                      FailedContractingParty, 
                                                      eventHappened, mailbox, 
                                                      depositorInitTx, 
                                                      serialized, unserialized, 
                                                      Actor, BK, 
                                                      KnownSerializedTx, Coin, 
                                                      ConfirmedCoin, SpentCoin, 
                                                      age, height, depositorTx, 
                                                      depositorWitnessedTx, 
                                                      AdversaryTx, 
                                                      AdversaryWitnessedTx >>

Depositor == DepositorCreateTx \/ DepositorSendWitnessedTx
                \/ DepositorWaitForNetworkToConfirmTx

EventHappen == /\ pc[event] = "EventHappen"
               /\ eventHappened' = TRUE
               /\ pc' = [pc EXCEPT ![event] = "Done"]
               /\ UNCHANGED << depositor, event, oracle, withdrawer, network, 
                               adversary, Party, ContractingParty, 
                               FailedContractingParty, mailbox, 
                               reachedFailablePoint, depositorInitTx, 
                               serialized, unserialized, Actor, BK, 
                               KnownSerializedTx, Coin, ConfirmedCoin, 
                               SpentCoin, age, height, depositorTx, 
                               depositorWitnessedTx, AdversaryTx, 
                               AdversaryWitnessedTx >>

Event == EventHappen

OracleSendHashToDepositor == /\ pc[oracle] = "OracleSendHashToDepositor"
                             /\ /\ IsCryptoObj((Hash20(Rand(oracle,20,0))))
                                /\ IsKnownCryptoObj_a(BK[oracle],oracle,KnownSerializedTx[oracle],(Hash20(Rand(oracle,20,0))))
                             /\ mailbox' = [mailbox EXCEPT ![depositor][oracle] = mailbox[depositor][oracle] \o <<(Hash20(Rand(oracle,20,0)))>>]
                             /\ BK' = [BK EXCEPT ![depositor] = BK[depositor] \cup {(Hash20(Rand(oracle,20,0)))}]
                             /\ pc' = [pc EXCEPT ![oracle] = "OracleWaitForEventToHappen"]
                             /\ UNCHANGED << depositor, event, oracle, 
                                             withdrawer, network, adversary, 
                                             Party, ContractingParty, 
                                             FailedContractingParty, 
                                             eventHappened, 
                                             reachedFailablePoint, 
                                             depositorInitTx, serialized, 
                                             unserialized, Actor, 
                                             KnownSerializedTx, Coin, 
                                             ConfirmedCoin, SpentCoin, age, 
                                             height, depositorTx, 
                                             depositorWitnessedTx, AdversaryTx, 
                                             AdversaryWitnessedTx >>

OracleWaitForEventToHappen == /\ pc[oracle] = "OracleWaitForEventToHappen"
                              /\ eventHappened = TRUE
                              /\ pc' = [pc EXCEPT ![oracle] = "OracleSendPreimageToWithdrawer"]
                              /\ UNCHANGED << depositor, event, oracle, 
                                              withdrawer, network, adversary, 
                                              Party, ContractingParty, 
                                              FailedContractingParty, 
                                              eventHappened, mailbox, 
                                              reachedFailablePoint, 
                                              depositorInitTx, serialized, 
                                              unserialized, Actor, BK, 
                                              KnownSerializedTx, Coin, 
                                              ConfirmedCoin, SpentCoin, age, 
                                              height, depositorTx, 
                                              depositorWitnessedTx, 
                                              AdversaryTx, 
                                              AdversaryWitnessedTx >>

OracleSendPreimageToWithdrawer == /\ pc[oracle] = "OracleSendPreimageToWithdrawer"
                                  /\ /\ IsCryptoObj((Rand(oracle,20,0)))
                                     /\ IsKnownCryptoObj_a(BK[oracle],oracle,KnownSerializedTx[oracle],(Rand(oracle,20,0)))
                                  /\ mailbox' = [mailbox EXCEPT ![withdrawer][oracle] = mailbox[withdrawer][oracle] \o <<(Rand(oracle,20,0))>>]
                                  /\ BK' = [BK EXCEPT ![withdrawer] = BK[withdrawer] \cup {(Rand(oracle,20,0))}]
                                  /\ pc' = [pc EXCEPT ![oracle] = "Done"]
                                  /\ UNCHANGED << depositor, event, oracle, 
                                                  withdrawer, network, 
                                                  adversary, Party, 
                                                  ContractingParty, 
                                                  FailedContractingParty, 
                                                  eventHappened, 
                                                  reachedFailablePoint, 
                                                  depositorInitTx, serialized, 
                                                  unserialized, Actor, 
                                                  KnownSerializedTx, Coin, 
                                                  ConfirmedCoin, SpentCoin, 
                                                  age, height, depositorTx, 
                                                  depositorWitnessedTx, 
                                                  AdversaryTx, 
                                                  AdversaryWitnessedTx >>

Oracle == OracleSendHashToDepositor \/ OracleWaitForEventToHappen
             \/ OracleSendPreimageToWithdrawer

WithdrawerSendingPubKeyToDepositor == /\ pc[withdrawer] = "WithdrawerSendingPubKeyToDepositor"
                                      /\ /\ IsCryptoObj((PubKey33(withdrawer,0)))
                                         /\ IsKnownCryptoObj_a(BK[withdrawer],withdrawer,KnownSerializedTx[withdrawer],(PubKey33(withdrawer,0)))
                                      /\ mailbox' = [mailbox EXCEPT ![depositor][withdrawer] = mailbox[depositor][withdrawer] \o <<(PubKey33(withdrawer,0))>>]
                                      /\ BK' = [BK EXCEPT ![depositor] = BK[depositor] \cup {(PubKey33(withdrawer,0))}]
                                      /\ reachedFailablePoint' = [reachedFailablePoint EXCEPT ![withdrawer] = TRUE]
                                      /\ pc' = [pc EXCEPT ![withdrawer] = "Done"]
                                      /\ UNCHANGED << depositor, event, oracle, 
                                                      withdrawer, network, 
                                                      adversary, Party, 
                                                      ContractingParty, 
                                                      FailedContractingParty, 
                                                      eventHappened, 
                                                      depositorInitTx, 
                                                      serialized, unserialized, 
                                                      Actor, KnownSerializedTx, 
                                                      Coin, ConfirmedCoin, 
                                                      SpentCoin, age, height, 
                                                      depositorTx, 
                                                      depositorWitnessedTx, 
                                                      AdversaryTx, 
                                                      AdversaryWitnessedTx >>

Withdrawer == WithdrawerSendingPubKeyToDepositor

NetworkWorking == /\ pc[network] = "NetworkWorking"
                  /\ \/ /\ \E tx \in {tx \in {unserialized[coin[1].serializedTx] : coin \in Coin \ ConfirmedCoin} : confirmable(serialized,ConfirmedCoin,SpentCoin,tx)}:
                             /\ ConfirmedCoin' = (ConfirmedCoin \cup {<<TxID(serialized[tx]),k>> : k \in 0..(tx.nTxOut - 1)})
                             /\ SpentCoin' = (SpentCoin \cup {<<tx.txIn[k + 1].prevTxID,tx.txIn[k + 1].prevTxOutIdx>> : k \in 0..(tx.nTxIn - 1)})
                        /\ UNCHANGED <<age, height>>
                     \/ /\ {tx \in {unserialized[coin[1].serializedTx] : coin \in Coin \ ConfirmedCoin} : confirmable(serialized,ConfirmedCoin,SpentCoin,tx)} = {}
                        /\ age' = [coin \in DOMAIN age |-> age[coin] + 144]
                        /\ height' = height + 144
                        /\ /\ ~ ENABLED Depositor
                           /\ ~ ENABLED Oracle
                           /\ ~ ENABLED Withdrawer
                        /\ height' <= MAXHEIGHT
                        /\ UNCHANGED <<ConfirmedCoin, SpentCoin>>
                  /\ pc' = [pc EXCEPT ![network] = "NetworkWorking"]
                  /\ UNCHANGED << depositor, event, oracle, withdrawer, 
                                  network, adversary, Party, ContractingParty, 
                                  FailedContractingParty, eventHappened, 
                                  mailbox, reachedFailablePoint, 
                                  depositorInitTx, serialized, unserialized, 
                                  Actor, BK, KnownSerializedTx, Coin, 
                                  depositorTx, depositorWitnessedTx, 
                                  AdversaryTx, AdversaryWitnessedTx >>

Network == NetworkWorking

AdversaryWorking == /\ pc[adversary] = "AdversaryWorking"
                    /\ AdversaryTx' = {tx \in {aTx(unserialized,
                                               adversary,
                                               age,
                                               height,
                                               coin) : coin \in {coin \in Coin \ SpentCoin : ~IsMine_cheated(unserialized,serialized,BK,Actor,adversary,KnownSerializedTx,Coin,SpentCoin,age,height,coin)}} \cup (DOMAIN serialized \ {unserialized[coin[1].serializedTx] : coin \in Coin})
                                                     : /\ IsTx(tx)
                                                       /\ creatable_cheated(BK,{adversary} \cup {p \in FailedContractingParty : reachedFailablePoint[p]},KnownSerializedTx,tx)}
                    /\ \E adversaryTx \in AdversaryTx':
                         /\ serialized' =               [
                                            x \in DOMAIN serialized
                                              \cup {adversaryTx}
                                            |-> IF x \in DOMAIN serialized THEN serialized[x] ELSE
                                                Cardinality(DOMAIN serialized)
                                          ]
                         /\ unserialized' =                 [
                                              x \in DOMAIN unserialized
                                                \cup {serialized'[adversaryTx]}
                                              |-> IF x \in DOMAIN unserialized THEN unserialized[x] ELSE
                                                  adversaryTx
                                            ]
                         /\ KnownSerializedTx' =                      [
                                                   x \in DOMAIN KnownSerializedTx |-> KnownSerializedTx[x] \cup {serialized'[adversaryTx]}
                                                 ]
                         /\ AdversaryWitnessedTx' = {witnessedTx \in AWitnessedTx(unserialized',
                                                                                  adversaryTx,
                                                                                  age,
                                                                                  height) : /\ IsWitnessedTx_cheated(witnessedTx)
                                                                                            /\ sendable_cheated(unserialized',BK,{adversary} \cup {p \in FailedContractingParty : reachedFailablePoint[p]},KnownSerializedTx',witnessedTx)
                                                                                            /\ receivable_cheated(unserialized',serialized',BK,{adversary} \cup {p \in FailedContractingParty : reachedFailablePoint[p]},KnownSerializedTx',Coin,SpentCoin,age,height,witnessedTx)}
                         /\ \E adversaryWitnessedTx \in AdversaryWitnessedTx':
                              /\ BK' =       [
                                         a \in Actor |-> BK[a] \cup Wit_for_WitnessedTx(adversaryWitnessedTx) \cup Arg_for_Tx(adversaryWitnessedTx)
                                       ]
                              /\ Coin' = (Coin \cup {<<TxID(serialized'[unwitnessed_for_WitnessedTx(adversaryWitnessedTx)]),k>> : k \in 0..(adversaryWitnessedTx.nTxOut - 1)})
                              /\ age' =        [
                                          coin \in DOMAIN age
                                               \cup {<<TxID(serialized'[unwitnessed_for_WitnessedTx(adversaryWitnessedTx)]),k>> : k \in 0..(adversaryWitnessedTx.nTxOut - 1)}
                                          |-> IF coin \in DOMAIN age THEN age[coin] ELSE
                                              0
                                        ]
                    /\ pc' = [pc EXCEPT ![adversary] = "AdversaryWorking"]
                    /\ UNCHANGED << depositor, event, oracle, withdrawer, 
                                    network, adversary, Party, 
                                    ContractingParty, FailedContractingParty, 
                                    eventHappened, mailbox, 
                                    reachedFailablePoint, depositorInitTx, 
                                    Actor, ConfirmedCoin, SpentCoin, height, 
                                    depositorTx, depositorWitnessedTx >>

Adversary == AdversaryWorking

Next == Depositor \/ Event \/ Oracle \/ Withdrawer \/ Network \/ Adversary

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Depositor)
        /\ WF_vars(Oracle)
        /\ WF_vars(Withdrawer)
        /\ WF_vars(Network)

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Jan 16 14:35:19 JST 2023 by azon
\* Created Thu Nov 03 06:12:42 JST 2022 by azon
