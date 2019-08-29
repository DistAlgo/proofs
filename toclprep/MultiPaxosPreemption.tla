------------------------------- MODULE MultiPaxosPreemption -------------------------------
(***************************************************************************)
(* This is a TLA+ specification and machine checked proof of the           *)
(* MultiPaxos Consensus algorithm.                                         *)
(***************************************************************************)
EXTENDS Integers, TLAPS, FiniteSets, FiniteSetTheorems
CONSTANTS Proposers, Acceptors, Quorums, Values
VARIABLES msgs,     \* Set of sent messages
          pBal,     \* Current ballot being run by proposers
          aBal,     \* For each acceptor, the highest ballot seen by it.
          aVoted    \* Set of <<ballot, slot, value>> triples per acceptor that it has VotedForIn.

ASSUME QuorumAssumption == Quorums \subseteq SUBSET Acceptors /\ \A Q1, Q2 \in Quorums: Q1 \cap Q2 # {}

Ballots == Nat
Slots == Nat
vars == <<msgs, aVoted, aBal, pBal>>
Send(m) == msgs' = msgs \cup {m}

(***************************************************************************)
(* Phase 1a: Executed by a proposer, it selects a ballot number on which   *)
(* Phase 1a has never been initiated. This number is sent to any set of    *)
(* acceptors which contains at least one quorum from Quorums. Trivially it *)
(* can be broadcasted to all Acceptors. For safety, any subset of          *)
(* Acceptors would suffice. For liveness, a subset containing at least one *)
(* Quorum is needed.                                                       *)
(***************************************************************************)
Phase1a(p) == /\ Send([type |-> "1a", from |-> p, bal |-> pBal[p]])
              /\ UNCHANGED <<aVoted, aBal, pBal>>
              
(***************************************************************************)
(* Phase 1b: If an acceptor receives a 1a message with ballot b greater    *)
(* than that of any 1a message to which it has already responded, then it  *)
(* responds to the request with a promise not to accept any more proposals *)
(* for ballots numbered less than b; otherwise it sends a preempt to the   *)
(* proposer telling the greater ballot.                                    *)
(* In case of a 1b reply, the acceptor writes a mapping in Slots ->        *)
(* Ballots \times Values. This mapping reveals for each slot, the value    *)
(* that the acceptor most recently (that is, highest ballot) voted on, if  *)
(* any.                                                                    *)
(***************************************************************************)
Phase1b(a) == \E m \in msgs: m.type = "1a" /\
  IF m.bal > aBal[a] THEN
     /\ Send([type |-> "1b", from |-> a, bal |-> m.bal, voted |-> aVoted[a]])
     /\ aBal' = [aBal EXCEPT ![a] = m.bal]
     /\ UNCHANGED <<aVoted, pBal>>
 ELSE
     /\ Send([type |-> "preempt", to |-> m.from, bal |-> aBal[a]])
     /\ UNCHANGED <<aVoted, aBal, pBal>>
        
(***************************************************************************)
(* Phase 2a: If the proposer receives a response to its 1b message (for    *)
(* ballot b) from a quorum of acceptors, then it sends a 2a message to all *)
(* acceptors for a proposal in ballot b. Per slot received in the replies, *)
(* the proposer finds out the value most recently (i.e., highest ballot)   *)
(* voted by the acceptors in the received set. Thus a mapping in Slots ->  *)
(* Values is created. This mapping along with the ballot that passed Phase *)
(* 1a is propogated to again, any subset of Acceptors - Hopefully to one   *)
(* containing at least one quorum. MaxSV creates the desired mapping from   *)
(* received replies. NewSV instructs how new slots are entered in   *)
(* the system.                                                             *)
(***************************************************************************)
MaxBSV(T)    == {t \in T: \A t1 \in T: t1.slot = t.slot => t1.bal \leq t.bal}
MaxSV(T)           == {[slot |-> t.slot, val |-> t.val]: t \in MaxBSV(T)}
UnusedS(T)      == {s \in Slots: ~\E t\in T: t.slot = s}
NewSV(T)   == CHOOSE D \in SUBSET [slot: UnusedS(T), val: Values]:
                       \A d1, d2 \in D: d1.slot = d2.slot => d1 = d2
PropSV(T) == MaxSV(T) \cup NewSV(T)




Phase2a(p) ==
  /\ ~\E m \in msgs: (m.type = "2a") /\ (m.bal = pBal[p])
  /\ \E Q \in Quorums, S \in SUBSET {m \in msgs: (m.type = "1b") /\ (m.bal = pBal[p])}:
       /\ \A a \in Q: \E m \in S: m.from = a
       /\ Send([type |-> "2a", from |-> p, bal |-> pBal[p], decrees |-> PropSV(UNION {m.voted: m \in S})])
  /\ UNCHANGED <<aBal, aVoted, pBal>>

(***************************************************************************)
(* Phase 2b: If an acceptor receives a 2a message for a ballot which is    *)
(* the highest that it has seen, it votes for the all the message's values *)
(* in ballot b.                                                            *)
(***************************************************************************)
Phase2b(a) == \E m \in msgs: m.type = "2a" /\
  IF m.bal \geq aBal[a] THEN
     /\ Send([type |-> "2b", from |-> a, bal |-> m.bal, decrees |-> m.decrees])
     /\ aBal' = [aBal EXCEPT ![a] = m.bal]
     /\ aVoted' = [aVoted EXCEPT ![a] = {d \in aVoted[a]: ~\E d2 \in m.decrees: d.slot = d2.slot } \cup
                    {[bal |-> m.bal, slot |-> d.slot, val |-> d.val]: d \in m.decrees}]
     /\ UNCHANGED <<pBal>>
 ELSE
     /\ Send([type |-> "preempt", to |-> m.from, bal |-> aBal[a]])
     /\ UNCHANGED <<aVoted, aBal, pBal>>

(***************************************************************************)
(* Preempt: If a proposer is responded with a preempt message, it realizes *)
(* the existence of a larger ballot than its in the system. Following this *)
(* the proposer updates its pBal, which is the next ballot it is           *)
(* going to propose on, to be greater than the received ballot in preempt, *)
(* and a ballot on which no 1a message has been sent yet by anyone in the  *)
(* system.                                                                 *)
(***************************************************************************)
NewBallot(b2) == CHOOSE b \in Ballots: b > b2 /\ ~ \E m \in msgs: m.type = "1a" /\ m.bal = b

Preempt(p) == \E m \in msgs:
  /\ m.type = "preempt" /\ m.to = p /\ m.bal > pBal[p]
  /\ pBal' = [pBal EXCEPT ![p] = NewBallot(m.bal)]
  /\ UNCHANGED <<aVoted, aBal, msgs>>

Init == aVoted = [a \in Acceptors |-> {}]  /\ msgs = {} /\ aBal = [a \in Acceptors |-> -1]  /\ pBal = [p \in Proposers |-> 0]
Next == \/ \E p \in Proposers: Phase1a(p) \/ Phase2a(p) \/ Preempt(p)
        \/ \E a \in Acceptors: Phase1b(a) \/ Phase2b(a)
Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
(***************************************************************************)
(* How a value is chosen:                                                  *)
(*                                                                         *)
(* This spec does not contain any actions in which a value is explicitly   *)
(* chosen (or a chosen value learned).  What it means for a value to be    *)
(* chosen is defined by the operator Chosen, where Chosen(s, v) means that *)
(* value v has been chosen for slot s.                                     *)
(***************************************************************************)
VotedForIn(a, b, s, v) == \E m \in msgs:
  m.type = "2b" /\ m.from = a /\ m.bal = b /\ \E d \in m.decrees: d.slot = s /\ d.val = v

ChosenIn(b, s, v) == \E Q \in Quorums: \A a \in Q: VotedForIn(a, b, s, v)
Chosen(s, v) == \E b \in Ballots: ChosenIn(b, s, v)

(***************************************************************************)
(* The consistency condition that a consensus algorithm must satisfy is    *)
(* the invariance of the following state predicate Consistency.            *)
(***************************************************************************)
Consistency == \A v1, v2 \in Values, s \in Slots: Chosen(s, v1) /\ Chosen(s, v2) => (v1 = v2)
-----------------------------------------------------------------------------



(***************************************************************************)
(* This section of the spec defines the invariant Inv.                     *)
(***************************************************************************)
Messages == [type: {"1a"}, from: Proposers, bal: Ballots] \cup
            [type: {"1b"}, from: Acceptors, bal: Ballots, voted: SUBSET [bal: Ballots, slot: Slots, val: Values]] \cup
            [type: {"2a"}, from: Proposers, bal: Ballots, decrees: SUBSET [slot: Slots, val: Values]] \cup
            [type: {"2b"}, from: Acceptors, bal: Ballots, decrees: SUBSET [slot: Slots, val: Values]] \cup
            [type: {"preempt"}, to: Proposers, bal: Ballots]

TypeOK == /\ msgs \in SUBSET Messages /\ aVoted \in [Acceptors -> SUBSET [bal: Ballots, slot: Slots, val: Values]]
          /\ aBal \in [Acceptors -> Ballots \cup {-1}] /\ pBal \in [Proposers -> Ballots] /\ IsFiniteSet(msgs)

(***************************************************************************)
(* WontVoteIn(a, b, s) is a predicate that implies that acceptor a has not *)
(* voted and will never vote in ballot b wrt slot s.                       *)
(***************************************************************************)                                       
WontVoteIn(a, b, s) == aBal[a] > b /\ \A v \in Values: ~ VotedForIn(a, b, s, v)

(***************************************************************************)
(* The predicate SafeAt(b, s, v) implies that no value other than perhaps  *)
(* v has been or ever will be chosen in any ballot numbered less than b    *)
(* for slot s.                                                             *)
(***************************************************************************)                   
SafeAt(b, s, v) == \A b2 \in 0..(b-1): \E Q \in Quorums: \A a \in Q: VotedForIn(a, b2, s, v) \/ WontVoteIn(a, b2, s)

(***************************************************************************)
(* Max(S) picks the largest element in the set S.                          *)
(***************************************************************************)
Max(S) == CHOOSE b \in S: \A b2 \in S: b \geq b2

(***************************************************************************)
(* MaxBallotInSlot(S, s) picks the highest ballot in S for slot s or       *)
(* -1 if S has no vote in slot s. S is a set of records with at least two  *)
(* fields: slot and bal.                                                   *)
(***************************************************************************)
MaxBallotInSlot(S, s) == LET B == {e.bal: e \in {e \in S: e.slot = s}}  IN
                         IF {e \in S: e.slot = s} = {} THEN -1 ELSE Max(B)

MsgInv1b(m) == /\ m.bal \leq aBal[m.from]
               /\ \A r\in m.voted: VotedForIn(m.from, r.bal, r.slot, r.val)
               /\ \A b2\in Ballots, s\in Slots, v \in Values: b2 \in MaxBallotInSlot(m.voted, s)+1..m.bal-1 =>
                      ~ VotedForIn(m.from, b2, s, v)

MsgInv2a(m) == /\ \A d \in m.decrees: SafeAt(m.bal, d.slot, d.val)
               /\ \A d1,d2 \in m.decrees: d1.slot = d2.slot => d1 = d2
               /\ \A m2 \in msgs: (m2.type = "2a" /\ m2.bal = m.bal) => m = m2

MsgInv2b(m) == /\ \E m2 \in msgs: m2.type = "2a" /\ m2.bal = m.bal /\ m2.decrees = m.decrees
               /\ m.bal \leq aBal[m.from]

MsgInv == \A m \in msgs: /\ (m.type = "1b") => MsgInv1b(m)
                         /\ (m.type = "2a") => MsgInv2a(m)
                         /\ (m.type = "2b") => MsgInv2b(m)

AccInv == \A a \in Acceptors:
  /\ aBal[a] = -1 => aVoted[a] = {}
  /\ \A r \in aVoted[a]: aBal[a] \geq r.bal /\ VotedForIn(a, r.bal, r.slot, r.val)
  /\ \A b \in Ballots, s \in Slots, v \in Values: VotedForIn(a, b, s, v) => \E r \in aVoted[a]: r.bal \geq b /\ r.slot = s
  /\ \A b \in Ballots, s \in Slots, v \in Values: b > MaxBallotInSlot(aVoted[a], s) => ~ VotedForIn(a, b, s, v)

(***************************************************************************)
(* The following lemmas are simple consequences of the definitions.        *)
(***************************************************************************)
AXIOM MaxInSet == \A S \in (SUBSET Nat) \ {}: Max(S) \in S
AXIOM MaxOnNat == \A S \in SUBSET Nat: ~\E s \in S: Max(S) < s

LEMMA MaxOnNatS == \A S1, S2 \in (SUBSET Nat) \ {}: S1 \subseteq S2 => Max(S1) =< Max(S2)  BY MaxInSet

LEMMA MBISType == \A S \in SUBSET [bal: Ballots, slot: Slots, val: Values], s \in Slots: MaxBallotInSlot(S, s) \in Ballots \cup {-1}
BY MaxInSet DEF MaxBallotInSlot

LEMMA MBISSubsets == \A S1, S2 \in SUBSET [bal: Ballots, slot: Slots, val: Values], s \in Slots: S1 \subseteq S2 =>
                        MaxBallotInSlot(S1, s) =< MaxBallotInSlot(S2, s)
  <1> SUFFICES ASSUME NEW S1 \in SUBSET [bal: Ballots, slot: Slots, val: Values], NEW s\in Slots,
                      NEW S2 \in SUBSET [bal: Ballots, slot: Slots, val: Values], S1 \subseteq S2
               PROVE  MaxBallotInSlot(S1, s) =< MaxBallotInSlot(S2, s)
      OBVIOUS
  <1>1. CASE ~ \E d \in S1: d.slot = s
    <2>1. MaxBallotInSlot(S1, s) = -1  BY <1>1 DEF MaxBallotInSlot
    <2> QED BY <2>1, MBISType DEF Ballots
  <1>2. CASE \E d \in S1: d.slot = s
    <2>1. CASE ~ \E d \in S2 \ S1: d.slot = s
      <3>1. MaxBallotInSlot(S1, s) = MaxBallotInSlot(S2, s)  BY <2>1, <1>2 DEF MaxBallotInSlot
      <3> QED BY <3>1, MBISType DEF Ballots
    <2>2. CASE \E d \in S2 \ S1: d.slot = s  BY <2>2, <1>2, MBISType, MaxOnNatS DEF Ballots, MaxBallotInSlot
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>1, <1>2

LEMMA MBISNoSlot == \A S \in SUBSET [bal: Ballots, slot: Slots, val: Values], s \in Slots:
                       (~ \E d \in S: d.slot = s) <=> MaxBallotInSlot(S, s) = -1 
BY MaxInSet DEF MaxBallotInSlot, Ballots

LEMMA MBISExists == \A S \in SUBSET [bal: Ballots, slot: Slots, val: Values], s \in Slots: MaxBallotInSlot(S, s) \in Ballots =>
                       \E d\in S: d.slot = s /\ d.bal = MaxBallotInSlot(S, s)
  <1> SUFFICES ASSUME NEW S \in SUBSET [bal: Ballots, slot: Slots, val: Values],
                      NEW s \in Slots, MaxBallotInSlot(S, s) \in Ballots
               PROVE  \E d \in S: d.bal = MaxBallotInSlot(S, s) /\ d.slot = s
      OBVIOUS
    <1>1. \E d \in S: d.slot = s  BY DEF MaxBallotInSlot, Ballots
    <1>2. MaxBallotInSlot(S, s) = Max({d.bal: d \in {d \in S: d.slot = s}})  BY <1>1 DEF MaxBallotInSlot
  <1> QED BY <1>1, <1>2, MaxInSet

LEMMA MBISNoMore == \A S \in SUBSET [bal: Ballots, slot: Slots, val: Values], s \in Slots:
                       ~\E d \in S: d.bal > MaxBallotInSlot(S, s) /\ d.slot = s
  <1> SUFFICES ASSUME NEW S \in SUBSET [bal: Ballots, slot: Slots, val: Values], NEW s \in Slots
               PROVE  ~\E d\in S: d.bal > MaxBallotInSlot(S, s) /\ d.slot = s
      OBVIOUS
    <1>1. CASE ~\E d \in S: d.slot = s  BY <1>1
    <1>2. CASE \E d \in S: d.slot = s
      <2>1. ~ \E b \in {d.bal: d \in {d \in S: d.slot = s}}: b > MaxBallotInSlot(S, s)
            BY <1>2, MaxOnNat DEF MaxBallotInSlot, Ballots, Slots
      <2>2. ~ \E d \in S: (d.slot = s /\ ~(d.bal =< MaxBallotInSlot(S, s)))  BY <2>1
      <2> QED BY <2>2
  <1> QED BY <1>1, <1>2

LEMMA NPC == \A S: /\ NewSV(S) \in (SUBSET [slot: UnusedS(S), val: Values])
                   /\ \A t1, t2 \in NewSV(S): t1.slot = t2.slot => t1 = t2
                   /\ ~ \E t1 \in MaxSV(S), t2 \in NewSV(S): t1.slot = t2.slot
  <1> SUFFICES ASSUME NEW S
               PROVE  /\ NewSV(S) \in (SUBSET [slot: UnusedS(S), val: Values])
                      /\ \A t1, t2 \in NewSV(S): t1.slot = t2.slot => t1 = t2
                      /\ ~ \E t1 \in MaxSV(S), t2 \in NewSV(S): t1.slot = t2.slot
      OBVIOUS
  <1>1. \E T \in (SUBSET [slot: UnusedS(S), val: Values]) : \A t1, t2 \in T: t1.slot = t2.slot => t1 = t2
        BY DEF UnusedS
  <1>2. NewSV(S) \in (SUBSET [slot: UnusedS(S), val: Values])  BY <1>1 DEF NewSV
  <1>3. \A t1, t2 \in NewSV(S): t1.slot = t2.slot => t1 = t2  BY <1>1 DEF NewSV
  <1>4. ~ \E t1 \in MaxSV(S), t2 \in ([slot: UnusedS(S), val: Values]) : t1.slot = t2.slot
        BY DEF MaxSV, MaxBSV, UnusedS
  <1> QED BY <1>2, <1>3, <1>4

LEMMA VotedInv ==  MsgInv /\ TypeOK => \A a \in Acceptors, b \in Ballots, s \in Slots, v \in Values:
                     VotedForIn(a, b, s, v) => SafeAt(b, s, v) /\ b =< aBal[a]
BY DEF VotedForIn, MsgInv, Messages, TypeOK, MsgInv2a, MsgInv1b, MsgInv2b

LEMMA VotedOnce == MsgInv => \A a1, a2 \in Acceptors, b \in Ballots, v1, v2 \in Values, s \in Slots:
                     VotedForIn(a1, b, s, v1) /\ VotedForIn(a2, b, s, v2) => (v1 = v2)
BY DEF MsgInv, VotedForIn, MsgInv2a, MsgInv1b, MsgInv2b

LEMMA VotedUnion == MsgInv /\ TypeOK => \A m1, m2 \in msgs: m1.type = "1b" /\ m2.type = "1b" =>
                      \A d1 \in m1.voted, d2\in m2.voted: (d1.bal = d2.bal/\ d1.slot = d2.slot) =>
                        d1.val = d2.val
  <1> SUFFICES ASSUME MsgInv, TypeOK, NEW m1 \in msgs, NEW m2 \in msgs, m1.type = "1b", m2.type = "1b",
                      NEW d1 \in m1.voted, NEW d2 \in m2.voted, d1.bal = d2.bal, d1.slot = d2.slot
               PROVE  d1.val= d2.val
      OBVIOUS
    <1>1. VotedForIn(m1.from, d1.bal, d1.slot, d1.val)  BY DEF MsgInv, MsgInv1b
    <1>2. VotedForIn(m2.from, d2.bal, d2.slot, d2.val)  BY DEF MsgInv, MsgInv1b
  <1> QED BY <1>1, <1>2, VotedOnce DEF TypeOK, Messages

(***************************************************************************)
(* Inv is the complete inductive invariant.                                *)
(***************************************************************************)
Inv == TypeOK /\ MsgInv /\ AccInv

LEMMA Phase1aVotedForInv == TypeOK => \A p \in Proposers: Phase1a(p) => \A a \in Acceptors, b \in Ballots, s \in Slots, v \in Values:
                              VotedForIn(a, b, s, v) <=> VotedForIn(a, b, s, v)'
BY DEF VotedForIn, Send, TypeOK, Messages, Phase1a

LEMMA Phase1bVotedForInv == TypeOK => \A a \in Acceptors: Phase1b(a) => \A a2 \in Acceptors, b \in Ballots, s \in Slots, v \in Values:
                              VotedForIn(a2, b, s, v) <=> VotedForIn(a2, b, s, v)'
BY DEF VotedForIn, Send, TypeOK, Messages, Phase1b

LEMMA Phase2aVotedForInv == TypeOK => \A p \in Proposers: Phase2a(p) => \A a \in Acceptors, b \in Ballots, s \in Slots, v \in Values:
                              VotedForIn(a, b, s, v) <=> VotedForIn(a, b, s, v)'
BY DEF VotedForIn, Send, TypeOK, Messages, Phase2a, PropSV, MaxSV, NewSV, UnusedS, MaxBSV

LEMMA Phase2bVotedForInv == TypeOK => \A a \in Acceptors: Phase2b(a) => \A a2 \in Acceptors, b \in Ballots, s \in Slots, v \in Values:
                              VotedForIn(a2, b, s, v) => VotedForIn(a2, b, s, v)'
BY DEF VotedForIn, Send, TypeOK, Messages, Phase2b

LEMMA PreemptVotedForInv == TypeOK => \A p \in Proposers: Preempt(p) => \A a \in Acceptors, b \in Ballots, s \in Slots, v \in Values:
                              VotedForIn(a, b, s, v) <=> VotedForIn(a, b, s, v)'
BY DEF VotedForIn, Send, TypeOK, Messages, Preempt

-----------------------------------------------------------------------------
(***************************************************************************)
(* The following lemma shows that (the invariant implies that) the         *)
(* predicate SafeAt(v, b,s) is stable, meaning that once it becomes true,  *)
(* it remains true throughout the rest of the excecution.                  *)
(***************************************************************************)
LEMMA SafeAtStable == Inv /\ Next /\ TypeOK' => \A b \in Ballots, s \in Slots, v \in Values:
                        SafeAt(b, s, v) => SafeAt(b, s, v)'
<1> SUFFICES ASSUME Inv, Next, TypeOK', NEW b \in Ballots, NEW s \in Slots, NEW v \in Values, SafeAt(b, s, v)
             PROVE  SafeAt(b, s, v)'
    OBVIOUS
<1> USE DEF Send, Inv, Ballots
<1>1. CASE \E p \in Proposers: Phase1a(p)  BY <1>1 DEF SafeAt, Phase1a, VotedForIn, WontVoteIn
<1>2. CASE \E a \in Acceptors: Phase1b(a)
      BY <1>2, QuorumAssumption DEF TypeOK, SafeAt, WontVoteIn, VotedForIn, Phase1b
<1>3. ASSUME NEW p \in Proposers, Phase2a(p)  PROVE SafeAt(b, s, v)'
  <2>1. \A a \in Acceptors, b2 \in Ballots, s2 \in Slots: WontVoteIn(a, b2, s2) <=> WontVoteIn(a, b2, s2)'
        BY <1>3, Phase2aVotedForInv DEF WontVoteIn, Send, Phase2a
  <2> QED BY <2>1, QuorumAssumption, Phase2aVotedForInv, <1>3 DEF SafeAt
<1>4. ASSUME NEW a \in Acceptors, Phase2b(a)  PROVE SafeAt(b, s, v)'
  <2>1. PICK m \in msgs: Phase2b(a)!(m)  BY <1>4 DEF Phase2b
  <2>2. \A a2 \in Acceptors, b2 \in Ballots: aBal[a2] > b2 => aBal'[a2] > b2  BY <2>1 DEF TypeOK
  <2>3. ASSUME NEW a2 \in Acceptors, NEW b2 \in Ballots, NEW s2 \in Slots, NEW v2 \in Values, WontVoteIn(a2, b2, s2),
               VotedForIn(a2, b2, s2, v2)', NEW S \in SUBSET [slot: Slots \ {s2}, val: Values]
        PROVE  FALSE
    <3>1. \E m1 \in msgs' \ msgs: /\ m1.type = "2b" /\ m1.bal = b2 /\ m1.from = a2
                                  /\ \E d \in m1.decrees: d.slot = s2 /\ d.val = v2
          BY <2>3 DEF VotedForIn, WontVoteIn
    <3>2. a2 = a /\ m.bal = b2  BY <2>1, <3>1 DEF TypeOK
    <3> QED  BY <2>1, <2>3, <3>2, <3>1 DEF Phase2b, WontVoteIn, TypeOK 
  <2>4. \A a2 \in Acceptors, b2 \in Ballots, s2 \in Slots : WontVoteIn(a2, b2, s2) => WontVoteIn(a2, b2, s2)'
    BY <2>2, <2>3 DEF WontVoteIn
  <2> QED BY Phase2bVotedForInv, <2>4, QuorumAssumption, <1>4 DEF SafeAt
<1>5. CASE \E p \in Proposers: Preempt(p)  BY <1>5 DEF SafeAt, Preempt, VotedForIn, WontVoteIn
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF Next

THEOREM Invariant == Spec => []Inv
<1> USE DEF Ballots, Slots
<1>1. Init => Inv  BY FS_EmptySet DEF Init, Inv, TypeOK, AccInv, MsgInv, VotedForIn
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE  Inv'
      OBVIOUS
  <2> USE DEF Inv
  <2>1. CASE Next
  <3>1. TypeOK'
    <4>1. ASSUME NEW p \in Proposers, Phase1a(p)  PROVE TypeOK'
          BY <4>1, msgs' \ msgs \subseteq Messages, FS_AddElement DEF Phase1a, TypeOK, Send, Messages
    <4>2. ASSUME NEW p \in Proposers, Phase2a(p)  PROVE TypeOK'
      <5>1. PICK Q \in Quorums, S \in SUBSET {m \in msgs: (m.type = "1b") /\ (m.bal = pBal[p])}:
                /\ \A a \in Q: \E m \in S: m.from = a
                /\ Send([type |-> "2a", from |-> p, bal |-> pBal[p],
                     decrees |-> PropSV(UNION {m.voted: m \in S})])  BY <4>2 DEF Phase2a
      <5>2. UnusedS(UNION {m.voted: m \in S}) \subseteq Slots  BY <5>1 DEF UnusedS, TypeOK, Messages
      <5>3. MaxBSV(UNION {m.voted: m \in S}) \subseteq [bal: Ballots, slot: Slots, val: Values]
            BY DEF MaxBSV, TypeOK, Messages
      <5>4. /\ NewSV(UNION {m.voted: m \in S}) \subseteq [slot: Slots, val: Values]
            /\ MaxSV(UNION {m.voted: m \in S}) \subseteq [slot: Slots, val: Values]  BY <5>3, <5>2, NPC DEF MaxSV
      <5>5. PropSV(UNION {m.voted: m \in S}) \subseteq [slot: Slots, val: Values]  BY <5>4 DEF PropSV
      <5>6. \A m2 \in msgs' \ msgs: /\ m2.type = "2a" /\ m2.from = p /\ m2.bal = pBal[p]
                                    /\ m2.decrees = PropSV(UNION {m.voted: m \in S})
            BY <5>1, <5>5 DEF Send, TypeOK, Messages
      <5>7. (msgs \in SUBSET Messages)'  BY <4>2, <5>6, <5>1, <5>5, msgs' \ msgs \subseteq Messages DEF Phase2a,
            TypeOK, Send, Messages
      <5> QED BY <5>7, <4>2, FS_AddElement DEF Phase2a, TypeOK, Send
    <4>3. ASSUME NEW a \in Acceptors, Phase1b(a)  PROVE TypeOK'
      <5>1. PICK m \in msgs: Phase1b(a)!(m)  BY <4>3 DEF Phase1b
      <5>2. \A m2 \in msgs' \ msgs: \/ m2.type = "1b" /\ m2.from = a /\ m2.bal = m.bal /\ m2.voted = aVoted[a]
                                    \/ m2.type = "preempt" /\ m2.to = m.from /\ m2.bal = aBal[a]
            BY <5>1 DEF Send
      <5>4. (msgs \in SUBSET Messages)'  BY <5>1, <5>2 DEF TypeOK, Messages, Send
      <5>5. IsFiniteSet(msgs)'  BY <5>2, <5>1, FS_AddElement DEF TypeOK, Send
      <5> QED BY <5>4, <5>5, <4>3 DEF Phase1b, TypeOK
    <4>4. ASSUME NEW a \in Acceptors, Phase2b(a)  PROVE TypeOK'
      <5>1. PICK m \in msgs: Phase2b(a)!(m)  BY <4>4 DEF Phase2b
      <5>2. \A m2 \in msgs' \ msgs: \/ m2.type = "2b" /\ m2.from = a /\ m2.bal = m.bal /\ m2.decrees = m.decrees
                                    \/ m2.type = "preempt" /\ m2.to = m.from /\ m2.bal = aBal[a]
            BY <5>1 DEF Send
      <5>3. IsFiniteSet(msgs)'  BY <5>2, <5>1, FS_AddElement DEF TypeOK, Send
      <5>4. (msgs \in SUBSET Messages)'  BY <5>1, <5>2 DEF TypeOK, Send, Messages
      <5>5. \/ aVoted = aVoted'
            \/ /\ DOMAIN aVoted = DOMAIN aVoted'
               /\ aVoted'[a] = {d \in aVoted[a]: ~\E d2 \in m.decrees: d.slot = d2.slot} \cup
                               {[bal |-> m.bal, slot |-> d.slot, val |-> d.val]: d \in m.decrees}
               /\ \A a2 \in Acceptors \ {a}: aVoted[a2] = aVoted'[a2]  BY <5>1 DEF TypeOK
      <5>6. (aVoted \in [Acceptors -> SUBSET [bal: Ballots, slot: Slots, val: Values]])'  BY <5>1, <5>5,
            {[bal |-> m.bal, slot |-> d.slot, val |-> d.val]: d \in m.decrees} \subseteq [bal: Ballots, slot: Slots, val: Values],
            {d \in aVoted[a]: ~\E d2 \in m.decrees: d.slot = d2.slot} \subseteq [bal: Ballots, slot: Slots, val: Values],
            aVoted'[a] \subseteq [bal: Ballots, slot: Slots, val: Values] DEF TypeOK, Messages
      <5> QED BY <5>4, <5>6, <4>4, <5>3 DEF Phase2b, TypeOK
    <4>5. ASSUME NEW p \in Proposers, Preempt(p)  PROVE TypeOK'
      <5> DEFINE S == {m1 \in msgs: m1.type = "1a"}  T == {s.bal: s \in S}  f == [s \in S |-> s.bal]
      <5> HIDE DEF S, T, f
      <5>1. PICK m \in msgs: Preempt(p)!(m)  BY <4>5 DEF Preempt
      <5>2. T \subseteq Ballots  BY DEF T, S, TypeOK, Messages
      <5>3. \E b \in Ballots: b > m.bal /\ b \notin T
            BY <5>2, MaxInSet, Max(T \cup {m.bal}) + 1 > m.bal, <5>1 DEF Max, TypeOK, Messages
      <5>4. NewBallot(m.bal) \in Ballots  BY <5>3 DEF NewBallot, TypeOK, Messages, T, S
      <5>5. (pBal \in [Proposers -> Ballots])'  BY <5>1, <5>4 DEF TypeOK, Messages
      <5> QED BY <4>5, <5>5 DEF Preempt, TypeOK
    <4> QED BY <2>1, <4>1, <4>2, <4>3, <4>4, <4>5 DEF Next

  <3>2. AccInv'
    <4>1. CASE \E p \in Proposers: Phase1a(p)  BY <4>1, <3>1, Phase1aVotedForInv DEF AccInv, TypeOK, Phase1a, Send
    <4>2. ASSUME NEW p \in Proposers, Phase2a(p)  PROVE AccInv'
      <5>1. \A a \in Acceptors, b \in Ballots, s \in Slots, v \in Values: VotedForIn(a, b, s, v) <=> VotedForIn(a, b, s, v)'
            BY <4>2, Phase2aVotedForInv
      <5> QED BY <3>1, <4>2, <5>1 DEF AccInv, TypeOK, Phase2a, Send, Messages
    <4>3. CASE \E a \in Acceptors: Phase1b(a)  BY <4>3, <3>1, Phase1bVotedForInv DEF AccInv, TypeOK, Phase1b, Send
    <4>4. ASSUME NEW a \in Acceptors, Phase2b(a)  PROVE AccInv'
      <5> SUFFICES ASSUME NEW a2 \in Acceptors'
                   PROVE  (/\ aBal[a2] = -1 => aVoted[a2] = {}
                           /\ \A r \in aVoted[a2]: VotedForIn(a2, r.bal, r.slot, r.val) /\ r.bal =< aBal[a2]
                           /\ \A b \in Ballots, s \in Slots, v \in Values:
                                /\ VotedForIn(a2, b, s, v) => \E r \in aVoted[a2]: r.bal >= b /\ r.slot = s 
                                /\ b > MaxBallotInSlot(aVoted[a2], s) => ~ VotedForIn(a2, b, s, v))'
          BY DEF AccInv
      <5>1. PICK m \in msgs: Phase2b(a)!(m)  BY <4>4 DEF Phase2b
      <5>2. CASE (a2 = a /\ ~ (m.bal >= aBal[a])) \/ a2 # a
        <6>1. \A b \in Ballots, s \in Slots, v \in Values: VotedForIn(a2, b, s, v) <=> VotedForIn(a2, b, s, v)'
              BY <3>1, <5>1, <5>2 DEF Phase2b, TypeOK, Ballots, Messages, VotedForIn, Send
        <6> QED BY <6>1, <5>1, <5>2, <4>4, <3>1 DEF Phase2b, Send, AccInv, TypeOK, Messages
      <5>3. CASE a2 = a /\ (m.bal >= aBal[a])
        <6>1. (aBal[a2] = -1 => aVoted[a2] = {})'  BY <5>3, <4>4, <3>1 DEF AccInv, Phase2b, Send,
              TypeOK, Messages
        <6>2. (\A r \in aVoted[a2]: VotedForIn(a2, r.bal, r.slot, r.val) /\ r.bal =< aBal[a2])'
          <7> SUFFICES ASSUME NEW r \in (aVoted[a2])'
                       PROVE  (VotedForIn(a2, r.bal, r.slot, r.val) /\ r.bal =< aBal[a2])'
              OBVIOUS
          <7>1. VotedForIn(a2, r.bal, r.slot, r.val)'
            <8>1. CASE r \in aVoted[a2]
              <9>1. VotedForIn(a2, r.bal, r.slot, r.val)  BY <5>3, <4>4, <8>1 DEF AccInv
              <9> QED BY <9>1, Phase2bVotedForInv, <3>1, <4>4 DEF TypeOK, Messages
            <8>2. CASE r \in aVoted'[a2] \ aVoted[a2]
              <9> DEFINE m2 == [type |-> "2b", from |-> a, bal |-> m.bal, decrees |-> m.decrees]
              <9>1. m2 \in msgs' BY <5>1, <5>3, Send(m2) DEF Send
              <9>2. r.bal = m.bal /\ \E d \in m.decrees: r.slot = d.slot /\ r.val = d.val  BY <5>1, <5>3, <3>1, <8>2
              <9> QED BY <9>1, <9>2, <5>3 DEF Send, TypeOK, Messages, VotedForIn
            <8> QED BY <8>1, <8>2
          <7>2. (r.bal =< aBal[a2])'  BY <5>1, <5>3, <3>1, aBal[a] =< aBal'[a], r \in aVoted[a] => r.bal =< aBal'[a],
                aVoted'[a] = {d \in aVoted[a]: ~\E d2 \in m.decrees: d.slot = d2.slot} \cup
                             {[bal |-> m.bal, slot |-> d.slot, val |-> d.val]: d \in m.decrees},
                r \in aVoted'[a2] \ aVoted[a2] => r.bal = m.bal
               DEF AccInv, Send, TypeOK, Messages
          <7> QED BY <7>1, <7>2
        <6>3. (\A b \in Ballots, s \in Slots, v \in Values: VotedForIn(a2, b, s, v) => \E r \in aVoted[a2]: r.bal >= b /\ r.slot = s)'
          <7> SUFFICES ASSUME NEW b \in Ballots', NEW s \in Slots', NEW v \in Values', VotedForIn(a2, b, s, v)'
                       PROVE  (\E r\in aVoted[a2]: r.bal >= b /\ r.slot = s)'
              OBVIOUS
          <7>1. CASE VotedForIn(a2, b, s, v)
            <8>1. PICK r \in aVoted[a2]: r.bal >= b /\ r.slot = s  BY <7>1 DEF AccInv, TypeOK, Messages
            <8>2. m.bal >= b  BY <8>1, <5>3 DEF TypeOK, Messages, AccInv
            <8>3. CASE \E d \in m.decrees: d.slot = s
              <9>1. \E r2 \in aVoted'[a]: r2.bal = m.bal /\ r2.slot = s BY <5>1, <5>3,
                    aVoted'[a] = {d \in aVoted[a]: ~\E d2 \in m.decrees: d.slot = d2.slot} \cup
                    {[bal |-> m.bal, slot |-> d.slot, val |-> d.val]: d \in m.decrees}, <8>3 DEF TypeOK
              <9> QED BY <9>1, <5>3, <8>2
            <8>4. CASE ~ \E d \in m.decrees: d.slot = s  BY <8>4, <8>1, <5>1, <5>3, r \in aVoted'[a2]
            <8> QED BY <8>3, <8>4
          <7>2. CASE ~ VotedForIn(a2, b, s, v)
            <8>1. \E d \in m.decrees: d.slot = s  BY <5>1, <7>2 DEF Send, TypeOK, Messages, VotedForIn
            <8>2. \E r \in aVoted'[a2]: r.bal = m.bal /\ r.slot = s  BY <5>1, <8>1, <2>1, <5>3 DEF Send, TypeOK,
                  Messages
            <8>3. b = m.bal  BY <5>1, <7>2, <5>3 DEF VotedForIn, Send
            <8> QED BY <8>2, <8>3
          <7> QED BY <7>1, <7>2
        <6>4. (\A b \in Ballots, s \in Slots, v \in Values: b > MaxBallotInSlot(aVoted[a2], s) => ~ VotedForIn(a2, b, s, v))'
          <7> SUFFICES ASSUME NEW b \in Ballots', NEW s \in Slots', NEW v \in Values', (VotedForIn(a2, b, s, v))',
                              (b > MaxBallotInSlot(aVoted[a2], s))'
                       PROVE  FALSE
              OBVIOUS
          <7>1. ~\E d \in aVoted'[a2]: d.slot = s /\ d.bal > MaxBallotInSlot(aVoted[a2], s)'
                BY MBISNoMore, <3>1 DEF TypeOK
          <7> QED BY <7>1, <6>3, \E r \in aVoted'[a2]: r.bal >= b /\ r.slot = s, MBISType, <3>1 DEF Send,
              TypeOK, Messages
        <6> QED BY <6>1, <6>2, <6>3, <6>4
      <5> QED BY <5>2, <5>3
    <4>5. CASE \E p \in Proposers: Preempt(p)
      <5>1. \A a \in Acceptors, s \in Slots: MaxBallotInSlot(aVoted[a], s) = MaxBallotInSlot(aVoted[a], s)'
            BY <3>1, <4>5 DEF Preempt, MaxBallotInSlot
      <5> QED BY <4>5, <3>1, PreemptVotedForInv, <5>1 DEF AccInv, TypeOK, Preempt, Send
    <4>. QED BY <4>1, <4>2, <4>3, <4>4, <4>5, <2>1 DEF Next
  
  <3>3. MsgInv'
    <4>1. CASE \E p \in Proposers: Phase1a(p)  BY <4>1, Phase1aVotedForInv, <3>1, SafeAtStable, <2>1
         DEF Phase1a, MsgInv, Send, TypeOK, Messages, MsgInv1b, MsgInv2a, MsgInv2b
    <4>2. ASSUME NEW a \in Acceptors, Phase1b(a)  PROVE  MsgInv'
      <5>1. PICK m \in msgs: Phase1b(a)!(m)  BY <4>2 DEF Phase1b
      <5> DEFINE m1 == [type |-> "1b", from |-> a, bal |-> m.bal, voted |-> aVoted[a]]
      <5>2. (m1.bal =< aBal[m1.from])'  BY <5>1, <3>1 DEF Phase1b, Send, TypeOK, MsgInv, Messages
      <5>3. m1.voted = aVoted[m1.from]  BY <5>1, <3>1 DEF Phase1b, Send, TypeOK, Messages
      <5>4. (\A r \in m1.voted: VotedForIn(m1.from, r.bal, r.slot, r.val))'
            BY <5>1, <4>2, Phase1bVotedForInv, <3>1, <5>3 DEF TypeOK, Messages, AccInv
      <5>5. (\A b \in Ballots, s \in Slots, v \in Values: b > MaxBallotInSlot(m1.voted, s) => ~VotedForIn(m1.from, b, s, v))'
            BY Phase1bVotedForInv, <4>2, <5>3, <5>1, <3>2, <3>1 DEF AccInv, MsgInv, Send, TypeOK, Messages
      <5>6. \A s \in Slots: MaxBallotInSlot(m1.voted, s) \in Ballots \cup {-1}  BY <3>1, MBISType DEF TypeOK, Messages
      <5>7. \A s \in Slots : MaxBallotInSlot(m1.voted, s)+1 \in Ballots
        <6> SUFFICES ASSUME NEW s \in Slots  PROVE  MaxBallotInSlot(m1.voted, s)+1 \in Ballots OBVIOUS
        <6>1. CASE MaxBallotInSlot(m1.voted, s) = -1 BY <6>1
        <6>2. CASE MaxBallotInSlot(m1.voted, s) \in Ballots BY \A x \in Ballots : x+1 \in Ballots, <6>2
        <6> QED BY <6>1, <6>2, <5>6
      <5>8. \A s \in Slots : MaxBallotInSlot(m1.voted, s)+1 > MaxBallotInSlot(m1.voted, s)
        <6> SUFFICES ASSUME NEW s \in Slots  PROVE  MaxBallotInSlot(m1.voted, s)+1 > MaxBallotInSlot(m1.voted, s)
          OBVIOUS
        <6>1. CASE MaxBallotInSlot(m1.voted, s) = -1 BY <6>1
        <6>2. CASE MaxBallotInSlot(m1.voted, s) \in Ballots BY \A x \in Ballots : x+1 > x, <6>2
        <6> QED BY <6>1, <6>2, <5>6
      <5>9. m1.bal \in Ballots  BY <3>1 DEF TypeOK, Messages
      <5>10. (\A s \in Slots, b \in Ballots : b \in MaxBallotInSlot(m1.voted, s)+1..m1.bal-1 =>
                b > MaxBallotInSlot(m1.voted, s))
        <6> SUFFICES ASSUME NEW s \in Slots, NEW b \in Ballots, b \in MaxBallotInSlot(m1.voted, s)+1..m1.bal-1
                     PROVE  b > MaxBallotInSlot(m1.voted, s) OBVIOUS
          <6> HIDE DEF m1
          <6> DEFINE x == MaxBallotInSlot(m1.voted, s)
          <6> DEFINE y == m1.bal-1
          <6>1. x \in Ballots \cup {-1} BY <5>6
          <6>2. y \in Ballots \cup {-1} BY <5>9
          <6> HIDE DEF x, y
          <6>3. CASE x+1 > y
            <7>1. \A e \in Ballots : e \notin x+1..y BY <6>3, <6>1, <6>2
            <7> QED BY <6>3, <7>1 DEF x, y
          <6>4. CASE x+1 = y BY <6>4, <5>7, <5>8, <5>9, <3>1, <6>2 DEF x, y
          <6>5. CASE x+1 < y
            <7>1. \A e \in Ballots : e \in x+1..y => e > x BY <6>5, <6>1, <6>2
            <7>2. b \in x+1..y BY DEF x, y
            <7>3. b > x BY <7>2, <7>1
            <7> QED BY <7>3 DEF x
        <6> QED BY <6>1, <6>2, <6>3, <6>4, <6>5
      <5>11. (\A s \in Slots, b \in Ballots : b \in MaxBallotInSlot(m1.voted, s)+1..m1.bal-1 =>
                b > MaxBallotInSlot(m1.voted, s))'
        BY <5>10, <5>1
      <5>12. (\A b \in Ballots, s \in Slots, v \in Values: b \in MaxBallotInSlot(m1.voted, s)+1..m1.bal-1 =>
                ~VotedForIn(m1.from, b, s, v))'
        <6> SUFFICES ASSUME NEW s \in Slots', NEW v \in Values', NEW b \in Ballots'
                     PROVE  (b \in MaxBallotInSlot(m1.voted, s)+1..m1.bal-1 =>
                                ~ VotedForIn(m1.from, b, s, v))'
          OBVIOUS
        <6>1. CASE ~ \E x \in Ballots : x \in (MaxBallotInSlot(m1.voted, s)+1..m1.bal-1)' BY <6>1
        <6>2. CASE \E x \in Ballots : x \in (MaxBallotInSlot(m1.voted, s)+1..m1.bal-1)' BY <6>2, <5>5, <5>11, <5>8, <5>7
        <6> QED BY <6>1, <6>2
      <5>13. CASE m.bal > aBal[a]
        <6> SUFFICES ASSUME NEW m2 \in msgs'
                     PROVE  (/\ (m2.type = "1b") => MsgInv1b(m2)
                             /\ (m2.type = "2a") => MsgInv2a(m2)
                             /\ (m2.type = "2b") => MsgInv2b(m2))'
            BY DEF MsgInv
        <6>1. ((m2.type = "1b") => MsgInv1b(m2))'
          <7>1. CASE m2 \in msgs  BY <7>1, <5>8, <5>1, Phase1bVotedForInv, <4>2 DEF MsgInv, MsgInv1b,
                TypeOK, Messages
          <7>2. CASE m2 \in msgs' \ msgs
            <8>1. m2 = m1  BY <5>1, <7>2, <5>13 DEF Send
            <8> QED BY <7>2, <5>13, Phase1bVotedForInv, <4>2, <5>2, <5>4, <5>12, <5>1, <3>1, <2>1,
                <8>1 DEF Send, TypeOK, MsgInv, Messages, MsgInv1b
          <7> QED BY <7>1, <7>2
        <6>2. ((m2.type = "2a" => MsgInv2a(m2)) /\ (m2.type = "2b" => MsgInv2b(m2)))'
              BY <5>8, Phase1bVotedForInv, <5>1, <4>2, <3>1, SafeAtStable, <2>1 DEF Send, TypeOK,
              MsgInv, Messages, MsgInv2a, MsgInv2b
        <6> QED BY <6>1, <6>2
      <5>14. CASE ~ (m.bal > aBal[a]) BY <5>14, Phase1bVotedForInv, <4>2, <5>2, <5>4, <5>12, <5>1,
             SafeAtStable, <3>1, <2>1 DEF Send, TypeOK, MsgInv, Messages, MsgInv1b, MsgInv2a, MsgInv2b
      <5> QED BY <5>13, <5>14
    <4>3. ASSUME NEW p \in Proposers, Phase2a(p)  PROVE  MsgInv'
      <5> SUFFICES ASSUME NEW m \in msgs'
                   PROVE  (/\ (m.type = "1b") => MsgInv1b(m)
                           /\ (m.type = "2a") => MsgInv2a(m)
                           /\ (m.type = "2b") => MsgInv2b(m))'
          BY DEF MsgInv
      <5> DEFINE b == pBal[p]
      <5>1. PICK Q \in Quorums, S \in SUBSET {m2 \in msgs: (m2.type = "1b") /\ (m2.bal = b)}:
              /\\A a \in Q: \E m2\in S: m2.from = a
              /\Send([type |-> "2a", bal |-> b, from |-> p, decrees |-> PropSV(UNION {m2.voted: m2 \in S})])
            BY <4>3 DEF Phase2a
      <5>2. b = pBal'[p] /\ b \in Ballots  BY <4>3 DEF Phase2a, TypeOK
      <5>3. \A m2 \in msgs' \ msgs: m2.type = "2a" /\ m2.bal = b  BY <5>1 DEF Send
      <5>4. ((m.type = "1b") => MsgInv1b(m))'
        <6> SUFFICES ASSUME (m.type = "1b")'  PROVE  MsgInv1b(m)'
            OBVIOUS 
        <6>1. (m.bal =< aBal[m.from])'  BY <4>3, <5>3, <3>1, Phase2aVotedForInv DEF TypeOK, Messages,
              MsgInv, Phase2a, MsgInv1b
        <6>2. (\A r \in m.voted: VotedForIn(m.from, r.bal, r.slot, r.val))'  BY <4>3, <5>3, <3>1,
              Phase2aVotedForInv DEF TypeOK, Messages, MsgInv, MsgInv1b
        <6>3. \A s \in Slots: MaxBallotInSlot(m.voted, s) = MaxBallotInSlot(m.voted, s)'  BY DEF MaxBallotInSlot
        <6>4. (\A b2 \in Ballots, s \in Slots, v \in Values: b2 \in MaxBallotInSlot(m.voted, s)+1..m.bal-1 =>
                 ~ VotedForIn(m.from, b2, s, v))'
              BY <4>3, <5>3, <3>1, Phase2aVotedForInv, <6>3 DEF TypeOK, Messages, MsgInv, MsgInv1b
        <6> QED BY <6>1, <6>2, <6>4 DEF MsgInv1b
      <5>5. ((m.type = "2a") => MsgInv2a(m))'
        <6> SUFFICES ASSUME (m.type = "2a")'  PROVE  MsgInv2a(m)'
            OBVIOUS
        <6> DEFINE VS == UNION {m2.voted: m2 \in S}
        <6>1. \A a \in Q: aBal[a] >= b  BY <5>1, <3>2, <3>1 DEF MsgInv, TypeOK, Messages, MsgInv1b
        <6>2. (\A d \in m.decrees: SafeAt(m.bal, d.slot, d.val))'
          <7>1. \A d \in [slot: UnusedS(VS), val: Values]: SafeAt(b, d.slot, d.val)
            <8> SUFFICES ASSUME NEW d \in [slot: UnusedS(VS), val: Values]  PROVE  SafeAt(b, d.slot, d.val)
                OBVIOUS
            <8>1. \A m2 \in S: ~\E d2 \in m2.voted: d.slot = d2.slot  BY DEF UnusedS
            <8>2. \A m2 \in S: MaxBallotInSlot(m2.voted, d.slot) + 1 = 0  BY <8>1 DEF MaxBallotInSlot
            <8>3. \A m2 \in S, b2 \in Ballots, s \in Slots, v \in Values: b2 \in MaxBallotInSlot(m2.voted, s) + 1..m2.bal - 1 =>
                    ~VotedForIn(m2.from, b2, s, v)  BY DEF MsgInv, MsgInv1b
            <8>4. \A v \in Values, b2 \in Ballots, a \in Q: b2 \in 0..b-1 => ~VotedForIn(a, b2, d.slot, v)
                  BY <5>1, <8>2, <8>3 DEF UnusedS, TypeOK, Messages
            <8> QED BY <8>4, <3>1, <6>1 DEF SafeAt, NewSV, UnusedS, WontVoteIn, TypeOK, Messages
          <7>2. \A d \in [slot: UnusedS(VS), val: Values]: SafeAt(b, d.slot, d.val)'  BY <7>1, SafeAtStable,
                <3>1, <2>1, <5>2 DEF NewSV, UnusedS, TypeOK, Messages
          <7>3. \A d \in NewSV(VS): SafeAt(b, d.slot, d.val)'  BY <7>2, NPC DEF NewSV
          <7>4. \A d \in MaxBSV(VS): SafeAt(b, d.slot, d.val)
            <8> SUFFICES ASSUME NEW d \in MaxBSV(VS), NEW b2 \in Ballots, b2 \in 0..(b-1)
                         PROVE  \E Q2\in Quorums: \A a \in Q2:
                                  VotedForIn(a, b2, d.slot, d.val) \/ WontVoteIn(a, b2, d.slot)
                BY DEF SafeAt
            <8> DEFINE max == MaxBallotInSlot(VS, d.slot)
            <8> USE DEF MaxBSV
            <8>1. max \in Ballots  BY MBISType, MBISNoSlot DEF TypeOK, Messages
            <8>2. \A m2 \in S: MaxBallotInSlot(m2.voted, d.slot) =< max
                  BY \A m2 \in S: m2.voted \subseteq VS, MBISSubsets DEF MaxBSV, TypeOK, Messages
            <8>3. ~\E d2 \in VS: (d2.bal > d.bal /\ d2.slot = d.slot)
                  BY \A d2 \in VS: ~(~(d2.bal =< d.bal) /\ d2.slot = d.slot) DEF MaxBSV, TypeOK, Messages
            <8>4. VS \in SUBSET [bal: Ballots, slot: Slots, val: Values]  BY <3>1 DEF TypeOK, Messages
            <8>5. max = d.bal
              <9> SUFFICES ASSUME max # d.bal  PROVE  FALSE
                  OBVIOUS
              <9>1. CASE max > d.bal
                <10> HIDE DEF VS
                <10>1. \E d2\in VS: d2.bal = max /\ d2.slot = d.slot  BY <8>4, <8>1, MBISExists
                <10> QED BY <10>1, <8>3, <9>1
              <9>2. CASE max < d.bal  BY MBISNoMore, <9>2 DEF MaxBSV, TypeOK, Messages
              <9> QED BY <9>1, <9>2, <8>1 DEF Ballots, TypeOK, Messages
            <8>6. CASE b2 \in max+1..b-1
              <9> HIDE DEF max
              <9>1. \A m2 \in S, b3 \in Ballots, v \in Values: b3 \in MaxBallotInSlot(m2.voted, d.slot)+1..b-1 =>
                      ~VotedForIn(m2.from, b3, d.slot, v)
                    BY DEF MsgInv, TypeOK, Messages, MsgInv1b
              <9>2. \A m2 \in S, v \in Values: ~VotedForIn(m2.from, b2, d.slot, v)
                    BY <8>6, <9>1, <8>2, <8>1, MBISType DEF TypeOK, Messages, Send
              <9> QED BY <5>1, <8>6, <6>1, <9>2 DEF MsgInv, MsgInv1b, TypeOK, Messages, WontVoteIn,
                  MaxBSV
            <8>7. CASE b2 = max
                <9>1. \E a \in Acceptors, m2 \in S: m2.from = a /\ \E d2 \in m2.voted:
                        d2.bal = d.bal /\ d2.slot = d.slot /\ d2.val = d.val
                      BY DEF MaxBallotInSlot, TypeOK, Messages
                <9>2. \E a \in Acceptors: VotedForIn(a, b2, d.slot, d.val)
                      BY <8>7, <9>1, <8>5 DEF MsgInv, TypeOK, Messages, MsgInv1b
                <9>3. \A q \in Q, v2 \in Values: VotedForIn(q, b2, d.slot, v2) => v2 = d.val
                      BY <9>2, VotedOnce, QuorumAssumption DEF TypeOK, Messages
                <9>4. \A q \in Q: aBal[q] > b2  BY <5>1 DEF MsgInv, TypeOK, Messages, MsgInv1b
                <9> QED BY <8>7, <9>3, <9>4 DEF WontVoteIn
            <8>8. CASE b2 \in 0..max-1
                <9>1. \E a \in Acceptors: VotedForIn(a, d.bal, d.slot, d.val)
                      BY <8>8,<8>2 DEF MsgInv, TypeOK, Messages, MsgInv1b
                <9>2. SafeAt(d.bal, d.slot, d.val)  BY <9>1, VotedInv DEF TypeOK, Messages
                <9> QED BY <8>8, <9>2, <8>5 DEF SafeAt, MsgInv, TypeOK, Messages, MaxBallotInSlot
            <8> QED BY <8>6, <8>7, <8>8, <8>1
          <7>5. MaxBSV(VS) \in SUBSET [bal: Ballots, slot: Slots, val: Values]  BY DEF MaxBSV, TypeOK, Messages
          <7>6. \A d \in MaxBSV(VS): SafeAt(b, d.slot, d.val)'  BY <7>4, SafeAtStable, <3>1, <7>5, <2>1, <5>2
          <7>7. \A d \in MaxSV(VS): SafeAt(b, d.slot, d.val)'  BY <7>6, <7>5 DEF MaxSV
          <7>8. \A d \in MaxSV(VS) \cup NewSV(VS): SafeAt(b, d.slot, d.val)'  BY <7>7, <7>3
          <7>9. (\A m2 \in msgs: m2.type = "2a" => \A d \in m2.decrees: SafeAt(m2.bal, d.slot, d.val))'
            <8> SUFFICES ASSUME NEW m2 \in msgs', (m2.type = "2a")', NEW d \in m2.decrees
                         PROVE  (SafeAt(m2.bal, d.slot, d.val))'
                OBVIOUS
            <8>1. CASE m2 \in msgs  BY <3>1, SafeAtStable, <8>1, <2>1 DEF MsgInv, MsgInv2a, Messages, TypeOK
            <8>2. CASE m2 \in msgs' \ msgs
              <9>1. SafeAt(m2.bal, d.slot, d.val)'  BY <7>8, <8>2, <5>1, <5>2 DEF Send, PropSV
              <9> QED BY <3>1, <9>1 DEF Send, TypeOK, Messages
            <8> QED BY <8>1, <8>2
          <7> QED BY <7>9
        <6>3. (\A d1,d2 \in m.decrees: d1.slot = d2.slot => d1 = d2)'
          <7>1. \A m2 \in msgs' \ msgs: \A d1,d2 \in m2.decrees: d1.slot = d2.slot => d1 = d2
            <8>1. VS \in SUBSET [bal: Ballots, slot: Slots, val: Values]  BY DEF Messages, TypeOK
            <8>2. \A r1, r2 \in MaxBSV(VS): r1.slot = r2.slot => r1.bal = r2.bal  BY <8>1 DEF MaxBSV
            <8>3. MaxBSV(VS) \subseteq VS  BY <8>1 DEF MaxBSV
            <8>4. \A r1, r2 \in MaxBSV(VS): r1.bal = r2.bal /\ r1.slot = r2.slot => r1.val = r2.val
                  BY <8>3, VotedUnion
            <8>5. \A r1, r2 \in MaxBSV(VS): r1.slot = r2.slot => r1.bal = r2.bal /\ r1.val = r2.val
                  BY <8>4, <8>2, <8>3, <8>1
            <8>6. \A r1, r2 \in MaxSV(VS): r1.slot = r2.slot => r1 = r2  BY <8>5 DEF MaxSV
            <8> QED BY <8>6, NPC, <5>1 DEF PropSV, Send
          <7> QED BY <7>1 DEF MsgInv, MsgInv2a
        <6>4. (\A m2 \in msgs: (m2.type = "2a" /\ m2.bal = m.bal) => (m2 = m))'
          <7>1. \A m2 \in msgs: (m2.type = "2a") => (m2.bal # b)  BY <4>3 DEF Phase2a
          <7>2. \A m1, m2 \in msgs' \ msgs: m1 = m2  BY <4>3 DEF Phase2a, Send
          <7> QED BY <7>1, <7>2, <5>3, <2>1, <3>1 DEF MsgInv, MsgInv2a
        <6> QED BY <6>2, <6>3, <6>4 DEF MsgInv2a
      <5>6. ((m.type = "2b") => MsgInv2b(m))'  BY <5>3, <5>1, m.type = "2b" => m \in msgs,
            <3>1, <4>3 DEF TypeOK, Messages, MsgInv, Phase2a, Send, MsgInv2b
      <5> QED BY <5>4, <5>5, <5>6
    <4>4. ASSUME NEW a \in Acceptors, Phase2b(a)  PROVE  MsgInv'
      <5> SUFFICES ASSUME NEW m \in msgs'
                   PROVE  (/\ (m.type = "1b") => MsgInv1b(m)
                           /\ (m.type = "2a") => MsgInv2a(m)
                           /\ (m.type = "2b") => MsgInv2b(m))'
          BY DEF MsgInv
      <5>1. PICK m1 \in msgs: Phase2b(a)!(m1)  BY <4>4 DEF Phase2b
      <5>2. ((m.type = "1b") => MsgInv1b(m))'
        <6> SUFFICES ASSUME (m.type = "1b")'  PROVE  MsgInv1b(m)'
            OBVIOUS
        <6>1. (m.bal =< aBal[m.from] /\ \A r \in m.voted: VotedForIn(m.from, r.bal, r.slot, r.val))'
              BY <5>1, <3>1, <4>4, Phase2bVotedForInv DEF MsgInv, MsgInv1b, TypeOK,
              Messages, Send
        <6>2. (\A b \in Ballots, s \in Slots, v \in Values: b \in MaxBallotInSlot(m.voted, s)+1..m.bal-1 =>
                 ~ VotedForIn(m.from, b, s, v))'
          <7> SUFFICES ASSUME NEW b \in Ballots', NEW s \in Slots', NEW v \in Values',
                              (b \in MaxBallotInSlot(m.voted, s)+1..m.bal-1)'
                       PROVE  (~ VotedForIn(m.from, b, s, v))'
              OBVIOUS
          <7>1. ~ VotedForIn(m.from, b, s, v)  BY <5>1 DEF Send, MsgInv, TypeOK, Messages, MsgInv1b
          <7>2. CASE m.from # a \/ ~(m1.bal >= aBal[a])  BY <5>1, <3>1, <7>2, <7>1 DEF VotedForIn,
                 TypeOK, Messages, Send
          <7>3. CASE m.from = a /\ (m1.bal >= aBal[a])
            <8>1. \A m2 \in msgs' \ msgs: m2.bal = m1.bal  BY <5>1, <7>3, <6>1, <7>3 DEF Send, TypeOK
            <8>2. \A m2 \in msgs' \ msgs: m2.bal # b  BY <5>1, <7>3, <6>1, <7>3, <8>1 DEF TypeOK, Messages
            <8> QED BY <7>3, <7>1, <8>2 DEF VotedForIn, TypeOK, Messages          
          <7> QED BY <7>2, <7>3 DEF TypeOK, Messages
        <6> QED BY <6>1, <6>2 DEF MsgInv1b
      <5>3. ((m.type = "2a") => MsgInv2a(m))'  BY SafeAtStable, <3>1, <4>4, <2>1 DEF MsgInv, MsgInv2a,
            TypeOK, Messages, Phase2b, Send
      <5>4. ((m.type = "2b") => MsgInv2b(m))'
        <6>1. CASE ~ (m1.bal >= aBal[a]) \/ m \in msgs  BY <5>1, <3>1, <6>1 DEF TypeOK, Messages,
               Send, MsgInv, MsgInv2b
        <6>2. CASE m1.bal >= aBal[a] /\ m \in msgs' \ msgs  BY <5>1, <3>1, <6>2 DEF TypeOK, Send, MsgInv2b
        <6> QED BY <6>1, <6>2
      <5> QED BY <5>2, <5>3, <5>4 DEF MsgInv2b
    <4>5. CASE \E p \in Proposers: Preempt(p)  BY <4>5, PreemptVotedForInv, <3>1, SafeAtStable,
           <2>1 DEF Preempt, MsgInv, TypeOK, Messages, MsgInv1b, MsgInv2a, MsgInv2b
    <4> QED BY <4>1, <4>2, <4>3, <4>4, <4>5, <2>1 DEF Next
  <3> QED BY <3>1, <3>2, <3>3 DEF Inv, vars, Next
  <2>2. CASE UNCHANGED vars  BY <2>2 DEF vars, Inv, TypeOK, AccInv, MsgInv, VotedForIn,
         SafeAt, WontVoteIn, MaxBallotInSlot, MsgInv1b, MsgInv2a, MsgInv2b
  <2> QED BY <2>1, <2>2
<1> QED BY <1>1, <1>2, PTL DEF Spec

THEOREM Consistent == Spec => []Consistency
<1> USE DEF Ballots
<1>1. Inv => Consistency
  <2> SUFFICES ASSUME Inv, NEW v1 \in Values,  NEW v2 \in Values, NEW s \in Slots, NEW b1 \in Ballots, NEW b2 \in Ballots,
                      ChosenIn(b1, s, v1), ChosenIn(b2, s, v2), b1 =< b2
               PROVE  v1 = v2
      BY DEF Consistency, Chosen
  <2>1. CASE b1 = b2
    <3>1. \E a \in Acceptors: VotedForIn(a, b1, s, v1) /\ VotedForIn(a, b1, s, v2)
          BY <2>1, QuorumAssumption DEF ChosenIn
    <3> QED BY <3>1, VotedOnce DEF Inv
  <2>2. CASE b1 < b2
    <3>1. SafeAt(b2, s, v2)  BY VotedInv, QuorumAssumption DEF ChosenIn, Inv
    <3>2. PICK Q1 \in Quorums: \A a \in Q1: VotedForIn(a, b1, s, v1)  BY DEF ChosenIn
    <3>3. PICK Q2 \in Quorums: \A a \in Q2: VotedForIn(a, b1, s, v2) \/ WontVoteIn(a, b1, s)  BY <3>1, <2>2 DEF SafeAt
    <3> QED BY <3>2, <3>3, QuorumAssumption, VotedOnce, Z3 DEF WontVoteIn, Inv
  <2> QED BY <2>1, <2>2
<1> QED BY Invariant, <1>1, PTL
=============
