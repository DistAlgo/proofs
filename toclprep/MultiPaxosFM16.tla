------------------------------- MODULE MultiPaxosFM16 -------------------------------
(***************************************************************************)
(* This is a TLA+ specification of the MultiPaxos Consensus algorithm,     *)
(* described in                                                            *)
(*                                                                         *)
(*  The Part-Time Parliament:                                              *)
(*  http://research.microsoft.com/en-us/um/people/lamport/pubs/lamport-paxos.pdf *)
(*                                                                         *)
(* and a TLAPS-checked proof of its correctness. This is an extension of   *)
(* the proof of Basic Paxos found in TLAPS examples directory.             *)
(***************************************************************************)
EXTENDS Integers, TLAPS, TLC, FiniteSets, Sequences

CONSTANTS Acceptors, Values, Quorums, Proposers

ASSUME QuorumAssumption == 
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

(***************************************************************************)
(* The following lemma is an immediate consequence of the assumption.      *)
(***************************************************************************)
LEMMA QuorumNonEmpty == \A Q \in Quorums : Q # {}
BY QuorumAssumption

Ballots == Nat
Slots == Nat

VARIABLES msgs,             \* The set of messages that have been sent.
          acceptorVoted,    \* The sets of <ballot, slot, value> triples
                            \* per acceptor that it has VotedForIn.
          acceptorMaxBal    \* For each acceptor, the highest ballot seen
                            \* by it.

vars == <<msgs, acceptorVoted, acceptorMaxBal>>

Send(m) == msgs' = msgs \cup {m}

None == CHOOSE v : v \notin Values

Init == /\ msgs = {}
        /\ acceptorVoted = [a \in Acceptors |-> {}]
        /\ acceptorMaxBal = [a \in Acceptors |-> -1]

(***************************************************************************)
(* Phase 1a: Executed by a proposer, it selects a ballot number on which   *)
(* Phase 1a has never been initiated. This number is sent to any set of    *)
(* acceptors which contains at least one quorum from Quorums. Trivially it *)
(* can be broadcasted to all Acceptors. For safety, any subset of          *)
(* Acceptors would suffice. For liveness, a subset containing at least one *)
(* Quorum is needed.                                                       *)
(***************************************************************************)
Phase1a(b) == /\ ~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b)
              /\ Send([type |-> "1a", bal |-> b])
              /\ UNCHANGED <<acceptorVoted, acceptorMaxBal>>
              
(***************************************************************************)
(* Phase 1b: If an acceptor receives a 1a message with ballot b greater    *)
(* than that of any 1a message to which it has already responded, then it  *)
(* responds to the request with a promise not to accept any more proposals *)
(* for ballots numbered less than b; otherwise it sends a preempt to the   *)
(* proposer telling the greater ballot.                                    *)
(* In case of a 1b reply, the acceptor writes a mapping in S -> B \times V *)
(* This This mapping reveals for each slot, the value that the acceptor    *)
(* most recently (i.e., highest ballot) voted on, if any.                  *)
(***************************************************************************)
Phase1b(a) == 
  \E m \in msgs : 
     /\ m.type = "1a"
     /\ m.bal > acceptorMaxBal[a]
     /\ Send([type |-> "1b", bal |-> m.bal, from |-> a, voted |-> acceptorVoted[a]])
     /\ acceptorMaxBal' = [acceptorMaxBal EXCEPT ![a] = m.bal]
     /\ UNCHANGED <<acceptorVoted>>
        
(***************************************************************************)
(* Phase 2a: If the proposer receives a response to its 1b message (for    *)
(* ballot b) from a quorum of acceptors, then it sends a 2a message to all *)
(* acceptors for a proposal in ballot b. Per slot received in the replies, *)
(* the proposer finds out the value most recently (i.e., highest ballot)   *)
(* voted by the acceptors in the received set. Thus a mapping in S -> V    *)
(* is created. This mapping along with the ballot that passed Phase 1a is  *)
(* propogated to again, any subset of Acceptors - Hopefully to one         *)
(* containing at least one Quorum.                                         *)
(* Bmax            creates the desired mapping from received replies.      *)
(* NewProposals    instructs how new slots are entered in the system.      *)
(***************************************************************************)
PartialBmax(T) ==
  {t \in T : \A t1 \in T : t1.slot = t.slot => t1.bal =< t.bal}

Bmax(T) ==
  {[slot |-> t.slot, val |-> t.val] : t \in PartialBmax(T)}

FreeSlots(T) ==
  {s \in Slots : ~ \E t \in T : t.slot = s}

NewProposals(T) ==
  (CHOOSE D \in SUBSET [slot : FreeSlots(T), val : Values] \ {}:
    \A d1, d2 \in D : d1.slot = d2.slot => d1 = d2)

ProposeDecrees(T) ==
  Bmax(T) \cup NewProposals(T)

LEMMA NPC ==
  \A S : /\ NewProposals(S) \in (SUBSET [slot : FreeSlots(S), val : Values]) \ {}
         /\ \A t1, t2 \in NewProposals(S) : t1.slot = t2.slot => t1 = t2
         /\ ~ \E t1 \in Bmax(S), t2 \in NewProposals(S) : t1.slot = t2.slot
  <1> SUFFICES ASSUME NEW S
               PROVE  /\ NewProposals(S) \in (SUBSET [slot : FreeSlots(S), val : Values]) \ {}
                      /\ \A t1, t2 \in NewProposals(S) : t1.slot = t2.slot => t1 = t2
                      /\ ~ \E t1 \in Bmax(S), t2 \in NewProposals(S) : t1.slot = t2.slot
    OBVIOUS
  <1>0. \E T \in (SUBSET [slot : FreeSlots(S), val : Values]) \ {} :
      \A t1, t2 \in T : t1.slot = t2.slot => t1 = t2
    BY DEF FreeSlots
  <1>1. NewProposals(S) \in (SUBSET [slot : FreeSlots(S), val : Values]) \ {}
    BY <1>0 DEF NewProposals
  <1>2. \A t1, t2 \in NewProposals(S) : t1.slot = t2.slot => t1 = t2
    BY <1>0 DEF NewProposals
  <1>3. ~ \E t1 \in Bmax(S), t2 \in ([slot : FreeSlots(S), val : Values] \ {}) : t1.slot = t2.slot
    BY DEF Bmax, PartialBmax, FreeSlots
  <1>4. QED
    BY <1>1, <1>2, <1>3

Phase2a(b) ==
  /\ ~ \E m \in msgs : (m.type = "2a") /\ (m.bal = b)
  /\ \E Q \in Quorums :
        \E S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = b)} :
           /\ \A a \in Q : \E m \in S : m.from = a
           /\ Send([type |-> "2a", bal |-> b, decrees |-> ProposeDecrees(UNION {m.voted : m \in S})])
  /\ UNCHANGED <<acceptorMaxBal, acceptorVoted>>

(***************************************************************************)
(* Phase 2b: If an acceptor receives a 2a message for a ballot which is    *)
(* the highest that it has seen, it votes for the all the message's values *)
(* in ballot b.                                                            *)
(***************************************************************************)
Phase2b(a) == 
  \E m \in msgs :
    /\ m.type = "2a"
    /\ m.bal >= acceptorMaxBal[a]
    /\ Send([type |-> "2b", bal |-> m.bal, decrees |-> m.decrees, from |-> a])
    /\ acceptorMaxBal' = [acceptorMaxBal EXCEPT ![a] = m.bal]
    /\ acceptorVoted' = [acceptorVoted EXCEPT ![a] = 
                    {d \in acceptorVoted[a] : ~ \E d1 \in m.decrees : d.slot = d1.slot } \cup
                    {[bal |-> m.bal, slot |-> d.slot, val |-> d.val] : d \in m.decrees}]
    
Next == \/ \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars       
-----------------------------------------------------------------------------
(***************************************************************************)
(* How a value is chosen:                                                  *)
(*                                                                         *)
(* This spec does not contain any actions in which a value is explicitly   *)
(* chosen (or a chosen value learned).  What it means for a value to be    *)
(* chosen is defined by the operator Chosen, where Chosen(v, s) means that *)
(* v has been chosen for slot s.                                           *)
(***************************************************************************)
VotedForIn(a, v, b, s) ==
  \E m \in msgs : /\ m.type = "2b"
                  /\ m.bal = b
                  /\ m.from = a
                  /\ \E d \in m.decrees : d.slot = s /\ d.val = v

ChosenIn(v, b, s) == \E Q \in Quorums :
                     \A a \in Q : VotedForIn(a, v, b, s)

Chosen(v, s) == \E b \in Ballots : ChosenIn(v, b, s)

(***************************************************************************)
(* The consistency condition that a consensus algorithm must satisfy is    *)
(* the invariance of the following state predicate Consistency.            *)
(***************************************************************************)
Consistency == \A v1, v2 \in Values, s \in Slots : Chosen(v1, s) /\ Chosen(v2, s) => (v1 = v2)
-----------------------------------------------------------------------------
(***************************************************************************)
(* This section of the spec defines the invariant Inv.                     *)
(***************************************************************************)
Messages ==      [type : {"1a"}, bal : Ballots, from : Proposers]
            \cup [type : {"1b"}, bal : Ballots, voted : SUBSET [bal : Ballots, slot : Slots, val : Values], from : Acceptors]
            \cup [type : {"2a"}, bal : Ballots, decrees : SUBSET [slot : Slots, val : Values], from : Proposers]
            \cup [type : {"2b"}, bal : Ballots, from : Acceptors, decrees : SUBSET [slot : Slots, val : Values]]

TypeOK == /\ msgs \in SUBSET Messages
          /\ acceptorVoted \in [Acceptors -> SUBSET [bal : Ballots, slot : Slots, val : Values]]
          /\ acceptorMaxBal \in [Acceptors -> Ballots \cup {-1}]
          /\ \A a \in Acceptors: \A r \in acceptorVoted[a] : acceptorMaxBal[a] >= r.bal

(***************************************************************************)
(* WontVoteIn(a, b, s) is a predicate that implies that a has not voted    *)
(* and never will vote in ballot b wrt slot s.                             *)
(***************************************************************************)                                       
WontVoteIn(a, b, s) == /\ \A v \in Values : ~ VotedForIn(a, v, b, s)
                       /\ acceptorMaxBal[a] > b

(***************************************************************************)
(* The predicate SafeAt(v, b, s) implies that no value other than perhaps  *)
(* v has been or ever will be chosen in any ballot numbered less than b    *)
(* for slot s.                                                             *)
(***************************************************************************)                   
SafeAt(v, b, s) == 
  \A c \in 0..(b-1) :
    \E Q \in Quorums : 
      \A a \in Q : VotedForIn(a, v, c, s) \/ WontVoteIn(a, c, s)

(***************************************************************************)
(* Maximum(S) picks the largest element in the set S.                      *)
(***************************************************************************)
Maximum(B) ==
  CHOOSE b \in B : \A b2 \in B : b >= b2

AXIOM MaxInSet ==
  \A S \in (SUBSET Nat) \ {}: Maximum(S) \in S

AXIOM MaxOnNat ==
  \A S \in SUBSET Nat :
  ~ \E s \in S : Maximum(S) < s
  
LEMMA MaxOnNatS ==
  \A S1, S2 \in (SUBSET Nat) \ {}: S1 \subseteq S2 =>
    Maximum(S1) =< Maximum(S2)
  BY MaxOnNat, MaxInSet

(***************************************************************************)
(* MaxVotedBallotInSlot(voted, s) picks the highest ballot in voted for    *)
(* slot s.                                                                 *)
(***************************************************************************)
MaxVotedBallotInSlot(D, s) ==
  LET B == {d.bal : d \in {d \in D : d.slot = s}} IN
  IF {d \in D : d.slot = s} = {} THEN -1
  ELSE Maximum(B)

LEMMA MVBISType ==
\A S \in SUBSET [bal : Ballots, slot : Slots, val : Values], 
   s \in Slots: MaxVotedBallotInSlot(S, s) \in Ballots \cup {-1}
    BY MaxInSet DEF MaxVotedBallotInSlot

LEMMA MVBISSubsets ==
\A S1, S2 \in SUBSET [bal : Ballots, slot : Slots, val : Values]:
    S1 \subseteq S2
    =>
    \A s \in Slots: MaxVotedBallotInSlot(S1, s) =< MaxVotedBallotInSlot(S2, s)
  <1> SUFFICES ASSUME NEW S1 \in SUBSET [bal : Ballots, slot : Slots, val : Values],
                      NEW S2 \in SUBSET [bal : Ballots, slot : Slots, val : Values],
                      S1 \subseteq S2,
                      NEW s \in Slots
               PROVE  MaxVotedBallotInSlot(S1, s) =< MaxVotedBallotInSlot(S2, s)
    OBVIOUS
  <1>3. {d.bal : d \in {d \in S1 : d.slot = s}} \subseteq {d.bal : d \in {d \in S2 : d.slot = s}}
    OBVIOUS
  <1>1. CASE ~ \E d \in S1 : d.slot = s
    <2>1. MaxVotedBallotInSlot(S1, s) = -1
      BY <1>1 DEF MaxVotedBallotInSlot
    <2> QED BY <2>1, MVBISType DEF Ballots
  <1>2. CASE \E d \in S1 : d.slot = s
    <2>1. CASE ~ \E d \in S2 \ S1 : d.slot = s
      <3>1. MaxVotedBallotInSlot(S1, s) = MaxVotedBallotInSlot(S2, s)
        BY <2>1, <1>2 DEF MaxVotedBallotInSlot
      <3> QED BY <3>1, MVBISType DEF Ballots
    <2>2. CASE \E d \in S2 \ S1 : d.slot = s
      BY <2>2, <1>2, MVBISType, MaxOnNatS, <1>3 DEF Ballots, MaxVotedBallotInSlot
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>1, <1>2

LEMMA MVBISNoSlot ==
\A S \in SUBSET [bal : Ballots, slot : Slots, val : Values], s \in Slots:
  (~ \E d \in S : d.slot = s) <=> (MaxVotedBallotInSlot(S, s) = -1) 
  BY MaxInSet DEF MaxVotedBallotInSlot, Ballots

LEMMA MVBISExists ==
\A S \in SUBSET [bal : Ballots, slot : Slots, val : Values],
    s \in Slots:
    (MaxVotedBallotInSlot(S, s) \in Ballots)
     =>
     \E d \in S : d.slot = s /\ d.bal = MaxVotedBallotInSlot(S, s)
  <1> SUFFICES ASSUME NEW S \in SUBSET [bal : Ballots, slot : Slots, val : Values],
                      NEW s \in Slots,
                      MaxVotedBallotInSlot(S, s) \in Ballots
               PROVE  \E d \in S : d.slot = s /\ d.bal = MaxVotedBallotInSlot(S, s)
    OBVIOUS
    <1>1. \E d \in S : d.slot = s
      BY DEF MaxVotedBallotInSlot, Ballots
    <1> DEFINE Ss == {d \in S : d.slot = s}
    <1> DEFINE Bs == {d.bal : d \in Ss}
    <1>2. MaxVotedBallotInSlot(S, s) = Maximum(Bs)
      BY <1>1 DEF MaxVotedBallotInSlot
    <1>3. Bs \subseteq Ballots OBVIOUS
  <1> QED
    BY <1>1, <1>2, <1>3, MaxInSet
  
LEMMA MVBISNoMore ==
\A S \in SUBSET [bal : Ballots, slot : Slots, val : Values], 
   s \in Slots:
     ~\E d \in S : d.slot = s /\ d.bal > MaxVotedBallotInSlot(S, s)
  <1> SUFFICES ASSUME NEW S \in SUBSET [bal : Ballots, slot : Slots, val : Values],
                      NEW s \in Slots
               PROVE  ~\E d \in S : d.slot = s /\ d.bal > MaxVotedBallotInSlot(S, s)
    OBVIOUS
    <1>1. CASE ~\E d \in S : d.slot = s
      BY <1>1
    <1>2. CASE \E d \in S : d.slot = s
        <2> DEFINE Ss == {d \in S : d.slot = s}
        <2> DEFINE Bs == {d.bal : d \in Ss}
        <2>3. Bs \subseteq Ballots OBVIOUS
        <2>1. ~ \E bbb \in Bs : bbb > MaxVotedBallotInSlot(S, s)
          BY <1>2, MaxOnNat, <2>3 DEF MaxVotedBallotInSlot, Ballots, Slots
        <2>2. ~ \E dd \in S : (dd.slot = s /\ ~(dd.bal =< MaxVotedBallotInSlot(S, s)))
          BY <2>1
        <2> QED BY <2>2
  <1> QED
    BY <1>1, <1>2

MsgInv ==
  \A m \in msgs : 
    /\ (m.type = "1b") =>
         /\ m.bal =< acceptorMaxBal[m.from]
         /\ \A r \in m.voted : VotedForIn(m.from, r.val, r.bal, r.slot)
         /\ \A s \in Slots, v \in Values, c \in Ballots :
            c \in MaxVotedBallotInSlot(m.voted, s)+1..m.bal-1 =>
                ~ VotedForIn(m.from, v, c, s)
    /\ (m.type = "2a") => 
         /\ \A d \in m.decrees : SafeAt(d.val, m.bal, d.slot)
         /\ \A d1,d2 \in m.decrees : d1.slot = d2.slot => d1 = d2
         /\ \A ma \in msgs : (ma.type = "2a") /\ (ma.bal = m.bal)
                                => (ma = m)
    /\ (m.type = "2b") => 
         /\ \E ma \in msgs : /\ ma.type = "2a"
                             /\ ma.bal  = m.bal
                             /\ ma.decrees = m.decrees
         /\ m.bal =< acceptorMaxBal[m.from]

(***************************************************************************)
(* The following three lemmas are simple consequences of the definitions.  *)
(***************************************************************************)
LEMMA VotedInv == 
        MsgInv /\ TypeOK => 
            \A a \in Acceptors, v \in Values, b \in Ballots, s \in Slots :
                VotedForIn(a, v, b, s) => SafeAt(v, b, s) /\ b =< acceptorMaxBal[a]
BY DEF VotedForIn, MsgInv, Messages, TypeOK

LEMMA VotedOnce == 
        MsgInv => \A a1, a2 \in Acceptors, b \in Ballots, v1, v2 \in Values, s \in Slots :
                       VotedForIn(a1, v1, b, s) /\ VotedForIn(a2, v2, b, s) => (v1 = v2)
BY DEF MsgInv, VotedForIn

LEMMA VotedUnion ==
  MsgInv /\ TypeOK => \A m1, m2 \in msgs: 
    /\ m1.type = "1b"
    /\ m2.type = "1b"
    => \A d1 \in m1.voted, d2 \in m2.voted :
        /\ d1.bal = d2.bal
        /\ d1.slot = d2.slot
        => d1.val = d2.val
  <1> SUFFICES ASSUME MsgInv /\ TypeOK,
                      NEW m1 \in msgs, NEW m2 \in msgs,
                      /\ m1.type = "1b"
                      /\ m2.type = "1b",
                      NEW d1 \in m1.voted, NEW d2 \in m2.voted,
                      d1.bal = d2.bal, d1.slot = d2.slot
               PROVE  d1.val = d2.val
    OBVIOUS
    <1>1. VotedForIn(m1.from, d1.val, d1.bal, d1.slot)
      BY DEF MsgInv
    <1>2. VotedForIn(m2.from, d2.val, d2.bal, d2.slot)
      BY DEF MsgInv
  <1> QED BY <1>1, <1>2, VotedOnce DEF TypeOK, Messages

AccInv ==
  \A a \in Acceptors:
    /\ (acceptorMaxBal[a] = -1) => (acceptorVoted[a] = {})
    /\ \A r \in acceptorVoted[a] : VotedForIn(a, r.val, r.bal, r.slot)
    /\ \A b \in Ballots, s \in Slots, v \in Values :
       VotedForIn(a, v, b, s) => \E r \in acceptorVoted[a] : /\ r.slot = s
                                                             /\ r.bal >= b
    /\ \A c \in Ballots, s \in Slots, v \in Values :
        c > MaxVotedBallotInSlot(acceptorVoted[a], s) => ~ VotedForIn(a, v, c, s)

(***************************************************************************)
(* Inv is the complete inductive invariant.                                *)
(***************************************************************************)
Inv == TypeOK /\ MsgInv /\ AccInv

LEMMA Phase1aVotedForInv ==
  TypeOK =>
  \A b \in Ballots : Phase1a(b) =>
                            \A aa \in Acceptors, bb \in Ballots, vv \in Values, ss \in Slots :
                              VotedForIn(aa, vv, bb, ss) <=> VotedForIn(aa, vv, bb, ss)'
BY DEF VotedForIn, Send, TypeOK, Messages, Phase1a

LEMMA Phase1bVotedForInv ==
  TypeOK =>
  \A a \in Acceptors : Phase1b(a) =>
                            \A aa \in Acceptors, bb \in Ballots, vv \in Values, ss \in Slots :
                              VotedForIn(aa, vv, bb, ss) <=> VotedForIn(aa, vv, bb, ss)'
BY DEF VotedForIn, Send, TypeOK, Messages, Phase1b

LEMMA Phase2aVotedForInv ==
  TypeOK =>
  \A b \in Ballots : Phase2a(b) =>
                            \A aa \in Acceptors, bb \in Ballots, vv \in Values, ss \in Slots :
                              VotedForIn(aa, vv, bb, ss) <=> VotedForIn(aa, vv, bb, ss)'
  <1> SUFFICES ASSUME TypeOK,
                      NEW b \in Ballots,
                      Phase2a(b),
                      NEW aa \in Acceptors, NEW bb \in Ballots, NEW vv \in Values, NEW ss \in Slots
               PROVE  VotedForIn(aa, vv, bb, ss) <=> VotedForIn(aa, vv, bb, ss)'
    OBVIOUS
  <1>1. VotedForIn(aa, vv, bb, ss) => VotedForIn(aa, vv, bb, ss)'
    BY DEF VotedForIn, Send, TypeOK, Messages, Phase2a
  <1>3. \A m \in msgs' \ msgs : m.type = "2a"
    BY DEF Send, TypeOK, Messages, Phase2a
  <1>2. VotedForIn(aa, vv, bb, ss)' => VotedForIn(aa, vv, bb, ss)
    BY <1>3 DEF VotedForIn, Send, TypeOK, Messages
  <1> QED
    BY <1>1, <1>2


LEMMA Phase2bVotedForInv ==
  TypeOK =>
  \A a \in Acceptors : Phase2b(a) =>
                            \A aa \in Acceptors, bb \in Ballots, vv \in Values, ss \in Slots :
                              VotedForIn(aa, vv, bb, ss) => VotedForIn(aa, vv, bb, ss)'
BY DEF VotedForIn, Send, TypeOK, Messages, Phase2b  
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following lemma shows that (the invariant implies that) the         *)
(* predicate SafeAt(v, b,s) is stable, meaning that once it becomes true,  *)
(* it remains true throughout the rest of the excecution.                  *)
(***************************************************************************)
LEMMA SafeAtStable == Inv /\ Next /\ TypeOK' => 
                          \A v \in Values, b \in Ballots, s \in Slots:
                                  SafeAt(v, b, s) => SafeAt(v, b, s)'
<1> SUFFICES ASSUME Inv, Next, TypeOK',
                    NEW v \in Values, NEW b \in Ballots, NEW s \in Slots, SafeAt(v, b, s)
             PROVE  SafeAt(v, b, s)'
  OBVIOUS
<1> USE DEF Send, Inv, Ballots
<1>1. ASSUME NEW bb \in Ballots, Phase1a(bb)
      PROVE  SafeAt(v, b, s)'
  BY <1>1, SMT DEF SafeAt, Phase1a, VotedForIn, WontVoteIn
<1>2. ASSUME NEW a \in Acceptors, Phase1b(a)
      PROVE  SafeAt(v, b, s)'
  BY <1>2, QuorumAssumption, SMTT(200) DEF TypeOK, SafeAt, WontVoteIn, VotedForIn, Phase1b
<1>3. ASSUME NEW bb \in Ballots, Phase2a(bb)
      PROVE  SafeAt(v, b, s)'
  <2>2. \A aa \in Acceptors, ss \in Slots, bbb \in Ballots :
        WontVoteIn(aa, bbb, ss) <=> WontVoteIn(aa, bbb, ss)'
    BY <1>3, Phase2aVotedForInv DEF WontVoteIn, Send, Phase2a
  <2> QED BY <2>2, QuorumAssumption, Phase2aVotedForInv, <1>3 DEF SafeAt
<1>4. ASSUME NEW a \in Acceptors, Phase2b(a)
      PROVE  SafeAt(v, b, s)'
  <2>1. PICK m \in msgs : Phase2b(a)!(m)
    BY <1>4 DEF Phase2b
  <2>3. \A aa \in Acceptors, bb \in Ballots : acceptorMaxBal[aa] > bb => acceptorMaxBal'[aa] > bb
    BY <2>1 DEF TypeOK
  <2>4. ASSUME NEW aa \in Acceptors, NEW bb \in Ballots, NEW ss \in Slots,
               WontVoteIn(aa, bb, ss), NEW vv \in Values,
               VotedForIn(aa, vv, bb, ss)',
               NEW S \in SUBSET [slot : Slots \ {ss}, val : Values]
        PROVE FALSE
    <3> DEFINE mm == [type |-> "2b", bal |-> bb, from |-> aa, decrees |-> {[slot |-> ss, val |-> vv]} \cup S]
    <3>1. \E m1 \in msgs' \ msgs :
              /\ m1.type = "2b"
              /\ \E d \in m1.decrees : d.slot = ss /\ d.val = vv
              /\ m1.bal = bb
              /\ m1.from = aa
        BY <2>4 DEF VotedForIn, WontVoteIn
    <3>3. aa = a /\ m.bal = bb
      BY <2>1, <3>1 DEF TypeOK
    <3>. QED
      BY <2>1, <2>4, <3>3, <3>1 DEF Phase2b, WontVoteIn, TypeOK 
  <2>5 \A aa \in Acceptors, bb \in Ballots, ss \in Slots : WontVoteIn(aa, bb, ss) => WontVoteIn(aa, bb, ss)'
    BY <2>3, <2>4 DEF WontVoteIn
  <2> QED
    BY Phase2bVotedForInv, <2>5, QuorumAssumption, <1>4 DEF SafeAt
<1>5. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF Next

THEOREM Invariant == Spec => []Inv
<1> USE DEF Ballots, Slots
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, AccInv, MsgInv, VotedForIn
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2> USE DEF Inv
  <2>1. CASE Next
  <3>1. TypeOK'
    <4>1. ASSUME NEW b \in Ballots, Phase1a(b) PROVE TypeOK'
      <5>1. (msgs \in SUBSET Messages)'
        BY <4>1, PTL DEF Phase1a, TypeOK
      <5>2. (acceptorVoted \in [Acceptors -> SUBSET [bal : Ballots, slot : Slots, val : Values]])'
        BY <4>1 DEF Phase1a, TypeOK
      <5>3. (acceptorMaxBal \in  [Acceptors -> Ballots \cup {-1}])'
        BY <4>1 DEF Phase1a, TypeOK
      <5>4. (\A a \in Acceptors: \A r \in acceptorVoted[a] : acceptorMaxBal[a] >= r.bal)'
        BY <4>1 DEF Phase1a, TypeOK
      <5>5. QED
        BY <5>1, <5>2, <5>3, <5>4 DEF TypeOK
    <4>2. ASSUME NEW b \in Ballots, Phase2a(b) PROVE TypeOK'
      <5>1. (msgs \in SUBSET Messages)'
        BY <4>2, PTL DEF Phase2a, TypeOK
      <5>2. (acceptorVoted \in [Acceptors -> SUBSET [bal : Ballots, slot : Slots, val : Values]])'
        BY <4>2 DEF Phase2a, TypeOK
      <5>3. (acceptorMaxBal \in  [Acceptors -> Ballots \cup {-1}])'
        BY <4>2 DEF Phase2a, TypeOK
      <5>4. (\A a \in Acceptors: \A r \in acceptorVoted[a] : acceptorMaxBal[a] >= r.bal)'
        BY <4>2 DEF Phase2a, TypeOK
      <5>5. QED
        BY <5>1, <5>2, <5>3, <5>4 DEF TypeOK
    <4>3. ASSUME NEW a \in Acceptors, Phase1b(a) PROVE TypeOK'
      <5>1. (msgs \in SUBSET Messages)'
        BY <4>3, PTL DEF Phase1b, TypeOK
      <5>2. (acceptorVoted \in [Acceptors -> SUBSET [bal : Ballots, slot : Slots, val : Values]])'
        BY <4>3 DEF Phase1b, TypeOK
      <5>3. (acceptorMaxBal \in  [Acceptors -> Ballots \cup {-1}])'
        BY <4>3 DEF Phase1b, TypeOK
      <5>4. (\A a_1 \in Acceptors: \A r \in acceptorVoted[a_1] : acceptorMaxBal[a_1] >= r.bal)'
        BY <4>3 DEF Phase1b, TypeOK
      <5>5. QED
        BY <5>1, <5>2, <5>3, <5>4 DEF TypeOK
    <4>4. ASSUME NEW a \in Acceptors, Phase2b(a) PROVE TypeOK'
      <5>1. (msgs \in SUBSET Messages)'
        BY <4>4, PTL DEF Phase2b, TypeOK
      <5>2. (acceptorVoted \in [Acceptors -> SUBSET [bal : Ballots, slot : Slots, val : Values]])'
        BY <4>4, PTL DEF Phase2b, TypeOK, Messages
      <5>3. (acceptorMaxBal \in  [Acceptors -> Ballots \cup {-1}])'
        BY <4>4 DEF Phase2b, TypeOK
      <5>4. (\A a_1 \in Acceptors: \A r \in acceptorVoted[a_1] : acceptorMaxBal[a_1] >= r.bal)'
        <6> SUFFICES ASSUME NEW a_1 \in Acceptors'
                     PROVE  (\A r \in acceptorVoted[a_1] : acceptorMaxBal[a_1] >= r.bal)'
          OBVIOUS
          <6>1. \A r \in acceptorVoted[a_1] : acceptorMaxBal'[a_1] >= r.bal
            BY <4>4 DEF Phase2b, TypeOK
          <6>2. \A r \in acceptorVoted'[a_1] \ acceptorVoted[a_1] : acceptorMaxBal'[a_1] = r.bal
            BY <4>4 DEF Phase2b, TypeOK
        <6> QED BY <6>1, <6>2 DEF TypeOK
      <5>5. QED
        BY <5>1, <5>2, <5>3, <5>4 DEF TypeOK
    <4>. QED
      BY <4>1, <4>2, <4>3, <4>4, <2>1 DEF Next

  <3>2. AccInv'
    <4>1. ASSUME NEW b \in Ballots, Phase1a(b) PROVE AccInv'
      <5>1. \A aa \in Acceptors, ss \in Slots :
                MaxVotedBallotInSlot(acceptorVoted[aa], ss) = MaxVotedBallotInSlot(acceptorVoted[aa], ss)'
        BY <3>1, <4>1 DEF Phase1a, MaxVotedBallotInSlot
      <5> QED BY <4>1, <3>1, Phase1aVotedForInv, <5>1, SMTT(100) DEF AccInv, TypeOK, Phase1a, Send
    <4>2. ASSUME NEW b \in Ballots, Phase2a(b) PROVE AccInv'
      <5>1. \A aa \in Acceptors, ss \in Slots :
                MaxVotedBallotInSlot(acceptorVoted[aa], ss) = MaxVotedBallotInSlot(acceptorVoted[aa], ss)'
        BY <3>1, <4>2 DEF Phase2a, MaxVotedBallotInSlot
      <5>2. \A aa \in Acceptors, bb \in Nat, vv \in Values, ss \in Nat :
                     VotedForIn(aa, vv, bb, ss)
                     <=> VotedForIn(aa, vv, bb, ss)'
        BY <4>2, Phase2aVotedForInv
      <5> QED BY <4>2, <3>1, <5>2, <5>1, SMTT(100) DEF AccInv, TypeOK, Phase2a, Send, Messages
    <4>3. ASSUME NEW a \in Acceptors, Phase1b(a) PROVE AccInv'
      <5>1. \A aa \in Acceptors, ss \in Slots :
                MaxVotedBallotInSlot(acceptorVoted[aa], ss) = MaxVotedBallotInSlot(acceptorVoted[aa], ss)'
        BY <3>1, <4>3 DEF Phase1b, MaxVotedBallotInSlot
    <5> QED BY <4>3, <3>1, Phase1bVotedForInv, <5>1 DEF AccInv, TypeOK, Phase1b, Send
    <4>4. ASSUME NEW a \in Acceptors, Phase2b(a) PROVE AccInv'
      <5> SUFFICES ASSUME NEW a_1 \in Acceptors'
                   PROVE  (/\ (acceptorMaxBal[a_1] = -1) => (acceptorVoted[a_1] = {})
                           /\ \A r \in acceptorVoted[a_1] : /\ VotedForIn(a_1, r.val, r.bal, r.slot)
                                                            /\ r.bal =< acceptorMaxBal[a_1]
                           /\ \A b \in Ballots, s \in Slots, v \in Values :
                               VotedForIn(a_1, v, b, s) => \E r \in acceptorVoted[a_1] : /\ r.slot = s
                                                                                         /\ r.bal >= b 
                           /\ \A c \in Ballots, s \in Slots, v \in Values :
                               c > MaxVotedBallotInSlot(acceptorVoted[a_1], s) => ~ VotedForIn(a_1, v, c, s)
                           )'
        BY DEF AccInv
      <5>. PICK m \in msgs : Phase2b(a)!(m)
          BY <4>4 DEF Phase2b
      <5>1 CASE a_1 # a
        <6>0. \A vv \in Values, bb \in Ballots, ss \in Slots:
                VotedForIn(a_1, vv, bb, ss) <=> VotedForIn(a_1, vv, bb, ss)'
          BY <3>1, <5>1 DEF Phase2b, TypeOK, Ballots, Messages, VotedForIn, Send
        <6>2. acceptorVoted[a_1] = acceptorVoted'[a_1]
          BY <3>1, <4>4, <5>1 DEF Phase2b, TypeOK, Ballots, Messages, Send
        <6>3. acceptorMaxBal[a_1] = acceptorMaxBal'[a_1]
          BY <3>1, <4>4, <5>1 DEF Phase2b, TypeOK, Ballots, Messages, Send
        <6>1. \A ss \in Slots :
            MaxVotedBallotInSlot(acceptorVoted[a_1], ss) = MaxVotedBallotInSlot(acceptorVoted[a_1], ss)'
          BY <6>2 DEF Phase2b, MaxVotedBallotInSlot
        <6>4. \A ss \in Slots : MaxVotedBallotInSlot(acceptorVoted[a_1], ss) \in Ballots \cup {-1}
          BY <3>1, <4>4, <5>1, MVBISType DEF Phase2b, TypeOK, Messages
        <6> QED BY <6>0, <6>1, <6>2, <6>3, <6>4 DEF AccInv, TypeOK, Messages
      <5>2 CASE a_1 = a
        <6>1. ((acceptorMaxBal[a_1] = -1) => (acceptorVoted[a_1] = {}))'
          BY <5>2, <4>4, <3>1 DEF AccInv, Phase2b, Send, TypeOK
        <6>2. (\A r \in acceptorVoted[a_1] : /\ VotedForIn(a_1, r.val, r.bal, r.slot)
                                             /\ r.bal =< acceptorMaxBal[a_1])'
          <7> SUFFICES ASSUME NEW r \in (acceptorVoted[a_1])'
                       PROVE  (/\ VotedForIn(a_1, r.val, r.bal, r.slot)
                               /\ r.bal =< acceptorMaxBal[a_1])'
            OBVIOUS
          <7>1. VotedForIn(a_1, r.val, r.bal, r.slot)'
            <8>1. CASE r \in acceptorVoted[a_1]
              <9>1. VotedForIn(a_1, r.val, r.bal, r.slot)
                BY <5>2, <4>4, <8>1 DEF AccInv
              <9> QED BY <9>1, Phase2bVotedForInv, <3>1, <4>4 DEF TypeOK, Messages
            <8>2. CASE r \in acceptorVoted'[a_1] \ acceptorVoted[a_1]
              <9>2. \E m1 \in msgs' : m1.type = "2b" /\ m1.decrees = m.decrees /\ m.bal = m1.bal /\ m1.from = a_1
                BY <3>1, <8>2, <5>2, IsaT(1000) DEF Send
              <9>4. r.bal = m.bal
                BY <5>2, <3>1, <8>2
              <9>5. \E d \in m.decrees : r.slot = d.slot /\ r.val = d.val
                BY <5>2, <3>1, <8>2
              <9>7. \A d \in m.decrees : d \in [slot : Slots, val : Values]
                BY <3>1 DEF TypeOK, Messages
              <9> QED BY <9>2, <9>4, <9>5 DEF Send, TypeOK, Messages, VotedForIn
            <8> QED BY <8>1, <8>2
          <7>2. (r.bal =< acceptorMaxBal[a_1])'
            BY <5>2, <4>4, <3>1, Phase2bVotedForInv DEF AccInv, Phase2b, Send, TypeOK, VotedForIn
          <7>3. QED
            BY <7>1, <7>2
        <6>4. (\A b \in Ballots, s \in Slots, v \in Values :
                VotedForIn(a_1, v, b, s) =>
                    \E r \in acceptorVoted[a_1] : /\ r.slot = s
                                                  /\ r.bal >= b)'
          <7> SUFFICES ASSUME NEW b \in Ballots', NEW s \in Slots', NEW v \in Values',
                              VotedForIn(a_1, v, b, s)'
                       PROVE  (\E r \in acceptorVoted[a_1] : /\ r.slot = s
                                                             /\ r.bal >= b)'
            OBVIOUS
          <7>1. CASE VotedForIn(a_1, v, b, s)
            <8>0. PICK r \in acceptorVoted[a_1] :
                           /\ r.slot = s
                           /\ r.bal >= b
              BY <7>1 DEF AccInv, TypeOK, Messages
            <8>5. m.bal >= b
              BY <8>0, <5>2 DEF TypeOK, Messages, AccInv
            <8>1. CASE \E d \in m.decrees : d.slot = s
              <9>1. \E rr \in acceptorVoted'[a_1] : /\ rr.slot = s
                                                    /\ rr.bal = m.bal
                BY <5>2, <8>1, IsaT(1000) DEF TypeOK
              <9> QED
                BY <9>1, <8>5
            <8>2. CASE ~ \E d \in m.decrees : d.slot = s
              <9>1. r \in acceptorVoted'[a_1]
                BY <8>2, <8>0, <5>2
              <9> QED
                BY <9>1, <8>0
            <8> QED BY <8>1, <8>2
          <7>2. CASE ~ VotedForIn(a_1, v, b, s)
            <8>2. \E d \in m.decrees : d.slot = s
              BY <7>2 DEF Send, TypeOK, Messages, VotedForIn
            <8>1. \E r \in acceptorVoted'[a_1] : /\ r.slot = s
                                                 /\ r.bal = m.bal
              BY <8>2, <2>1, <5>2 DEF Send, TypeOK, Messages
            <8>3. b = m.bal
              BY <7>2, <5>2 DEF VotedForIn, Send
            <8> QED BY <8>1, <8>3
          <7> QED BY <7>1, <7>2
        <6>3. (\A c \in Ballots, s \in Slots, v \in Values :
                c > MaxVotedBallotInSlot(acceptorVoted[a_1], s) => ~ VotedForIn(a_1, v, c, s))'
          <7> SUFFICES ASSUME NEW c \in Ballots', NEW s \in Slots', NEW v \in Values',
                              (c > MaxVotedBallotInSlot(acceptorVoted[a_1], s))',
                              (VotedForIn(a_1, v, c, s))'
                       PROVE  FALSE
            OBVIOUS
          <7>1. ~\E d \in acceptorVoted'[a_1] :
                    /\ d.slot = s
                    /\ d.bal > MaxVotedBallotInSlot(acceptorVoted[a_1], s)'
            BY MVBISNoMore, <3>1 DEF TypeOK
          <7>2. \E r \in acceptorVoted'[a_1] : /\ r.slot = s
                                               /\ r.bal >= c
            BY <6>4
          <7> QED
            BY <7>1, <7>2, MVBISType, <3>1 DEF Send, TypeOK, Messages
        <6>5. QED
          BY <6>1, <6>2, <6>3, <6>4
      <5> QED BY <5>1, <5>2
    <4>. QED
      BY <4>1, <4>2, <4>3, <4>4, <2>1 DEF Next
  
  <3>3. MsgInv'
    <4>1. ASSUME NEW b \in Ballots, Phase1a(b) PROVE  MsgInv'
        BY <4>1, Phase1aVotedForInv, <3>1, SafeAtStable, <2>1 DEF Phase1a, MsgInv, Send, TypeOK, Messages
    <4>2. ASSUME NEW a \in Acceptors, Phase1b(a) PROVE  MsgInv'
      <5>1. PICK m \in msgs : Phase1b(a)!(m)
          BY <4>2 DEF Phase1b
      <5> DEFINE mm == [type |-> "1b", bal |-> m.bal, voted |-> acceptorVoted[a], from |-> a]
      <5>2. (mm.bal =< acceptorMaxBal[mm.from])'
        BY <5>1, <3>1 DEF Phase1b, Send, TypeOK, MsgInv, Messages
      <5>6. mm.voted = acceptorVoted[mm.from]
        BY <5>1, <3>1 DEF Phase1b, Send, TypeOK, Messages
      <5>10. \A s \in Slots : MaxVotedBallotInSlot(mm.voted, s) \in Ballots \cup {-1}
        BY MVBISType, <3>1 DEF TypeOK, Messages
      <5>3. (\A r \in mm.voted : VotedForIn(mm.from, r.val, r.bal, r.slot))'
        BY <5>1, <4>2, Phase1bVotedForInv, <3>1, <5>6 DEF TypeOK, Messages, AccInv
      <5>7. (\A s \in Slots, v \in Values, c \in Ballots:
               c > MaxVotedBallotInSlot(mm.voted, s) =>
                   ~ VotedForIn(mm.from, v, c, s))'
        BY Phase1bVotedForInv, <4>2, <5>6, <5>1, <3>2, <3>1 DEF AccInv, MsgInv, Send, TypeOK, Messages
      <5>8. \A s \in Slots : MaxVotedBallotInSlot(mm.voted, s) \in Ballots \cup {-1}
        BY <3>1, MVBISType DEF TypeOK, Messages
      <5>9. \A s \in Slots : MaxVotedBallotInSlot(mm.voted, s)+1 \in Ballots
        <6> SUFFICES ASSUME NEW s \in Slots
                     PROVE  MaxVotedBallotInSlot(mm.voted, s)+1 \in Ballots
          OBVIOUS
        <6>1. CASE MaxVotedBallotInSlot(mm.voted, s) \in {-1}
          BY -1 + 1 = 0, 0 \in Ballots, <6>1
        <6>2. CASE MaxVotedBallotInSlot(mm.voted, s) \in Ballots
          BY \A x \in Ballots : x+1 \in Ballots, <6>2
        <6> QED
          BY <6>1, <6>2, <5>8
      <5>11. \A s \in Slots : MaxVotedBallotInSlot(mm.voted, s)+1 > MaxVotedBallotInSlot(mm.voted, s)
        <6> SUFFICES ASSUME NEW s \in Slots
                     PROVE  MaxVotedBallotInSlot(mm.voted, s)+1 > MaxVotedBallotInSlot(mm.voted, s)
          OBVIOUS
        <6>1. CASE MaxVotedBallotInSlot(mm.voted, s) \in {-1}
          BY -1 + 1 = 0, 0 > -1, <6>1
        <6>2. CASE MaxVotedBallotInSlot(mm.voted, s) \in Ballots
          BY \A x \in Ballots : x+1 > x, <6>2
        <6> QED
          BY <5>8, <6>1, <6>2
      <5>39. mm.bal \in Ballots
        BY <3>1 DEF TypeOK, Messages
      <5>41. (\A s \in Slots, c \in Ballots : c \in MaxVotedBallotInSlot(mm.voted, s)+1..mm.bal-1 =>
                c > MaxVotedBallotInSlot(mm.voted, s))
        <6> SUFFICES ASSUME NEW s \in Slots, NEW c \in Ballots,
                            c \in MaxVotedBallotInSlot(mm.voted, s)+1..mm.bal-1
                     PROVE  c > MaxVotedBallotInSlot(mm.voted, s)
          OBVIOUS
          <6> HIDE DEF mm
          <6> DEFINE x == MaxVotedBallotInSlot(mm.voted, s)
          <6> DEFINE y == mm.bal-1
          <6>10. x \in Ballots \cup {-1} BY <5>8
          <6>11. y \in Ballots \cup {-1} BY <5>39
          <6> HIDE DEF x, y
          <6>1. CASE x+1 > y
            <7>1. \A e \in Ballots : e \notin x+1..y
              BY <6>1, <6>10, <6>11
            <7> QED BY <6>1, <7>1 DEF x, y
          <6>2. CASE x+1 = y
            BY <6>2, <5>11, <5>9, <3>1, <5>39 DEF x, y
          <6>3. CASE x+1 < y
            <7>1. \A e \in Ballots : e \in x+1..y => e > x
              BY <6>3, <6>10, <6>11
            <7>2. c \in x+1..y BY DEF x, y
            <7>3. c > x BY <7>2, <7>1
            <7> QED BY <7>3 DEF x
        <6> QED BY <6>1, <6>2, <6>3, <6>10, <6>11
      <5>40. (\A s \in Slots, c \in Ballots : c \in MaxVotedBallotInSlot(mm.voted, s)+1..mm.bal-1 =>
                c > MaxVotedBallotInSlot(mm.voted, s))'
        BY <5>41, <5>1
      <5>4. (\A s \in Slots, v \in Values, c \in Ballots :
                c \in MaxVotedBallotInSlot(mm.voted, s)+1..mm.bal-1 =>
                   ~ VotedForIn(mm.from, v, c, s))'
        <6> SUFFICES ASSUME NEW s \in Slots', NEW v \in Values', NEW c \in Ballots'
                     PROVE  (c \in MaxVotedBallotInSlot(mm.voted, s)+1..mm.bal-1 =>
                                ~ VotedForIn(mm.from, v, c, s))'
          OBVIOUS
        <6>1. CASE ~ \E x \in Ballots : x \in (MaxVotedBallotInSlot(mm.voted, s)+1..mm.bal-1)'
          BY <6>1
        <6>2. CASE \E x \in Ballots : x \in (MaxVotedBallotInSlot(mm.voted, s)+1..mm.bal-1)'
          BY <6>2, <5>7, <5>40
        <6> QED BY <6>1, <6>2
      <5>20. CASE m.bal > acceptorMaxBal[a]
      <6> SUFFICES ASSUME NEW m2 \in msgs'
                   PROVE  (/\ (m2.type = "1b") =>
                                /\ m2.bal =< acceptorMaxBal[m2.from]
                                /\ \A r \in m2.voted : VotedForIn(m2.from, r.val, r.bal, r.slot)
                                /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   c \in MaxVotedBallotInSlot(m2.voted, s)+1..m2.bal-1 =>
                                       ~ VotedForIn(m2.from, v, c, s)
                           /\ (m2.type = "2a") => 
                                /\ \A d \in m2.decrees : SafeAt(d.val, m2.bal, d.slot)
                                /\ \A d1,d2 \in m2.decrees : d1.slot = d2.slot => d1 = d2
                                /\ \A ma \in msgs : (ma.type = "2a") /\ (ma.bal = m2.bal)
                                                       => (ma = m2)
                           /\ (m2.type = "2b") => 
                                /\ \E ma \in msgs : /\ ma.type = "2a"
                                                    /\ ma.bal  = m2.bal
                                                    /\ ma.decrees = m2.decrees
                                /\ m2.bal =< acceptorMaxBal[m2.from])'
        BY DEF MsgInv
        <6>1. ((m2.type = "1b") =>
               /\ m2.bal =< acceptorMaxBal[m2.from]
               /\ \A r \in m2.voted : VotedForIn(m2.from, r.val, r.bal, r.slot)
               /\ \A s \in Slots, v \in Values, c \in Ballots :
                  c \in MaxVotedBallotInSlot(m2.voted, s)+1..m2.bal-1 =>
                      ~ VotedForIn(m2.from, v, c, s))'
        <7>1. CASE m2 \in msgs
          BY <7>1, <5>20, <5>1, Phase1bVotedForInv, <4>2, IsaT(200) DEF MsgInv, TypeOK, Messages
        <7>2. CASE m2 \in msgs' \ msgs
          <8>1. m2 = mm
            BY <5>1, <7>2, <5>20 DEF Send
          <8> QED
          BY <7>2, <5>20, Phase1bVotedForInv, <4>2, <5>2, <5>3, <5>4, <5>1, <3>1, <2>1, <8>1
          DEF Send, TypeOK, MsgInv, Messages
        <7> QED BY <7>1, <7>2
        <6>2. ((m2.type = "2a") => 
               /\ \A d \in m2.decrees : SafeAt(d.val, m2.bal, d.slot)
               /\ \A d1,d2 \in m2.decrees : d1.slot = d2.slot => d1 = d2
               /\ \A ma \in msgs : (ma.type = "2a") /\ (ma.bal = m2.bal)
                                      => (ma = m2))'
            BY <5>20, Phase1bVotedForInv, <5>1, <4>2, <3>1, SafeAtStable, <2>1
            DEF Send, TypeOK, MsgInv, Messages        
        <6>3. ((m2.type = "2b") => 
               /\ \E ma \in msgs : /\ ma.type = "2a"
                                   /\ ma.bal  = m2.bal
                                   /\ ma.decrees = m2.decrees
               /\ m2.bal =< acceptorMaxBal[m2.from])'
        BY <5>20, Phase1bVotedForInv, <4>2, <5>1, <3>1, <2>1
        DEF Send, TypeOK, MsgInv, Messages
        <6> QED BY <6>1, <6>2, <6>3
      <5>21. CASE ~ (m.bal > acceptorMaxBal[a])
        BY <5>21, Phase1bVotedForInv, <4>2, <5>2, <5>3, <5>4, <5>1, <3>1, SafeAtStable, <2>1
        DEF Send, TypeOK, MsgInv, Messages
      <5>. QED BY <5>20, <5>21
    <4>3. ASSUME NEW b \in Ballots, Phase2a(b) PROVE  MsgInv'
      <5> SUFFICES ASSUME NEW m \in msgs'
                   PROVE  (/\ (m.type = "1b") =>
                                /\ m.bal =< acceptorMaxBal[m.from]
                                /\ \A r \in m.voted : VotedForIn(m.from, r.val, r.bal, r.slot)
                                /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   c \in MaxVotedBallotInSlot(m.voted, s)+1..m.bal-1 =>
                                       ~ VotedForIn(m.from, v, c, s)
                                                   \*/\ \A r1, r2 \in m.voted : r1.slot = r2.slot => r1 = r2
                           /\ (m.type = "2a") => 
                                /\ \A d \in m.decrees : SafeAt(d.val, m.bal, d.slot)
                                /\ \A d1,d2 \in m.decrees : d1.slot = d2.slot => d1 = d2
                                /\ \A ma \in msgs : (ma.type = "2a") /\ (ma.bal = m.bal)
                                                       => (ma = m)
                           /\ (m.type = "2b") => 
                                /\ \E ma \in msgs : /\ ma.type = "2a"
                                                    /\ ma.bal  = m.bal
                                                    /\ ma.decrees = m.decrees
                                /\ m.bal =< acceptorMaxBal[m.from])'
        BY DEF MsgInv
      <5> PICK Q \in Quorums, S \in SUBSET {mm \in msgs : (mm.type = "1b") /\ (mm.bal = b)} :
                        /\ \A a \in Q : \E mm \in S : mm.from = a
                        /\ Send([type |-> "2a", bal |-> b, decrees |-> ProposeDecrees(UNION {mm.voted : mm \in S})])
          BY <4>3 DEF Phase2a
      <5>0. \A mm \in msgs' \ msgs : /\ mm.type = "2a"
                                     /\ mm.type # "2b"
                                     /\ mm.type # "1b"
                                     /\ mm.bal = b
        BY DEF Send
      <5>1. ((m.type = "1b") =>
               /\ m.bal =< acceptorMaxBal[m.from]
               /\ \A r \in m.voted : VotedForIn(m.from, r.val, r.bal, r.slot)
               /\ \A s \in Slots, v \in Values, c \in Ballots :
                  c \in MaxVotedBallotInSlot(m.voted, s)+1..m.bal-1 =>
                      ~ VotedForIn(m.from, v, c, s))'
        <6> SUFFICES ASSUME (m.type = "1b")'
                     PROVE  (/\ m.bal =< acceptorMaxBal[m.from]
                             /\ \A r \in m.voted : VotedForIn(m.from, r.val, r.bal, r.slot)
                             /\ \A s \in Slots, v \in Values, c \in Ballots :
                                c \in MaxVotedBallotInSlot(m.voted, s)+1..m.bal-1 =>
                                    ~ VotedForIn(m.from, v, c, s))'
          OBVIOUS
        <6>0. \A s \in Slots : MaxVotedBallotInSlot(m.voted, s) = MaxVotedBallotInSlot(m.voted, s)'
          BY DEF MaxVotedBallotInSlot
        <6>1. (m.bal =< acceptorMaxBal[m.from])'
          BY <4>3, <5>0, <3>1, Phase2aVotedForInv DEF TypeOK, Messages, MsgInv, Phase2a
        <6>2. (\A r \in m.voted : VotedForIn(m.from, r.val, r.bal, r.slot))'
          BY <4>3, <5>0, <3>1, Phase2aVotedForInv DEF TypeOK, Messages, MsgInv
        <6>3. (\A s \in Slots, v \in Values, c \in Ballots :
               c \in MaxVotedBallotInSlot(m.voted, s)+1..m.bal-1 =>
                   ~ VotedForIn(m.from, v, c, s))'
          BY <4>3, <5>0, <3>1, Phase2aVotedForInv, <6>0 DEF TypeOK, Messages, MsgInv
        <6>4. QED
          BY <6>1, <6>2, <6>3
        
      <5>2. ((m.type = "2a") => 
               /\ \A d \in m.decrees : SafeAt(d.val, m.bal, d.slot)
               /\ \A d1,d2 \in m.decrees : d1.slot = d2.slot => d1 = d2
               /\ \A ma \in msgs : (ma.type = "2a") /\ (ma.bal = m.bal)
                                      => (ma = m))'
        <6> SUFFICES ASSUME (m.type = "2a")'
                     PROVE  (/\ \A d \in m.decrees : SafeAt(d.val, m.bal, d.slot)
                             /\ \A d1,d2 \in m.decrees : d1.slot = d2.slot => d1 = d2
                             /\ \A ma \in msgs : (ma.type = "2a") /\ (ma.bal = m.bal)
                                                    => (ma = m))'
          OBVIOUS
        <6> DEFINE VS == UNION {mm.voted : mm \in S}
        <6>0. \A a \in Q : acceptorMaxBal[a] >= b
            BY <3>2, <3>1 DEF MsgInv, TypeOK, Messages
        <6>1. (\A d \in m.decrees : SafeAt(d.val, m.bal, d.slot))'
          <7>13. \A d \in [slot : FreeSlots(VS), val : Values] \ {} : SafeAt(d.val, b, d.slot)
            <8> SUFFICES ASSUME NEW d \in [slot : FreeSlots(VS), val : Values] \ {}
                         PROVE  (SafeAt(d.val, b, d.slot))
              OBVIOUS
            <8>2. \A mm \in S : ~ \E d1 \in mm.voted : d.slot = d1.slot
              BY DEF FreeSlots
            <8>3. \A mm \in S : MaxVotedBallotInSlot(mm.voted, d.slot) + 1 = 0
              BY <8>2, SMTT(1000) DEF MaxVotedBallotInSlot
            <8>5. \A mm \in S : \A s \in Nat, v \in Values, c \in Nat :
                    c \in MaxVotedBallotInSlot(mm.voted, s) + 1..mm.bal - 1
                               => ~VotedForIn(mm.from, v, c, s)
              BY DEF MsgInv
            <8>4. \A vv \in Values, cc \in Ballots, a \in Q :
                    cc \in 0..b-1 => ~VotedForIn(a, vv, cc, d.slot)
              BY <8>3, <8>5 DEF FreeSlots, TypeOK, Messages
            <8> QED BY <8>4, <3>1, <6>0 DEF SafeAt, NewProposals, FreeSlots, WontVoteIn, TypeOK, Messages
          <7>77. \A d \in [slot : FreeSlots(VS), val : Values] \ {} : SafeAt(d.val, b, d.slot)'
            BY <7>13, SafeAtStable, <3>1, <2>1 DEF NewProposals, FreeSlots, TypeOK, Messages
          <7>14. \A d \in NewProposals(VS) : SafeAt(d.val, b, d.slot)'
            BY <7>77, NPC DEF NewProposals
          <7>15. \A d \in PartialBmax(VS) : SafeAt(d.val, b, d.slot)
            <8> SUFFICES ASSUME NEW d \in PartialBmax(VS),
                                NEW c \in Ballots,
                                c \in 0..(b-1)
                         PROVE  \E Q_1 \in Quorums : 
                                  \A a \in Q_1 : VotedForIn(a, d.val, c, d.slot) \/ WontVoteIn(a, c, d.slot)
              BY DEF SafeAt
            <8> DEFINE max == MaxVotedBallotInSlot(VS, d.slot)
            <8> USE DEF PartialBmax
            <8>5. d.slot \in Slots
              BY DEF PartialBmax, TypeOK, Messages
            <8>6. max \in Ballots \cup {-1}
              BY MVBISType, <8>5 DEF TypeOK, Messages
            <8>9. d \in VS
              OBVIOUS
            <8>8. max # -1
              BY <8>9, MVBISNoSlot DEF TypeOK, Messages
            <8>10. max \in Ballots
              BY <8>6, <8>8
            <8>4. \A a \in Q : acceptorMaxBal[a] >= b
              BY DEF MsgInv
            <8>7. \A mm \in S : mm.voted \subseteq VS
              OBVIOUS
            <8>0. \A mm \in S : MaxVotedBallotInSlot(mm.voted, d.slot) <= max
              BY MVBISSubsets, <8>7 DEF PartialBmax, TypeOK, Messages
            <8>31. \A dd \in VS : dd.slot = d.slot => dd.bal =< d.bal
              BY DEF PartialBmax, TypeOK, Messages
            <8>30. \A dd \in VS : ~(dd.slot = d.slot /\ ~(dd.bal =< d.bal))
              BY <8>31
            <8>33. ~ \E dd \in VS : (dd.slot = d.slot /\ dd.bal > d.bal)
              BY <8>30
            <8>35. d.bal \in Ballots
              BY DEF TypeOK, Messages
            <8>32. VS \in SUBSET [bal : Ballots, slot : Slots, val : Values]
              BY <3>1 DEF TypeOK, Messages
            <8>11. max = d.bal
              <9> SUFFICES ASSUME max # d.bal
                           PROVE  FALSE
                OBVIOUS
              <9>1. CASE max > d.bal
                <10>1. \E d1 \in VS : d1.slot = d.slot /\ d1.bal = max
                  BY <8>32, MVBISExists, <8>10
                <10> QED BY <10>1, <8>33, <9>1
              <9>2. CASE max < d.bal
                BY MVBISNoMore, <9>2 DEF PartialBmax, TypeOK, Messages
              <9> QED BY <9>1, <9>2, <8>10, <8>35 DEF Ballots
            <8>1. CASE c \in max+1..b-1
              <9>2. \A mm \in S, bb \in Ballots, v \in Values :
                               bb \in MaxVotedBallotInSlot(mm.voted, d.slot) + 1..b - 1
                               => ~VotedForIn(mm.from, v, bb, d.slot)
                BY <8>5 DEF MsgInv, TypeOK, Messages
              <9>1. \A mm \in S : \A v \in Values : ~VotedForIn(mm.from, v, c, d.slot)
                BY <8>1, <9>2, <8>0, <8>5, MVBISType, <8>6 DEF TypeOK, Messages
              <9> QED BY <8>1, <8>4, <9>1 DEF MsgInv, TypeOK, Messages, WontVoteIn, PartialBmax
            <8>2. CASE c = max
                <9>0. \E a \in Acceptors, mm \in S :
                        /\ mm.from = a
                        /\ \E dd \in mm.voted : /\ dd.bal = d.bal
                                                /\ dd.val = d.val
                                                /\ dd.slot = d.slot
                  BY DEF MaxVotedBallotInSlot, TypeOK, Messages
                <9>1. \E a \in Acceptors : VotedForIn(a, d.val, c, d.slot)
                  BY <8>2, <9>0, <8>11 DEF MsgInv, TypeOK, Messages
                <9>2. \A q \in Q, w \in Values : VotedForIn(q, w, c, d.slot) => w = d.val
                  BY <9>1, VotedOnce, QuorumAssumption, SMTT(200) DEF TypeOK, Messages
                <9>3. \A q \in Q : acceptorMaxBal[q] > c
                  BY DEF MsgInv, TypeOK, Messages
                <9>. QED
                  BY <8>2, <9>2, <9>3 DEF WontVoteIn
            <8>3. CASE c \in 0..max-1
                <9>0. \E a \in Acceptors, mm \in S :
                        /\ mm.from = a
                        /\ \E dd \in mm.voted : /\ dd.bal = d.bal
                                                /\ dd.val = d.val
                                                /\ dd.slot = d.slot
                  BY <8>2, <8>11 DEF MaxVotedBallotInSlot, TypeOK, Messages, Maximum
                <9>1. \E a \in Acceptors : VotedForIn(a, d.val, d.bal, d.slot)
                  BY <8>2,<8>0 DEF MsgInv, TypeOK, Messages
                <9>4. SafeAt(d.val, d.bal, d.slot)
                  BY <9>1, VotedInv DEF TypeOK, Messages
                <9>. QED
                  BY <8>3, <9>4, <8>11 DEF SafeAt, MsgInv, TypeOK, Messages, MaxVotedBallotInSlot
            <8> QED BY <8>1, <8>2, <8>3, <8>6
          <7>17. PartialBmax(VS) \in SUBSET [bal : Ballots, val : Values, slot : Slots]
            BY DEF PartialBmax, TypeOK, Messages
          <7>30. b \in Ballots
            BY DEF TypeOK
          <7>16. \A d \in PartialBmax(VS) : SafeAt(d.val, b, d.slot)'
            BY <7>15, SafeAtStable, <3>1, <7>17, <2>1
          <7>18. \A d \in Bmax(VS) : SafeAt(d.val, b, d.slot)'
            BY <7>16, <7>17 DEF Bmax
          <7>19. \A d \in Bmax(VS) \cup NewProposals(VS) : SafeAt(d.val, b, d.slot)'
            BY <7>18, <7>14 
          <7>20. (\A mm \in msgs: mm.type = "2a" => \A d \in mm.decrees : SafeAt(d.val, mm.bal, d.slot))'
            <8> SUFFICES ASSUME NEW mm \in msgs',
                                (mm.type = "2a")',
                                NEW d \in mm.decrees
                         PROVE  (SafeAt(d.val, mm.bal, d.slot))'
              OBVIOUS
            <8>1. CASE mm \in msgs
              BY <3>1, SafeAtStable, <8>1, <2>1 DEF MsgInv, Messages, TypeOK
            <8>2. CASE mm \in msgs' \ msgs
              <9>1. mm.decrees = ProposeDecrees(VS)
                BY <8>2 DEF Send, TypeOK, Messages
              <9>3. SafeAt(d.val, mm.bal, d.slot)'
                BY <9>1, <7>19, <8>2 DEF Send, ProposeDecrees
              <9> QED
              BY <3>1, <9>3 DEF Send, TypeOK, Messages
            <8> QED BY <8>1, <8>2
          <7> QED BY <7>20
        <6>2. (\A d1,d2 \in m.decrees : d1.slot = d2.slot => d1 = d2)'
          <7>11. \A r1, r2 \in VS : r1.bal = r2.bal /\ r1.slot = r2.slot => r1.val = r2.val
            BY VotedUnion
          <7>7. \A mmm \in msgs' \ msgs : \A d1,d2 \in mmm.decrees : d1.slot = d2.slot => d1 = d2
            <8>4. VS \in SUBSET [bal : Ballots, slot : Slots, val : Values]
              BY DEF Messages, TypeOK
            <8>3. \A r1, r2 \in PartialBmax(VS) : r1.slot = r2.slot => r1.bal = r2.bal
              BY <8>4 DEF PartialBmax
            <8>5. PartialBmax(VS) \in SUBSET [bal : Ballots, slot : Slots, val : Values]
              BY <8>4 DEF PartialBmax
            <8>6. PartialBmax(VS) \subseteq VS
              BY <8>4 DEF PartialBmax
            <8>7. \A r1, r2 \in PartialBmax(VS) :
              r1.bal = r2.bal /\ r1.slot = r2.slot => r1.val = r2.val
              BY <8>6, VotedUnion
            <8>10. \A d1,d2 \in PartialBmax(VS) : d1.slot = d2.slot => d1.bal = d2.bal /\ d1.val = d2.val
              BY <8>3, <8>7, <8>5
            <8>2. \A d1, d2 \in Bmax(VS) : d1.slot = d2.slot => d1.val = d2.val
              BY <8>10 DEF Bmax
            <8>21. Bmax(VS) \in SUBSET [slot : Slots, val : Values]
              BY <8>5 DEF Bmax 
            <8>9. \A d1, d2 \in Bmax(VS) : d1.slot = d2.slot => d1 = d2
              BY <8>2, <8>21 DEF Bmax
            <8>12. ~(\E d1 \in Bmax(VS), d2 \in NewProposals(VS) : d1.slot = d2.slot)
              BY NPC
            <8>16. \A mmm \in msgs' \ msgs : mmm.decrees = ProposeDecrees(VS)
              BY DEF Send
            <8> QED BY SMTT(500), <8>16, <8>9, <8>12, NPC DEF ProposeDecrees
          <7> QED BY <7>7 DEF MsgInv
        <6>3. (\A ma \in msgs : (ma.type = "2a") /\ (ma.bal = m.bal)
                                   => (ma = m))'
          <7>1. \A mm \in msgs' \ msgs : mm.type = "2a" /\ mm.bal = b
            BY <5>0
          <7>2. \A mm \in msgs : (mm.type = "2a") => (mm.bal # b)
            BY <4>3 DEF Phase2a
          <7>6. \A m1, m2 \in msgs' \ msgs : m1 = m2
            BY <4>3 DEF Phase2a, Send
          <7> QED BY <7>2, <7>6, <7>1, <2>1, <3>1 DEF MsgInv
        <6>4. QED
          BY <6>1, <6>2, <6>3
      <5>3. ((m.type = "2b") => 
               /\ \E ma \in msgs : /\ ma.type = "2a"
                                   /\ ma.bal  = m.bal
                                   /\ ma.decrees = m.decrees
               /\ m.bal =< acceptorMaxBal[m.from])'
        <6> SUFFICES ASSUME (m.type = "2b")'
                     PROVE  (/\ \E ma \in msgs : /\ ma.type = "2a"
                                                 /\ ma.bal  = m.bal
                                                 /\ ma.decrees = m.decrees
                             /\ m.bal =< acceptorMaxBal[m.from])'
          OBVIOUS
        <6>0. m \in msgs
          BY <5>0
        <6>1. (\E ma \in msgs : /\ ma.type = "2a"
                                /\ ma.bal  = m.bal
                                /\ ma.decrees = m.decrees)'
          BY <6>0, <3>1, <4>3 DEF TypeOK, Messages, MsgInv, Phase2a, Send
        <6>2. (m.bal =< acceptorMaxBal[m.from])'
          BY <5>0, <4>3, <3>1 DEF Phase2a, TypeOK, Messages, MsgInv
        <6>3. QED
          BY <6>1, <6>2
        
      <5>4. QED
        BY <5>1, <5>2, <5>3
    <4>4. ASSUME NEW a \in Acceptors, Phase2b(a) PROVE  MsgInv'
      <5> SUFFICES ASSUME NEW m \in msgs'
                   PROVE  (/\ (m.type = "1b") =>
                                /\ m.bal =< acceptorMaxBal[m.from]
                                /\ \A r \in m.voted : VotedForIn(m.from, r.val, r.bal, r.slot)
                                /\ \A s \in Slots, v \in Values, c \in Ballots :
                                   c \in MaxVotedBallotInSlot(m.voted, s)+1..m.bal-1 =>
                                       ~ VotedForIn(m.from, v, c, s)
                           /\ (m.type = "2a") => 
                                /\ \A d \in m.decrees : SafeAt(d.val, m.bal, d.slot)
                                /\ \A d1,d2 \in m.decrees : d1.slot = d2.slot => d1 = d2
                                /\ \A ma \in msgs : (ma.type = "2a") /\ (ma.bal = m.bal)
                                                       => (ma = m)
                           /\ (m.type = "2b") => 
                                /\ \E ma \in msgs : /\ ma.type = "2a"
                                                    /\ ma.bal  = m.bal
                                                    /\ ma.decrees = m.decrees
                                /\ m.bal =< acceptorMaxBal[m.from])'
        BY DEF MsgInv
      <5>. PICK m1 \in msgs : Phase2b(a)!(m1)
        BY <4>4 DEF Phase2b
      <5>0. \A aa \in Acceptors, vv \in Values, bb \in Ballots, ss \in Slots:
                VotedForIn(aa, vv, bb, ss) => VotedForIn(aa, vv, bb, ss)'
        BY DEF VotedForIn, Send
      <5>10. \A aa \in Acceptors \ {a}, vv \in Values, bb \in Ballots, ss \in Slots:
                VotedForIn(aa, vv, bb, ss) <=> VotedForIn(aa, vv, bb, ss)'
        BY DEF VotedForIn, Send
      <5>1. ((m.type = "1b") =>
               /\ m.bal =< acceptorMaxBal[m.from]
               /\ \A r \in m.voted : VotedForIn(m.from, r.val, r.bal, r.slot)
               /\ \A s \in Slots, v \in Values, c \in Ballots :
                  c \in MaxVotedBallotInSlot(m.voted, s)+1..m.bal-1 =>
                      ~ VotedForIn(m.from, v, c, s))'
        <6> SUFFICES ASSUME (m.type = "1b")'
                     PROVE  (/\ m.bal =< acceptorMaxBal[m.from]
                             /\ \A r \in m.voted : VotedForIn(m.from, r.val, r.bal, r.slot)
                             /\ \A s \in Slots, v \in Values, c \in Ballots :
                                c \in MaxVotedBallotInSlot(m.voted, s)+1..m.bal-1 =>
                                    ~ VotedForIn(m.from, v, c, s))'
          OBVIOUS
        <6>1. (m.bal =< acceptorMaxBal[m.from])'
          BY <3>1, <4>4, <5>0 DEF MsgInv, TypeOK, Messages, Phase2b, Send, MaxVotedBallotInSlot, VotedForIn
        <6>2. (\A r \in m.voted : VotedForIn(m.from, r.val, r.bal, r.slot))'
          BY <3>1, <4>4, <5>0 DEF MsgInv, TypeOK, Messages, Phase2b, Send
        <6>3. (\A s \in Slots, v \in Values, c \in Ballots :
               c \in MaxVotedBallotInSlot(m.voted, s)+1..m.bal-1 =>
                   ~ VotedForIn(m.from, v, c, s))'
          <7> SUFFICES ASSUME NEW s \in Slots', NEW v \in Values', NEW c \in Ballots',
                              (c \in MaxVotedBallotInSlot(m.voted, s)+1..m.bal-1)'
                       PROVE  (~ VotedForIn(m.from, v, c, s))'
            OBVIOUS
          <7>0. ~ VotedForIn(m.from, v, c, s)
            BY DEF Send, MsgInv, TypeOK, Messages
          <7>1. CASE m.from # a
            BY <3>1, <5>10, <7>1, <7>0 DEF TypeOK, Messages, Send
          <7>2. CASE m.from = a
            <8>1. CASE ~(m1.bal >= acceptorMaxBal[a])
              BY <8>1, <7>0 DEF Send, VotedForIn
            <8>2. CASE (m1.bal >= acceptorMaxBal[a])
                <9>2. acceptorMaxBal'[a] = m1.bal
                  BY <8>2 DEF TypeOK, Messages
                <9>1. \A mm \in msgs' \ msgs : mm.bal = m1.bal
                  BY <8>2, <6>1, <7>2 DEF Send, TypeOK
                <9>4. m1.bal # c
                  BY <8>2, <6>1, <7>2 DEF TypeOK, Messages
                <9>5. \A mm \in msgs' \ msgs : mm.bal # c
                  BY <9>1, <9>4
                <9> QED BY <8>2, <7>0, <9>5 DEF VotedForIn, TypeOK, Messages
            <8> QED BY <8>1, <8>2          
          <7> QED BY <7>1, <7>2 DEF TypeOK, Messages
        <6>4. QED
          BY <6>1, <6>2, <6>3
      <5>2. ((m.type = "2a") => 
               /\ \A d \in m.decrees : SafeAt(d.val, m.bal, d.slot)
               /\ \A d1,d2 \in m.decrees : d1.slot = d2.slot => d1 = d2
               /\ \A ma \in msgs : (ma.type = "2a") /\ (ma.bal = m.bal)
                                      => (ma = m))'
        BY SafeAtStable, <3>1, <4>4, <2>1 DEF MsgInv, TypeOK, Messages, Phase2b, Send
      <5>3. ((m.type = "2b") => 
               /\ \E ma \in msgs : /\ ma.type = "2a"
                                   /\ ma.bal  = m.bal
                                   /\ ma.decrees = m.decrees
               /\ m.bal =< acceptorMaxBal[m.from])'
        <6>1. CASE ~ (m1.bal >= acceptorMaxBal[a])
          BY <3>1, <6>1 DEF TypeOK, Messages, Send, MsgInv
        <6>2. CASE m1.bal >= acceptorMaxBal[a]
          <7>1. CASE m \in msgs
            BY <3>1, <6>2, <7>1 DEF TypeOK, Send, MsgInv, Messages
          <7>2. CASE m \in msgs' \ msgs
            BY <3>1, <6>2, <7>2 DEF TypeOK, Send
          <7> QED BY <7>2, <7>1
        <6> QED BY <6>1, <6>2
      <5>4. QED
        BY <5>1, <5>2, <5>3
    <4>. QED
      BY <4>1, <4>2, <4>3, <4>4, <2>1 DEF Next
  <3>4. QED
    BY <3>1, <3>2, <3>3 DEF Inv, vars, Next
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEF vars, Inv, TypeOK, AccInv, MsgInv, VotedForIn, SafeAt, WontVoteIn, MaxVotedBallotInSlot
  <2>3. QED
    BY <2>1, <2>2
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Consistent == Spec => []Consistency
<1> USE DEF Ballots
  
<1>1. Inv => Consistency
  <2> SUFFICES ASSUME Inv,  
                      NEW v1 \in Values,  NEW v2 \in Values, 
                      NEW b1 \in Ballots, NEW b2 \in Ballots,
                      NEW s \in Slots,
                      ChosenIn(v1, b1, s), ChosenIn(v2, b2, s),
                      b1 =< b2
               PROVE  v1 = v2
    BY DEF Consistency, Chosen
  <2>1. CASE b1 = b2
    <3>1. \E a \in Acceptors : VotedForIn(a, v1, b1, s) /\ VotedForIn(a, v2, b1, s)
      BY <2>1, QuorumAssumption DEF ChosenIn
    <3> QED 
    BY <3>1, VotedOnce DEF Inv
  <2>2. CASE b1 < b2
    <3>1. SafeAt(v2, b2, s)
      BY VotedInv, QuorumNonEmpty, QuorumAssumption DEF ChosenIn, Inv
    <3>2. PICK Q2 \in Quorums : 
                  \A a \in Q2 : VotedForIn(a, v2, b1, s) \/ WontVoteIn(a, b1, s)
      BY <3>1, <2>2 DEF SafeAt
    <3>3. PICK Q1 \in Quorums : \A a \in Q1 : VotedForIn(a, v1, b1, s)
      BY DEF ChosenIn
    <3>4. QED
      BY <3>2, <3>3, QuorumAssumption, VotedOnce, Z3 DEF WontVoteIn, Inv
  <2>3. QED
    BY <2>1, <2>2

<1>2. QED
  BY Invariant, <1>1, PTL

=============
