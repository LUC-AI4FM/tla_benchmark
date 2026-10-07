----------------------------- MODULE OneStepByzConsensus -----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    N,          \* Number of processes
    F,          \* Maximum number of Byzantine faulty processes tolerated
    T           \* Decision threshold parameter

ASSUME
    /\ N \in Nat /\ N > 0
    /\ F \in Nat /\ F < N
    /\ T \in Nat /\ T >= 0 /\ T <= N
    /\ N >= 3 * F + 1
    /\ F < T /\ T <= N - F

(*
  A folklore one-step consensus model with Byzantine faults (binary values).
  Each process has a fixed input bit. Nonfaulty processes broadcast their bit
  once (Propose) to all. Faulty processes may behave arbitrarily and may
  equivocate. Each process locally collects what has been "received" for it
  from the global sent matrix and, if it has at least T reports for some bit v,
  it may decide v. The model allows checking safety/liveness under different N,F,T.
*)

(***************************************************************************)
(* Sets and basic definitions                                              *)
(***************************************************************************)

Proc   == 1..N
Values == {0, 1}
NoMsg  == "NoMsg"
MsgVals == Values \cup {NoMsg}

IsCorrect(p) == p \in Proc /\ ~(p \in faulty)

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES
    faulty,     \* SUBSET Proc: current set of faulty processes
    input,      \* [Proc -> Values]: fixed input/proposal bit per process
    proposed,   \* [Proc -> BOOLEAN]: has the process performed its broadcast?
    sent,       \* [Proc -> [Proc -> MsgVals]]: message matrix (what s "sent" to r)
    recvd,      \* [Proc -> [Proc -> MsgVals]]: local view of what each receiver has "received"
    nsent,      \* [Proc -> Nat]: number of non-absent messages a process has sent
    nrecv,      \* [Proc -> Nat]: number of non-absent messages a process has in its local view
    decided,    \* [Proc -> BOOLEAN]: has the process decided?
    decision    \* [Proc -> Values]: the decision value (meaningful iff decided[p])
    
vars == << faulty, input, proposed, sent, recvd, nsent, nrecv, decided, decision >>

(***************************************************************************)
(* Typing and structural invariants                                        *)
(***************************************************************************)

TypeOK ==
    /\ faulty \subseteq Proc
    /\ input \in [Proc -> Values]
    /\ proposed \in [Proc -> BOOLEAN]
    /\ sent \in [Proc -> [Proc -> MsgVals]]
    /\ recvd \in [Proc -> [Proc -> MsgVals]]
    /\ nsent \in [Proc -> Nat]
    /\ nrecv \in [Proc -> Nat]
    /\ decided \in [Proc -> BOOLEAN]
    /\ decision \in [Proc -> Values]

FaultyBound == Cardinality(faulty) <= F

ConsistentCounts ==
    /\ \A p \in Proc:
         nsent[p] = Cardinality({ r \in Proc : sent[p][r] \in Values })
    /\ \A p \in Proc:
         nrecv[p] = Cardinality({ s \in Proc : recvd[p][s] \in Values })

(***************************************************************************)
(* Initial states                                                          *)
(***************************************************************************)

AllZeroInit ==
    /\ faulty = {}
    /\ input = [p \in Proc |-> 0]
    /\ proposed = [p \in Proc |-> FALSE]
    /\ sent = [p \in Proc |-> [r \in Proc |-> NoMsg]]
    /\ recvd = [p \in Proc |-> [r \in Proc |-> NoMsg]]
    /\ nsent = [p \in Proc |-> 0]
    /\ nrecv = [p \in Proc |-> 0]
    /\ decided = [p \in Proc |-> FALSE]
    /\ decision = [p \in Proc |-> 0]

AllOneInit ==
    /\ faulty = {}
    /\ input = [p \in Proc |-> 1]
    /\ proposed = [p \in Proc |-> FALSE]
    /\ sent = [p \in Proc |-> [r \in Proc |-> NoMsg]]
    /\ recvd = [p \in Proc |-> [r \in Proc |-> NoMsg]]
    /\ nsent = [p \in Proc |-> 0]
    /\ nrecv = [p \in Proc |-> 0]
    /\ decided = [p \in Proc |-> FALSE]
    /\ decision = [p \in Proc |-> 1]

Init == AllZeroInit \/ AllOneInit

(***************************************************************************)
(* Helper operators                                                        *)
(***************************************************************************)

CountVal(recMap, v) == Cardinality({ s \in Proc : recMap[s] = v })

(***************************************************************************)
(* Main nonfaulty step (propose + receive + optional decide)               *)
(***************************************************************************)

Step(p) ==
    /\ p \in Proc /\ ~(p \in faulty)
    LET
        newRow ==
            IF ~proposed[p]
            THEN [r \in Proc |-> input[p]]
            ELSE sent[p]
        newSent ==
            [sent EXCEPT ![p] = newRow]
        newNsentP ==
            IF ~proposed[p]
            THEN N
            ELSE nsent[p]
        newRecvdP ==
            [s \in Proc |-> IF newSent[s][p] \in Values THEN newSent[s][p] ELSE NoMsg]
        c0 == CountVal(newRecvdP, 0)
        c1 == CountVal(newRecvdP, 1)
        canDecide == { v \in Values : IF v = 0 THEN c0 >= T ELSE c1 >= T }
    IN
    /\ sent'     = newSent
    /\ proposed' = [proposed EXCEPT ![p] = TRUE]
    /\ nsent'    = [nsent EXCEPT ![p] = newNsentP]
    /\ recvd'    = [recvd EXCEPT ![p] = newRecvdP]
    /\ nrecv'    = [nrecv EXCEPT ![p] = Cardinality({ s \in Proc : newRecvdP[s] \in Values })]
    /\ IF (canDecide # {}) /\ ~decided[p]
       THEN
            LET v == CHOOSE vv \in canDecide : TRUE IN
            /\ decided'  = [decided EXCEPT ![p] = TRUE]
            /\ decision' = [decision EXCEPT ![p] = v]
       ELSE
            /\ decided'  = decided
            /\ decision' = decision
    /\ UNCHANGED << faulty, input >>

MainStep == \E p \in Proc : Step(p)

(***************************************************************************)
(* Byzantine actions                                                       *)
(***************************************************************************)

BecomeFaulty(p) ==
    /\ p \in Proc /\ ~(p \in faulty)
    /\ Cardinality(faulty) < F
    /\ faulty' = faulty \cup {p}
    /\ UNCHANGED << input, proposed, sent, recvd, nsent, nrecv, decided, decision >>

ByzSend(p, r, m) ==
    /\ p \in Proc /\ p \in faulty
    /\ r \in Proc
    /\ m \in MsgVals
    LET
        row2 == [sent[p] EXCEPT ![r] = m]
    IN
    /\ sent'  = [sent EXCEPT ![p] = row2]
    /\ nsent' = [nsent EXCEPT ![p] = Cardinality({ rr \in Proc : row2[rr] \in Values })]
    /\ UNCHANGED << faulty, input, proposed, recvd, nrecv, decided, decision >>

ByzantineAction == \E p \in Proc :
                      BecomeFaulty(p)
                   \/ \E r \in Proc, m \in MsgVals : ByzSend(p, r, m)

(***************************************************************************)
(* Next-state relation and Spec                                            *)
(***************************************************************************)

Next == MainStep \/ ByzantineAction

Spec == Init /\ [][Next]_vars /\ WF_vars(MainStep)

(***************************************************************************)
(* Safety properties (invariants)                                          *)
(***************************************************************************)

AgreementInv ==
    \A p \in Proc : \A q \in Proc :
        (IsCorrect(p) /\ IsCorrect(q) /\ decided[p] /\ decided[q]) => (decision[p] = decision[q])

AllZeroInputs == \A p \in Proc : input[p] = 0
AllOneInputs  == \A p \in Proc : input[p] = 1

ValidityInv ==
    /\ (AllZeroInputs => (\A p \in Proc : (IsCorrect(p) /\ decided[p]) => decision[p] = 0))
    /\ (AllOneInputs  => (\A p \in Proc : (IsCorrect(p) /\ decided[p]) => decision[p] = 1))

Safety == TypeOK /\ FaultyBound /\ ConsistentCounts /\ AgreementInv /\ ValidityInv

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

AllCorrectDecided == \A p \in Proc : IsCorrect(p) => decided[p]

Termination == <> AllCorrectDecided

====================================================================================