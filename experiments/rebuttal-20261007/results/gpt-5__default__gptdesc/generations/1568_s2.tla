------------------------------ MODULE Bakery ------------------------------

EXTENDS Naturals

CONSTANTS N, MAXTICKET

ASSUME /\ N \in Nat /\ N >= 1
       /\ MAXTICKET \in Nat /\ MAXTICKET >= 1

Proc == 1..N

VARIABLES pc, choosing, number

vars == << pc, choosing, number >>

PCStates == {"idle", "choose", "setnum", "wait", "cs", "exit"}

TypeInv ==
  /\ pc \in [Proc -> PCStates]
  /\ choosing \in [Proc -> BOOLEAN]
  /\ number \in [Proc -> 0..MAXTICKET]

TicketBound == \A i \in Proc: number[i] \in 0..MAXTICKET

Nums(n) == { n[i] : i \in Proc }

MaxOf(S) == IF S = {} THEN 0
            ELSE CHOOSE m \in S : \A x \in S : m >= x

MaxNum(n) == MaxOf(Nums(n))

TicketLess(i, j, n) == n[i] < n[j] \/ (n[i] = n[j] /\ i < j)

AwaitOK(i) ==
  \A j \in Proc :
    (j = i)
    \/ ( /\ ~choosing[j]
         /\ ( number[j] = 0
              \/ TicketLess(i, j, number)
            )
       )

Init ==
  /\ pc = [ i \in Proc |-> "idle" ]
  /\ choosing = [ i \in Proc |-> FALSE ]
  /\ number = [ i \in Proc |-> 0 ]

Choose(i) ==
  /\ i \in Proc
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "choose"]
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ UNCHANGED number

SetNum(i) ==
  /\ i \in Proc
  /\ pc[i] = "choose"
  /\ MaxNum(number) < MAXTICKET
  /\ pc' = [pc EXCEPT ![i] = "setnum"]
  /\ number' = [number EXCEPT ![i] = MaxNum(number) + 1]
  /\ UNCHANGED choosing

Unchoose(i) ==
  /\ i \in Proc
  /\ pc[i] = "setnum"
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ UNCHANGED number

Await(i) ==
  /\ i \in Proc
  /\ pc[i] = "wait"
  /\ AwaitOK(i)
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << choosing, number >>

EnterCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED << choosing, number >>

ExitCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "exit"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ number' = [number EXCEPT ![i] = 0]
  /\ UNCHANGED choosing

Process(i) == Choose(i) \/ SetNum(i) \/ Unchoose(i) \/ Await(i) \/ EnterCS(i) \/ ExitCS(i)

Next == \E i \in Proc : Process(i)

Fairness == \A i \in Proc : WF_vars(Process(i))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion ==
  \A i, j \in Proc : i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")

Inv == TypeInv /\ TicketBound /\ MutualExclusion

=============================================================================