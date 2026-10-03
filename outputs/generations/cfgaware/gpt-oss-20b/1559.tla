---- MODULE LockProtocol ----
EXTENDS Naturals

CONSTANT N = 2

VARIABLES turn, flag, h_turn, s

(* Type constraints *)
TypeOKHS == 
   /\ turn \in 1..N
   /\ flag \in [1..N -> BOOLEAN]
   /\ h_turn \in 1..N
   /\ s \in Nat

(* Initial state *)
Init == 
   /\ turn = 1
   /\ flag = [i \in 1..N |-> FALSE]
   /\ h_turn = 1
   /\ s = 0

(* Actions for the lock protocol with history and stuttering *)
EntryStep(i) ==
   /\ i \in 1..N
   /\ flag' = [flag EXCEPT ![i] = TRUE]
   /\ UNCHANGED <<turn, h_turn>>
   /\ s' = 1

TurnStep(i) ==
   LET j \in 1..N /\ j /= i IN
   /\ IF flag[j] = FALSE \/ turn = i THEN
          /\ turn' = i
          /\ h_turn' = i
      ELSE
          /\ UNCHANGED <<turn, h_turn>>
   /\ s' = 2

StutterStep ==
   /\ s' = 3

ExitStep(i) ==
   /\ i \in 1..N
   /\ flag' = [flag EXCEPT ![i] = FALSE]
   /\ UNCHANGED <<turn, h_turn>>
   /\ s' = 0

Next == 
   \/ \E i \in 1..N : EntryStep(i)
   \/ \E i \in 1..N : TurnStep(i)
   \/ StutterStep
   \/ \E i \in 1..N : ExitStep(i)

SpecHS == Init /\ [][Next]_<<turn, flag, h_turn, s>>

(* Invariant about history variable *)
InvHS == 
   /\ h_turn = turn

LockInv == 
   (* Mutual exclusion: not both flags true simultaneously *)
   \A i,j \in 1..N : (i # j) => ~(flag[i] /\ flag[j])

Spec == SpecHS

(* Peterson specification for two processes *)
PetersonInit ==
   /\ turn = 1
   /\ flag = [i \in 1..N |-> FALSE]

PetersonEntry(i) ==
   /\ i \in 1..N
   /\ flag' = [flag EXCEPT ![i] = TRUE]
   /\ UNCHANGED <<turn>>

PetersonTurn(i) ==
   LET j \in 1..N /\ j /= i IN
   /\ IF flag[j] = FALSE \/ turn = i THEN
          /\ turn' = i
      ELSE
          /\ UNCHANGED turn

PetersonExit(i) ==
   /\ i \in 1..N
   /\ flag' = [flag EXCEPT ![i] = FALSE]
   /\ UNCHANGED turn

PetersonNext == 
   \/ \E i \in 1..N : PetersonEntry(i)
   \/ \E i \in 1..N : PetersonTurn(i)
   \/ \E i \in 1..N : PetersonExit(i)

PSpec == PetersonInit /\ [][PetersonNext]_<<turn, flag>>

====