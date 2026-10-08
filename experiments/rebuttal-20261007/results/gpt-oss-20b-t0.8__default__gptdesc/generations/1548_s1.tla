---- MODULE ByzantineConsensus ----
EXTENDS Naturals, Sequences

CONSTANTS N, F, T, UNDEF

Proc == 1 .. N

VARIABLES state, proposal, faulty, sentVals, decision

(* ------------------------------------------------------------------ *)
(* Initial states: all processes in Propose state and either all-0 or all-1 proposals. *)
Init ==
  /\ state = [i \in Proc |-> "Propose"]
  /\ (proposal = [i \in Proc |-> 0] \/ proposal = [i \in Proc |-> 1])
  /\ faulty = {}
  /\ sentVals = [i \in Proc |-> UNDEF]
  /\ decision = [i \in Proc |-> UNDEF]

(* ------------------------------------------------------------------ *)
(* Action: a process becomes Byzantine. *)
BecomeFaulty(i) ==
  /\ i \in Proc
  /\ i \notin faulty
  /\ faulty' = faulty \cup {i}
  /\ UNCHANGED <<state, proposal, sentVals, decision>>

(* ------------------------------------------------------------------ *)
(* Action: all processes send their value in one step. *)
AllSend ==
  /\ (\A i \in Proc : state[i] = "Propose")
  /\ sentVals' = [i \in Proc |-> 
                    IF i \in faulty THEN CHOOSE v \in {0,1} : TRUE
                                     ELSE proposal[i]]
  /\ state'   = [i \in Proc |-> "Send"]
  /\ UNCHANGED decision

(* ------------------------------------------------------------------ *)
(* Action: a process decides based on the received messages. *)
Decide(i) ==
  /\ state[i] = "Send"
  /\ let c0 == \# {j \in Proc \ {i} : sentVals[j] = 0}
       c1 == \# {j \in Proc \ {i} : sentVals[j] = 1} in
      (c0 >= T \/ c1 >= T)
  /\ decision' = [decision EXCEPT ![i] = IF c0 >= T THEN 0 ELSE 1]
  /\ state'    = [state EXCEPT ![i] = "Decide"]

(* ------------------------------------------------------------------ *)
(* Next-state relation. *)
Next ==
  (\E i \in Proc : BecomeFaulty(i))
  \/ AllSend
  \/ (\E i \in Proc : Decide(i))

(* ------------------------------------------------------------------ *)
(* Safety invariants. *)

FaultBound == \# faulty <= F

ConsensusInv ==
  (\A i, j \in Proc :
     (state[i] = "Decide" /\ state[j] = "Decide") =>
        decision[i] = decision[j])

Validity ==
  (\A v \in {0,1} :
     ((\A i \in Proc \ faulty : proposal[i] = v) =>
        (\E j \in Proc : state[j] = "Decide" /\ decision[j] = v)))

(* ------------------------------------------------------------------ *)
(* Specification. *)
Spec == Init
       /\ [][Next]_<<state, proposal, faulty, sentVals, decision>>
       /\ FaultBound
       /\ ConsensusInv
       /\ Validity
       /\ Fairness(Next)