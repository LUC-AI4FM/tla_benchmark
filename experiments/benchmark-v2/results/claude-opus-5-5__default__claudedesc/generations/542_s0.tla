---- MODULE Increment ----
EXTENDS Integers, TLC

(* --algorithm Increment
variables x = 0;

process ProcA = "A"
begin
  a: x := x + 1;
end process;

process ProcB = "B"
begin
  b: x := x + 1;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

ProcSet == {"A"} \cup {"B"}

Init == (* Global variables *)
        /\ x = 0
        /\ pc = [self \in ProcSet |-> CASE self = "A" -> "a"
                                        [] self = "B" -> "b"]

a == /\ pc["A"] = "a"
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT !["A"] = "Done"]

ProcA == a

b == /\ pc["B"] = "b"
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT !["B"] = "Done"]

ProcB == b

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ProcA \/ ProcB
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TypeOK == /\ x \in Int
          /\ pc \in [ProcSet -> {"a", "b", "Done"}]

FinalValue == (\A self \in ProcSet : pc[self] = "Done") => x = 2

====