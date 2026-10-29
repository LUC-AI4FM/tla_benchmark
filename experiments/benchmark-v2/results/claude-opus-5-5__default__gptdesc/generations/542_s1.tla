---------------------------- MODULE TwoProcIncrement ----------------------------
EXTENDS Naturals, TLC

(* --algorithm TwoProcIncrement
variables x = 0;

process ProcA = "A"
begin
  IncA: x := x + 1;
end process;

process ProcB = "B"
begin
  IncB: x := x + 1;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

ProcSet == {"A"} \cup {"B"}

Init == /\ x = 0
        /\ pc = [self \in ProcSet |-> CASE self = "A" -> "IncA"
                                        [] self = "B" -> "IncB"]

IncA == /\ pc["A"] = "IncA"
        /\ x' = x + 1
        /\ pc' = [pc EXCEPT !["A"] = "Done"]

ProcA == IncA

IncB == /\ pc["B"] = "IncB"
        /\ x' = x + 1
        /\ pc' = [pc EXCEPT !["B"] = "Done"]

ProcB == IncB

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == ProcA \/ ProcB \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

\* END TRANSLATION

-----------------------------------------------------------------------------

TypeOK == /\ x \in 0..2
          /\ pc \in [ProcSet -> {"IncA", "IncB", "Done"}]

FinalValue == (\A self \in ProcSet : pc[self] = "Done") => x = 2

=============================================================================