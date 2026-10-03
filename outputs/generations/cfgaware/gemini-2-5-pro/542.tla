------------------------ MODULE TwoProcIncrement ------------------------
EXTENDS Integers, TLC

VARIABLES x, pc

ProcSet == {"ProcA", "ProcB"}

vars == <<x, pc>>

\* --algorithm TwoProc
\* begin
\*   variable x = 0;
\*   process ProcA
\*   begin Lbl_1:
\*     x := x + 1;
\*   end process;
\*   process ProcB
\*   begin Lbl_1:
\*     x := x + 1;
\*   end process
\* end algorithm

Init ==
  /\ x = 0
  /\ pc = [p \in ProcSet |-> "Lbl_1"]

A ==
  /\ pc["ProcA"] = "Lbl_1"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT !["ProcA"] = "Done"]

B ==
  /\ pc["ProcB"] = "Lbl_1"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT !["ProcB"] = "Done"]

Terminated == \A p \in ProcSet : pc[p] = "Done"

Terminating == Terminated /\ UNCHANGED vars

Next ==
  \/ A
  \/ B
  \/ Terminating

Termination == <>Terminated

Spec == Init /\ [][Next]_vars /\ Termination

=============================================================================