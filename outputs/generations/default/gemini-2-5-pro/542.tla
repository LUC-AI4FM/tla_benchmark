-------------------------- MODULE TwoIncrements --------------------------

EXTENDS Integers, TLC

CONSTANTS Procs
ASSUME Procs = {"ProcA", "ProcB"}

VARIABLES x, pc

vars == <<x, pc>>

(*
 * The set of possible values for the program counter.
 * "start": The initial location of a process.
 * "Done": The location of a process after it has finished its work.
 *)
PCValues == {"start", "Done"}

(*
 * TypeOK is a state invariant asserting that variables have the correct types.
 *)
TypeOK == /\ x \in Int
          /\ pc \in [Procs -> PCValues]

(*
 * The initial state of the system.
 * The shared variable x starts at 0.
 * Both processes start at the "start" location.
 *)
Init == /\ x = 0
        /\ pc = [self \in Procs |-> "start"]

(*
 * The action for process "ProcA". It can execute only when its pc is "start".
 * It increments the shared variable x and moves its pc to "Done".
 *)
ProcA == /\ pc["ProcA"] = "start"
         /\ x' = x + 1
         /\ pc' = [pc EXCEPT !["ProcA"] = "Done"]

(*
 * The action for process "ProcB". It can execute only when its pc is "start".
 * It increments the shared variable x and moves its pc to "Done".
 *)
ProcB == /\ pc["ProcB"] = "start"
         /\ x' = x + 1
         /\ pc' = [pc EXCEPT !["ProcB"] = "Done"]

(*
 * A predicate that is true if and only if all processes have finished.
 *)
Done == \A self \in Procs : pc[self] = "Done"

(*
 * An action that represents the system stuttering after termination.
 * This is enabled only when all processes are Done. It leaves all variables
 * unchanged. This is necessary to ensure the model does not deadlock upon
 * termination, which would violate liveness properties.
 *)
Terminating == Done /\ UNCHANGED vars

(*
 * The next-state relation. A step is either a ProcA step, a ProcB step,
 * or a Terminating (stuttering) step.
 *)
Next == ProcA \/ ProcB \/ Terminating

(*
 * The complete safety specification of the system.
 *)
Spec == Init /\ [][Next]_vars

(*
 * Fairness condition. To ensure termination, we must require that each
 * process action is weakly fair. This means that if a process action is
 * continuously enabled, it must eventually be executed.
 *)
Fairness == WF_vars(ProcA) /\ WF_vars(ProcB)

(*
 * The liveness property: The system eventually reaches a state where
 * all processes are done. This property holds under the Fairness assumption.
 *)
Termination == <>Done

=============================================================================