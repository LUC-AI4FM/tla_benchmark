------------------------------- MODULE ProgramWithComponent -------------------------------
EXTENDS Naturals, Integers

(***************************************************************************)
(* The reusable component is modeled abstractly as a deterministic         *)
(* numeric function of parameters fixed at "instantiation" time.  The      *)
(* parameters below play the role of the instantiation constants; the      *)
(* operator ComponentResult plays the role of the instantiated module's    *)
(* exported value.                                                         *)
(***************************************************************************)

\* Instantiation-time parameters of the component
ParamA == 2
ParamB == 3

\* Generic, reusable component: deterministic result from its parameters
Component(a, b) == a * b + a

\* The "instance" of the component, bound to the fixed parameters
ComponentResult == Component(ParamA, ParamB)

\* Known initial value of the program state
InitValue == 0

VARIABLES x, pc

vars == <<x, pc>>

TypeOK ==
    /\ x \in Int
    /\ pc \in {"compute", "Done"}

Init ==
    /\ x = InitValue
    /\ pc = "compute"

\* The single computation step: call the component, assign its result
Compute ==
    /\ pc = "compute"
    /\ x' = ComponentResult
    /\ pc' = "Done"

\* After termination, only stuttering is allowed
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Compute \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Compute)

----------------------------------------------------------------------------------------
\* Set of values the state may legitimately hold after the computation
ExpectedValues == {ComponentResult}

\* Safety: once terminated, x holds the component's result;
\* before termination, x still has its initial value
XCorrect ==
    /\ (pc = "Done") => (x \in ExpectedValues)
    /\ (pc = "compute") => (x = InitValue)

\* Liveness: the program eventually terminates
Termination == <>(pc = "Done")

\* No state changes after termination
StableAfterDone == [][(pc = "Done") => UNCHANGED vars]_vars

THEOREM Spec => [](TypeOK /\ XCorrect)
THEOREM Spec => Termination
THEOREM Spec => StableAfterDone
========================================================================================