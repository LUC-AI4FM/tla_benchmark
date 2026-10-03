------------------------------ MODULE LockWithAux ------------------------------

EXTENDS Naturals

CONSTANT Proc

(*
We assume a two-process system, intended to refine Peterson's algorithm.
If desired, replace this ASSUME with a more abstract two-element set.
*)
ASSUME Proc = {0, 1}

(*
Auxiliary operator: the other process.
*)
Other(p) == CHOOSE q \in Proc: q # p

VARIABLES
    pc,      \* process control: "idle", "trying", "critical"
    s,       \* stuttering counter to mimic 3-step entry protocol
    h_turn   \* history variable tracking the most recent assignment to Peterson's turn

Vars == << pc, s, h_turn >>

(*
State typing and basic safety invariants.
*)
TypeInv ==
    /\ pc \in [Proc -> {"idle", "trying", "critical"}]
    /\ s \in [Proc -> 0..3]
    /\ h_turn \in Proc

MutualExclusion ==
    \A p \in Proc: \A q \in Proc:
        p # q => ~(pc[p] = "critical" /\ pc[q] = "critical")

StutterInv ==
    \A p \in Proc: s[p] > 0 => pc[p] = "trying"

Safety == TypeInv /\ MutualExclusion /\ StutterInv

(*
Initial state: everyone idle, no stuttering, and turn history set to some process.
*)
Init ==
    /\ pc = [p \in Proc |-> "idle"]
    /\ s = [p \in Proc |-> 0]
    /\ h_turn \in Proc

(*
Actions of the lock protocol with auxiliary variables.
*)

Try(p) ==
    /\ p \in Proc
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "trying"]
    /\ s'  = [s  EXCEPT ![p] = 3]
    /\ h_turn' = Other(p)

Stutter(p) ==
    /\ p \in Proc
    /\ pc[p] = "trying"
    /\ s[p] > 0
    /\ pc' = pc
    /\ s'  = [s EXCEPT ![p] = s[p] - 1]
    /\ h_turn' = h_turn

Enter(p) ==
    /\ p \in Proc
    /\ pc[p] = "trying"
    /\ s[p] = 0
    /\ LET q == Other(p) IN (pc[q] # "trying" \/ h_turn = p)
    /\ pc' = [pc EXCEPT ![p] = "critical"]
    /\ s' = s
    /\ h_turn' = h_turn

Exit(p) ==
    /\ p \in Proc
    /\ pc[p] = "critical"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ s' = [s EXCEPT ![p] = 0]
    /\ h_turn' = h_turn

Next ==
    \E p \in Proc:
        Try(p) \/ Stutter(p) \/ Enter(p) \/ Exit(p)

(*
System specification with fairness to drive the stuttering countdown
and eventual entry when enabled.
*)
Spec ==
    Init /\ [][Next]_Vars /\
    (\A p \in Proc: WF_Vars(Stutter(p)) /\ WF_Vars(Enter(p)))

(*
Relating to Peterson's algorithm via a definitional instantiation.
We define a parameterized Peterson specification and instantiate it
with:
  - flag[p]  = (pc[p] /= "idle")
  - turn     = h_turn
  - pcP[p]   = "ncs" when idle, "cs" when critical, "try" otherwise
*)

(*
Parameterized Peterson actions and spec (two-process version).
flag: [Proc -> BOOLEAN]
turn: element of Proc
pcP:  [Proc -> {"ncs","try","cs"}]
*)
TryP(p, flag, turn, pcP) ==
    /\ p \in Proc
    /\ pcP[p] = "ncs"
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ turn' = Other(p)
    /\ pcP'  = [pcP  EXCEPT ![p] = "try"]

EnterP(p, flag, turn, pcP) ==
    /\ p \in Proc
    /\ pcP[p] = "try"
    /\ LET q == Other(p) IN (~flag[q] \/ turn = p)
    /\ pcP'  = [pcP EXCEPT ![p] = "cs"]
    /\ flag' = flag
    /\ turn' = turn

ExitP(p, flag, turn, pcP) ==
    /\ p \in Proc
    /\ pcP[p] = "cs"
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ pcP'  = [pcP  EXCEPT ![p] = "ncs"]
    /\ turn' = turn

PetersonInit(flag, turn, pcP) ==
    /\ \A p \in Proc: ~flag[p]
    /\ \A p \in Proc: pcP[p] = "ncs"
    /\ turn \in Proc

PetersonNext(flag, turn, pcP) ==
    \E p \in Proc: TryP(p, flag, turn, pcP) \/ EnterP(p, flag, turn, pcP) \/ ExitP(p, flag, turn, pcP)

PetersonSpec(flag, turn, pcP) ==
    PetersonInit(flag, turn, pcP)
    /\ [] [PetersonNext(flag, turn, pcP)]_<< flag, turn, pcP >>
    /\ (\A p \in Proc: WF_<< flag, turn, pcP >>(EnterP(p, flag, turn, pcP)))

(*
Instantiation (substitution) to relate this lock spec to Peterson's:
*)
PFlag == [p \in Proc |-> pc[p] # "idle"]
PTurn == h_turn
PPC   == [p \in Proc |-> IF pc[p] = "idle" THEN "ncs"
                          ELSE IF pc[p] = "critical" THEN "cs"
                          ELSE "try"]

PTSpec == PetersonSpec(PFlag, PTurn, PPC)

=============================================================================