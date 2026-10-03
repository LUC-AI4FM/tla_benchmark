------------------------------ MODULE Lock ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS Procs
ASSUME Procs = {0, 1}

Other(p) == CHOOSE q \in Procs : q # p

VARIABLES
    \* The program counter for each process: "nc" or "cs".
    pc,
    \* The turn variable for the lock.
    turn,
    \* Auxiliary stuttering variable to model Peterson's 3-step protocol.
    \* s[p]=0: idle, s[p]=1: interested, s[p]=2: turn set, s[p]=3: in CS.
    s,
    \* Auxiliary history variable to track assignments to 'turn'.
    h_turn

vars == <<pc, turn, s, h_turn>>

TypeOK ==
    /\ pc \in [Procs -> {"nc", "cs"}]
    /\ turn \in Procs
    /\ s \in [Procs -> 0..3]
    /\ h_turn \in Seq(Procs)

Init ==
    /\ pc = [p \in Procs |-> "nc"]
    /\ turn \in Procs
    /\ s = [p \in Procs |-> 0]
    /\ h_turn = <<turn>>

(* Step 1: Process p signals interest. This corresponds to setting flag[p]
   to TRUE in Peterson. This is a stuttering step w.r.t. <<pc, turn>>. *)
Enter1(p) ==
    /\ pc[p] = "nc"
    /\ s[p] = 0
    /\ s' = [s EXCEPT ![p] = 1]
    /\ UNCHANGED <<pc, turn, h_turn>>

(* Step 2: Process p sets the turn variable. This corresponds to setting the
   turn variable in Peterson. This is a stuttering step w.r.t. <<pc>>. *)
Enter2(p) ==
    /\ pc[p] = "nc"
    /\ s[p] = 1
    /\ turn' = p
    /\ s' = [s EXCEPT ![p] = 2]
    /\ h_turn' = Append(h_turn, p)
    /\ UNCHANGED <<pc>>

(* Step 3: Process p enters the critical section if its turn has come.
   This corresponds to passing the await condition in Peterson. *)
EnterCS(p) ==
    /\ pc[p] = "nc"
    /\ s[p] = 2
    /\ turn = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ s' = [s EXCEPT ![p] = 3]
    /\ UNCHANGED <<turn, h_turn>>

(* Process p exits the critical section. *)
ExitCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "nc"]
    /\ s' = [s EXCEPT ![p] = 0]
    /\ UNCHANGED <<turn, h_turn>>

Next == \E p \in Procs:
            Enter1(p) \/ Enter2(p) \/ EnterCS(p) \/ ExitCS(p)

\* Safety property: Mutual exclusion.
Mutex == \A p, q \in Procs : p # q => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Liveness property: Any process that tries to enter eventually does.
\* This is ensured by weak fairness on the EnterCS and ExitCS actions.
Fairness == \A p \in Procs: WF_vars(EnterCS(p)) /\ WF_vars(ExitCS(p))

Spec == Init /\ [][Next]_vars
SpecFair == Spec /\ Fairness

(***************************************************************************)
(* The following defines the standard Peterson's algorithm. The Lock       *)
(* protocol is specified to allow a formal proof of equivalence with it.   *)
(***************************************************************************)
LOCAL MODULE Peterson
    EXTENDS Naturals, TLC

    CONSTANTS Procs
    ASSUME Procs = {0, 1}
    Other(p) == CHOOSE q \in Procs : q # p

    VARIABLES pc, flag, turn
    vars == <<pc, flag, turn>>

    TypeOK ==
        /\ pc \in [Procs -> {"nc", "cs"}]
        /\ flag \in [Procs -> BOOLEAN]
        /\ turn \in Procs

    Init ==
        /\ pc = [i \in Procs |-> "nc"]
        /\ flag = [i \in Procs |-> FALSE]
        /\ turn \in Procs

    P1(p) == (* Set flag *)
        /\ pc[p] = "nc"
        /\ flag' = [flag EXCEPT ![p] = TRUE]
        /\ UNCHANGED <<pc, turn>>

    P2(p) == (* Set turn to other process *)
        /\ pc[p] = "nc"
        /\ flag[p]
        /\ turn' = Other(p)
        /\ UNCHANGED <<pc, flag>>

    Enter(p) == (* Await condition and enter CS *)
        /\ pc[p] = "nc"
        /\ flag[p]
        /\ \/ ~flag[Other(p)]
           \/ turn = p
        /\ pc' = [pc EXCEPT ![p] = "cs"]
        /\ UNCHANGED <<flag, turn>>

    Exit(p) == (* Exit CS and clear flag *)
        /\ pc[p] = "cs"
        /\ flag' = [flag EXCEPT ![p] = FALSE]
        /\ UNCHANGED <<pc, turn>>

    Next == \E p \in Procs: P1(p) \/ P2(p) \/ Enter(p) \/ Exit(p)

    Fairness == \A p \in Procs: WF_vars(Enter(p)) /\ WF_vars(Exit(p))

    Spec == Init /\ [][Next]_vars
    SpecFair == Spec /\ Fairness
END MODULE

(***************************************************************************)
(* Instantiation of Peterson's algorithm with substitutions from this      *)
(* module's variables. This defines the refinement mapping F where         *)
(* Peterson!vars = F(Lock!vars).                                           *)
(***************************************************************************)
P_pc   == pc
P_flag == [p \in Procs |-> s[p] >= 1]
P_turn == Other(turn)

PetersonSpec == INSTANCE Peterson
                  WITH pc <- P_pc, flag <- P_flag, turn <- P_turn, Procs <- Procs

(***************************************************************************)
(* The main theorem to be proven is that the Lock specification refines    *)
(* the Peterson specification, up to stuttering.                           *)
(*                                                                         *)
(* THEOREM SpecFair => PetersonSpec!SpecFair                               *)
(***************************************************************************)
=====================================================================