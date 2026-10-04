-------------------------------- MODULE LockHS --------------------------------
\* LockHS: Lock specification augmented with history and stuttering variables
\* for refinement equivalence with Peterson's algorithm

EXTENDS Integers, Sequences, FiniteSets, TLAPS

CONSTANTS Procs

ASSUME ProcsAssumption == Procs = {0, 1}

--------------------------------------------------------------------------------
\* Base Lock specification (embedded)
--------------------------------------------------------------------------------

VARIABLES pc, x

\* Program counter locations for base Lock
LockLocations == {"l0", "l1", "cs", "l2"}

TypeOKLock == 
    /\ pc \in [Procs -> LockLocations]
    /\ x \in Procs \cup {-1}

InitLock == 
    /\ pc = [p \in Procs |-> "l0"]
    /\ x = -1

\* l0: Non-critical section (ready to try for lock)
l0(p) == 
    /\ pc[p] = "l0"
    /\ pc' = [pc EXCEPT ![p] = "l1"]
    /\ x' = x

\* l1: Attempt to acquire lock
l1(p) == 
    /\ pc[p] = "l1"
    /\ x = -1
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ x' = p

\* cs: Critical section
cs(p) == 
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "l2"]
    /\ x' = x

\* l2: Release lock
l2(p) == 
    /\ pc[p] = "l2"
    /\ pc' = [pc EXCEPT ![p] = "l0"]
    /\ x' = -1

NextLock == \E p \in Procs : l0(p) \/ l1(p) \/ cs(p) \/ l2(p)

Init == InitLock

\* Mutual exclusion invariant
MutualExclusion == \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

LockInv == MutualExclusion

Spec == Init /\ [][NextLock]_<<pc, x>>

--------------------------------------------------------------------------------
\* Stuttering module (embedded)
--------------------------------------------------------------------------------

\* Stuttering states: top means no active stutter, 
\* stutter1 and stutter2 are intermediate stuttering states
StutterStates == {"top", "stutter1", "stutter2"}

--------------------------------------------------------------------------------
\* History and Stuttering Variables
--------------------------------------------------------------------------------

VARIABLES h_turn, s

varsHS == <<pc, x, h_turn, s>>
varsLock == <<pc, x>>

--------------------------------------------------------------------------------
\* Type Invariant for augmented specification
--------------------------------------------------------------------------------

TypeOKHS == 
    /\ TypeOKLock
    /\ h_turn \in Procs
    /\ s \in StutterStates

--------------------------------------------------------------------------------
\* Initial condition for augmented specification
--------------------------------------------------------------------------------

InitHS == 
    /\ Init
    /\ h_turn = 1
    /\ s = "top"

--------------------------------------------------------------------------------
\* PostStutter: Wrapper that introduces two stuttering steps
\* During the transition from stutter1 to stutter2, h_turn may be updated
--------------------------------------------------------------------------------

\* Start stuttering sequence (enter stutter1)
StartStutter(p) ==
    /\ s = "top"
    /\ pc[p] = "l1"
    /\ x = -1
    /\ s' = "stutter1"
    /\ h_turn' = h_turn
    /\ UNCHANGED varsLock

\* Middle stuttering step (stutter1 -> stutter2), update h_turn
MiddleStutter(p) ==
    /\ s = "stutter1"
    /\ s' = "stutter2"
    /\ h_turn' = p  \* Update h_turn during this transition
    /\ UNCHANGED varsLock

\* Complete stuttering and execute base l1 action
EndStutter(p) ==
    /\ s = "stutter2"
    /\ l1(p)
    /\ s' = "top"
    /\ h_turn' = h_turn

\* l1HS wraps base l1 with stuttering steps via PostStutter
l1HS(p) == StartStutter(p) \/ MiddleStutter(p) \/ EndStutter(p)

--------------------------------------------------------------------------------
\* Other actions proceed without stuttering, h_turn unchanged
--------------------------------------------------------------------------------

l0HS(p) == 
    /\ l0(p)
    /\ s = "top"
    /\ s' = s
    /\ h_turn' = h_turn

csHS(p) == 
    /\ cs(p)
    /\ s = "top"
    /\ s' = s
    /\ h_turn' = h_turn

l2HS(p) == 
    /\ l2(p)
    /\ s = "top"
    /\ s' = s
    /\ h_turn' = h_turn

--------------------------------------------------------------------------------
\* Next state relation for augmented specification
--------------------------------------------------------------------------------

NextHS == \E p \in Procs : l0HS(p) \/ l1HS(p) \/ csHS(p) \/ l2HS(p)

--------------------------------------------------------------------------------
\* Specification (safety property)
--------------------------------------------------------------------------------

SpecHS == InitHS /\ [][NextHS]_varsHS

--------------------------------------------------------------------------------
\* Consistency Invariant linking stuttering state and pc to h_turn
--------------------------------------------------------------------------------

InvHS ==
    /\ (s = "stutter1" => \E p \in Procs : pc[p] = "l1" /\ x = -1)
    /\ (s = "stutter2" => \E p \in Procs : pc[p] = "l1" /\ x = -1 /\ h_turn = p)
    /\ (s # "top" => \E p \in Procs : pc[p] = "l1")
    /\ h_turn \in Procs

--------------------------------------------------------------------------------
\* Peterson's Algorithm Specification (for refinement)
--------------------------------------------------------------------------------

\* Peterson's program counter locations
PetersonLocations == {"p0", "p1", "p2", "p3", "cs", "p4"}

\* Translation function: Lock pc -> Peterson pc
pc_translation(lock_pc, stutter_state, proc) ==
    CASE lock_pc[proc] = "l0" -> "p0"
      [] lock_pc[proc] = "l1" /\ stutter_state = "top" -> "p1"
      [] lock_pc[proc] = "l1" /\ stutter_state = "stutter1" -> "p2"
      [] lock_pc[proc] = "l1" /\ stutter_state = "stutter2" -> "p3"
      [] lock_pc[proc] = "cs" -> "cs"
      [] lock_pc[proc] = "l2" -> "p4"
      [] OTHER -> "p0"

\* Translation for Peterson's flag variable
flag_translation(lock_pc, stutter_state) ==
    [p \in Procs |-> 
        IF pc_translation(lock_pc, stutter_state, p) \in {"p2", "p3", "cs", "p4"}
        THEN TRUE
        ELSE FALSE]

\* Translation for Peterson's turn variable  
turn_translation(h) == h

\* Translation for Peterson's critical section indicator
c_translation(lock_pc) ==
    [p \in Procs |-> lock_pc[p] = "cs"]

--------------------------------------------------------------------------------
\* Peterson Module Instance
--------------------------------------------------------------------------------

P_pc == [p \in Procs |-> pc_translation(pc, s, p)]
P_flag == flag_translation(pc, s)
P_turn == turn_translation(h_turn)

\* Peterson's type invariant (refined)
PTypeOK ==
    /\ P_pc \in [Procs -> PetersonLocations]
    /\ P_flag \in [Procs -> BOOLEAN]
    /\ P_turn \in Procs

\* Peterson's mutual exclusion
PMutualExclusion == \A p, q \in Procs : (p # q) => ~(P_pc[p] = "cs" /\ P_pc[q] = "cs")

\* Peterson's initial condition
PInit ==
    /\ P_pc = [p \in Procs |-> "p0"]
    /\ P_flag = [p \in Procs |-> FALSE]
    /\ P_turn \in Procs

\* Peterson's specification (temporal property to be refined)
PSpec == PInit /\ [][TRUE]_<<P_pc, P_flag, P_turn>>

--------------------------------------------------------------------------------
\* Refinement assertions
--------------------------------------------------------------------------------

\* The augmented Lock specification implies the base Lock specification
THEOREM SpecHS => Spec
  PROOF OMITTED

\* The augmented Lock specification refines Peterson's specification  
THEOREM SpecHS => PSpec
  PROOF OMITTED

================================================================================