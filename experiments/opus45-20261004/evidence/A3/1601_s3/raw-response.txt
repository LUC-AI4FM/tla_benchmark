---------------------------- MODULE Fischer ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS N, Delta, Epsilon, Infinity

ASSUME N \in Nat /\ N > 0
ASSUME Delta \in Nat /\ Delta > 0
ASSUME Epsilon \in Nat /\ Epsilon > 0
ASSUME Infinity > Delta /\ Infinity > Epsilon

Procs == 1..N

(*--algorithm Fischer
variables
    turn = 0,
    timer = [p \in Procs |-> Infinity],
    pc_state = [p \in Procs |-> "idle"];
    
define
    \* Mutual exclusion invariant - at most one process in critical section
    MutualExclusion == \A p1, p2 \in Procs : 
        (pc_state[p1] = "cs" /\ pc_state[p2] = "cs") => p1 = p2
    
    \* Count processes in each state (for TLC state exploration)
    IdleCount == Cardinality({p \in Procs : pc_state[p] = "idle"})
    WaitingCount == Cardinality({p \in Procs : pc_state[p] = "waiting"})
    CheckCount == Cardinality({p \in Procs : pc_state[p] = "check"})
    CSCount == Cardinality({p \in Procs : pc_state[p] = "cs"})
    
    \* Liveness: some process is infinitely often in the critical section
    SomeoneInCS == \E p \in Procs : pc_state[p] = "cs"
end define;

\* The ticking process decrements all per-process timers
fair process Tick = 0
begin
TickLoop:
    while TRUE do
        timer := [p \in Procs |-> IF timer[p] > 0 /\ timer[p] < Infinity 
                                  THEN timer[p] - 1 
                                  ELSE timer[p]];
    end while;
end process;

\* Each process p runs Fischer's algorithm
fair process Proc \in Procs
begin
Idle:
    while TRUE do
        \* Wait until turn is 0 (no one claiming)
        await turn = 0;
        \* Set timer to Delta (write delay)
        timer[self] := Delta;
        pc_state[self] := "waiting";
        
    Writing:
        \* Wait for timer to expire before writing
        await timer[self] = 0;
        \* Write our ID to turn
        turn := self;
        \* Set timer to Epsilon (read delay)
        timer[self] := Epsilon;
        pc_state[self] := "check";
        
    Checking:
        \* Wait for timer to expire before checking
        await timer[self] = 0;
        \* Check if turn is still our ID
        if turn = self then
            pc_state[self] := "cs";
            
        CriticalSection:
            \* In critical section
            skip;
            \* Exit critical section
            turn := 0;
            timer[self] := Infinity;
            pc_state[self] := "idle";
        else
            \* Someone else wrote, go back to idle
            timer[self] := Infinity;
            pc_state[self] := "idle";
        end if;
    end while;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES turn, timer, pc_state, pc

vars == << turn, timer, pc_state, pc >>

ProcSet == {0} \cup (Procs)

Init == 
    /\ turn = 0
    /\ timer = [p \in Procs |-> Infinity]
    /\ pc_state = [p \in Procs |-> "idle"]
    /\ pc = [self \in ProcSet |-> CASE self = 0 -> "TickLoop"
                                    [] self \in Procs -> "Idle"]

\* Mutual exclusion invariant
MutualExclusion == \A p1, p2 \in Procs : 
    (pc_state[p1] = "cs" /\ pc_state[p2] = "cs") => p1 = p2

\* Count processes in each state
RECURSIVE Cardinality(_)
Cardinality(S) == IF S = {} THEN 0 ELSE 1 + Cardinality(S \ {CHOOSE x \in S : TRUE})

IdleCount == Cardinality({p \in Procs : pc_state[p] = "idle"})
WaitingCount == Cardinality({p \in Procs : pc_state[p] = "waiting"})
CheckCount == Cardinality({p \in Procs : pc_state[p] = "check"})
CSCount == Cardinality({p \in Procs : pc_state[p] = "cs"})

\* Liveness property
SomeoneInCS == \E p \in Procs : pc_state[p] = "cs"

\* Tick process action
TickLoop == 
    /\ pc[0] = "TickLoop"
    /\ timer' = [p \in Procs |-> IF timer[p] > 0 /\ timer[p] < Infinity 
                                 THEN timer[p] - 1 
                                 ELSE timer[p]]
    /\ pc' = [pc EXCEPT ![0] = "TickLoop"]
    /\ UNCHANGED << turn, pc_state >>

\* Process Proc actions
Idle(self) == 
    /\ pc[self] = "Idle"
    /\ turn = 0
    /\ timer' = [timer EXCEPT ![self] = Delta]
    /\ pc_state' = [pc_state EXCEPT ![self] = "waiting"]
    /\ pc' = [pc EXCEPT ![self] = "Writing"]
    /\ UNCHANGED turn

Writing(self) == 
    /\ pc[self] = "Writing"
    /\ timer[self] = 0
    /\ turn' = self
    /\ timer' = [timer EXCEPT ![self] = Epsilon]
    /\ pc_state' = [pc_state EXCEPT ![self] = "check"]
    /\ pc' = [pc EXCEPT ![self] = "Checking"]

Checking(self) == 
    /\ pc[self] = "Checking"
    /\ timer[self] = 0
    /\ IF turn = self
       THEN /\ pc_state' = [pc_state EXCEPT ![self] = "cs"]
            /\ pc' = [pc EXCEPT ![self] = "CriticalSection"]
       ELSE /\ timer' = [timer EXCEPT ![self] = Infinity]
            /\ pc_state' = [pc_state EXCEPT ![self] = "idle"]
            /\ pc' = [pc EXCEPT ![self] = "Idle"]
    /\ IF turn = self
       THEN UNCHANGED timer
       ELSE TRUE
    /\ UNCHANGED turn

CriticalSection(self) == 
    /\ pc[self] = "CriticalSection"
    /\ turn' = 0
    /\ timer' = [timer EXCEPT ![self] = Infinity]
    /\ pc_state' = [pc_state EXCEPT ![self] = "idle"]
    /\ pc' = [pc EXCEPT ![self] = "Idle"]

Proc(self) == Idle(self) \/ Writing(self) \/ Checking(self) \/ CriticalSection(self)

Tick == TickLoop

Next == Tick \/ (\E self \in Procs: Proc(self))

\* Fairness conditions
Fairness == /\ WF_vars(Tick)
            /\ \A self \in Procs : WF_vars(Proc(self))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Liveness property: infinitely often some process is in the critical section
Liveness == []<>SomeoneInCS

\* Type invariant for state checking
TypeOK == 
    /\ turn \in 0..N
    /\ timer \in [Procs -> 0..Infinity]
    /\ pc_state \in [Procs -> {"idle", "waiting", "check", "cs"}]
    /\ pc \in [ProcSet -> {"TickLoop", "Idle", "Writing", "Checking", "CriticalSection"}]

\* NOTE: A bug (mutual exclusion violation) should be found when N > 1 and Delta >= Epsilon
\* This highlights the timing-sensitive design of Fischer's algorithm:
\* The algorithm requires Delta < Epsilon for correctness

=============================================================================