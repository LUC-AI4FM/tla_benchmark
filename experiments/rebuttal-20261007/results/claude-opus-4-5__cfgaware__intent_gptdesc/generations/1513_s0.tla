---------------------------- MODULE TokenRingTermination ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS White, Black, Active, Passive

VARIABLES 
    tokenAt,        \* Which process holds the token (0, 1, or 2)
    tokenColor,     \* Color of the token (White or Black)
    procActive,     \* Array: procActive[i] = Active or Passive for process i
    procColor,      \* Array: procColor[i] = White or Black for process i
    terminated      \* Boolean: has termination been declared?

vars == <<tokenAt, procActive, procColor, tokenColor, terminated>>

Procs == {0, 1, 2}
Colors == {White, Black}
ActivityStates == {Active, Passive}

\* Next process in the ring (clockwise)
Next(p) == (p + 1) % 3

\* Previous process in the ring (counter-clockwise, for message sending)
Prev(p) == (p + 2) % 3

TypeInvariant ==
    /\ tokenAt \in Procs
    /\ tokenColor \in Colors
    /\ procActive \in [Procs -> ActivityStates]
    /\ procColor \in [Procs -> Colors]
    /\ terminated \in BOOLEAN

\* Initial state: all processes active and white, token at process 0, white token
Init ==
    /\ tokenAt = 0
    /\ tokenColor = White
    /\ procActive = [p \in Procs |-> Active]
    /\ procColor = [p \in Procs |-> White]
    /\ terminated = FALSE

\* A process becomes passive (finishes its local work)
BecomePassive(p) ==
    /\ procActive[p] = Active
    /\ ~terminated
    /\ procActive' = [procActive EXCEPT ![p] = Passive]
    /\ UNCHANGED <<tokenAt, tokenColor, procColor, terminated>>

\* A passive process becomes active due to receiving work from another process
\* When process q sends work to process p (where q > p in ring order), q becomes black
ReceiveWork(p) ==
    /\ procActive[p] = Passive
    /\ ~terminated
    /\ \E q \in Procs : 
        /\ q # p
        /\ procActive[q] = Active
        \* Sender q becomes black if it sends to a "lower" process (backwards in ring)
        /\ procColor' = [procColor EXCEPT ![q] = IF Prev(q) = p \/ (q > p) THEN Black ELSE procColor[q]]
    /\ procActive' = [procActive EXCEPT ![p] = Active]
    /\ UNCHANGED <<tokenAt, tokenColor, terminated>>

\* Process p does some local work (stays active, may change color)
DoWork(p) ==
    /\ procActive[p] = Active
    /\ ~terminated
    /\ UNCHANGED vars

\* Pass the token to the next process
\* When passing, if process is black, token becomes black
\* Process 0 initiates a new round by making token white if it was white and it is white
PassToken(p) ==
    /\ tokenAt = p
    /\ procActive[p] = Passive  \* Only passive processes pass the token
    /\ ~terminated
    /\ tokenAt' = Next(p)
    \* Token color: black if current process is black or token was already black
    /\ tokenColor' = IF procColor[p] = Black THEN Black ELSE tokenColor
    \* After passing, process becomes white
    /\ procColor' = [procColor EXCEPT ![p] = White]
    /\ UNCHANGED <<procActive, terminated>>

\* Process 0 initiates a new detection round
\* This happens when token returns to 0 and conditions aren't met for termination
InitiateRound ==
    /\ tokenAt = 0
    /\ procActive[0] = Passive
    /\ ~terminated
    /\ ~(tokenColor = White /\ procColor[0] = White)  \* Can't declare termination
    /\ tokenAt' = Next(0)
    /\ tokenColor' = White  \* Start fresh round with white token
    /\ procColor' = [procColor EXCEPT ![0] = White]
    /\ UNCHANGED <<procActive, terminated>>

\* Termination detection: process 0 declares termination
\* when it's passive, white, and receives a white token
DeclareTermination ==
    /\ tokenAt = 0
    /\ procActive[0] = Passive
    /\ procColor[0] = White
    /\ tokenColor = White
    /\ ~terminated
    /\ terminated' = TRUE
    /\ UNCHANGED <<tokenAt, tokenColor, procActive, procColor>>

\* Combined token passing action
TokenAction(p) ==
    \/ PassToken(p)
    \/ (p = 0 /\ InitiateRound)

Next ==
    \/ \E p \in Procs : BecomePassive(p)
    \/ \E p \in Procs : ReceiveWork(p)
    \/ \E p \in Procs : TokenAction(p)
    \/ DeclareTermination

\* Fairness: eventual token passing and fair scheduling
Fairness ==
    /\ \A p \in Procs : WF_vars(TokenAction(p))
    /\ WF_vars(DeclareTermination)
    /\ \A p \in Procs : WF_vars(BecomePassive(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* ============================================================================