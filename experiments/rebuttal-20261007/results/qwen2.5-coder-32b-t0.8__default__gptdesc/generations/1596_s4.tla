------------------------------- MODULE FastMutex -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS M, N \* M < N

VARIABLES x, y, b, cs

Init == /\ x = 0 
        /\ y = 0 
        /\ b = <<FALSE>> 
        /\ cs = {}

Next == \/ \/ /\ PC \in 1..M
                /\ \/ /\ x /= PC 
                       /\ y = 0 
                       /\ b[PC] = FALSE
                       /\ UNCHANGED <<y, b, cs>>
                           -> /\ x' = PC 
                              /\ b'[PC] = TRUE
                              /\ UNCHANGED <<x, cs>>
                   \/ /\ x = PC 
                       /\ (b[PC] = TRUE \/ (\E q \in 1..M : q # PC /\ y = q))
                       /\ UNCHANGED <<y, b, cs>>
                           -> /\ y' = PC 
                              /\ b'[PC] = FALSE
                              /\ UNCHANGED <<x, cs>>
                   \/ /\ x /= PC 
                       /\ y = PC 
                       /\ (\A q \in 1..M : q # PC => b[q] = FALSE)
                       /\ UNCHANGED <<b, cs>>
                           -> /\ cs' = cs \cup {PC}
                              /\ UNCHANGED <<x, y>>
                   \/ /\ x /= PC
                       /\ y /= PC 
                       /\ PC \notin cs
                       /\ (\A q \in 1..M : b[q] = FALSE)
                           -> /\ cs' = {}
                              /\ UNCHANGED <<x, y, b>>
        \/ /\ PC \in (M+1)..N
                /\ \/ /\ x /= PC 
                       /\ y = 0 
                       /\ b[PC] = FALSE
                       /\ UNCHANGED <<y, b, cs>>
                           -> /\ x' = PC 
                              /\ b'[PC] = TRUE
                              /\ UNCHANGED <<x, cs>>
                   \/ /\ x = PC 
                       /\ (b[PC] = TRUE \/ (\E q \in (M+1)..N : q # PC /\ y = q))
                       /\ UNCHANGED <<y, b, cs>>
                           -> /\ y' = PC 
                              /\ b'[PC] = FALSE
                              /\ UNCHANGED <<x, cs>>
                   \/ /\ x /= PC 
                       /\ y = PC 
                       /\ (\A q \in (M+1)..N : q # PC => b[q] = FALSE)
                       /\ UNCHANGED <<b, cs>>
                           -> /\ cs' = cs \cup {PC}
                              /\ UNCHANGED <<x, y>>
                   \/ /\ x /= PC
                       /\ y /= PC 
                       /\ PC \notin cs
                       /\ (\A q \in (M+1)..N : b[q] = FALSE)
                           -> /\ cs' = {}
                              /\ UNCHANGED <<x, y, b>>

Spec == /\ Init
        /\ [][Next]_<<x,y,b,cs>>
        /\ WF_(PC \in 1..M) <<Next>>
        /\ SF_(PC \in (M+1)..N) <<Next>>
        /\ <>[](\/ PC \in 1..N : cs' = cs \cup {PC})

MutualExclusion == \/ #cs <= 1

TypeOK == /\ x \in 0..N
          /\ y \in 0..N
          /\ b \in [1..N -> BOOLEAN]
          /\ cs \subseteq (1..N)

Spec == Spec /\ []TypeOK /\ []MutualExclusion
=============================================================================