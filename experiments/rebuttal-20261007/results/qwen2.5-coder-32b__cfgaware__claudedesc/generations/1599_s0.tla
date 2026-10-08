------------------------------- MODULE FastMutualExclusion -------------------------------
VARIABLES x, y, b

CONSTANTS N

ASSUME N \in Nat /\ N > 0

(*--algorithm fast_mutex
variables x = 0, y = 0, b = [i \in 1..N -> FALSE];

process p \in 1..N
begin
    while TRUE do
        j:
        b[self] := TRUE;
        x := self;
        if y = 0 then
            l4: await y = 0;
            y := self;
            l8: await x = self;
            (* Critical Section *)
            y := 0;
            b[self] := FALSE;
        else
            b[self] := FALSE;
            l10: while (\E i \in 1..N : b[i]) do
                skip;
            if y = self then
                (* Critical Section *)
                y := 0;
                b[self] := FALSE;
end if;
    end while;
end process
end algorithm*)

\* Definitions of the TLA+ specification

Spec == /\ \E x, y, b \in SUBSET (1..N) : Init(x, y, b)
        /\ [][Next]_<<x, y, b>>

Init(x, y, b) == /\ x = 0
                 /\ y = 0
                 /\ b = [i \in 1..N -> FALSE]

Next == \/ \E self \in 1..N : FastPath(self)
        \/ \E self \in 1..N : SlowPath(self)

FastPath(self) ==
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ x' = self
    /\ y = 0
    /\ l4: y = 0
    /\ y' = self
    /\ l8: x = self
    /\ \* Critical Section
    /\ y'' = 0
    /\ b'' = [b' EXCEPT ![self] = FALSE]

SlowPath(self) ==
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ x' = self
    /\ y # 0
    /\ b'' = [b' EXCEPT ![self] = FALSE]
    /\ l10: \A i \in 1..N : ~b'[i]
    /\ IF y = self THEN
           /\ \* Critical Section
           /\ y' = 0
           /\ b' = [b'' EXCEPT ![self] = FALSE]
       ELSE
           UNCHANGED <<y, b>>
       ENDIF

Invariant == \/ y = 0
             \/ (\A i, j \in 1..N : i # j => ~b[i] \/ ~b[j])

CondLiveness ==
    [](\/ \E self \in 1..N : <>[]~(b[self]))
    -> <>(\E self \in 1..N : <>(y = self))

FairSpec == Spec /\ WF_next

WF_next == WF_<<x, y, b>>[Next]

=============================================================================