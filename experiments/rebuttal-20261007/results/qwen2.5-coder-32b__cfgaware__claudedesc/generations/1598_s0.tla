------------------------------- MODULE FastMutualExclusion -------------------------------
CONSTANTS N

VARIABLES x, y, b, S

(*--algorithm fast_mutex
variables x = 0, y = 0, b \in [1..N -> BOOLEAN], S \in [1..N -> SUBSET (1..N)];

process process \in 1..N
begin
    while TRUE do
        with self = process;
            b[self] := TRUE;
            x := self;
            if y # 0 then
                b[self] := FALSE;
                await y = 0;
            else
                y := self;
                if x # self then
                    b[self] := FALSE;
                    S[self] := (1..N) \ {self};
                    while S[self] # {} do
                        with other \in CHOOSE p \in S[self]: b[p];
                            if ~b[other] then
                                S[self] := S[self] \ {other};
                            else
                                await FALSE;
                        endwith;
                    endwhile;
                    if y # self then
                        await y = 0;
                    endif;
                endif;
            endif;
            cs; (* critical section *)
            y := 0;
            b[self] := FALSE;
    endwhile;
end process;

end algorithm *)

Spec ==
    /\ Init
    /\ [][Next]_<<x, y, b>>
    /\ WF_pc

Init ==
    /\ x = 0
    /\ y = 0
    /\ b \in [1..N -> BOOLEAN]
    /\ (\A p \in 1..N: b[p] = FALSE)
    /\ S \in [1..N -> SUBSET (1..N)]
    /\ (\A p \in 1..N: S[p] = {})

Next ==
    \/ \E self \in 1..N : pc[self] = "raise_flag" /\ RaiseFlag(self)
    \/ \E self \in 1..N : pc[self] = "check_y" /\ CheckY(self)
    \/ \E self \in 1..N : pc[self] = "lower_flag_wait_y" /\ LowerFlagWaitY(self)
    \/ \E self \in 1..N : pc[self] = "write_y" /\ WriteY(self)
    \/ \E self \in 1..N : pc[self] = "check_x" /\ CheckX(self)
    \/ \E self \in 1..N : pc[self] = "clear_flags_wait_others" /\ ClearFlagsWaitOthers(self)
    \/ \E self \in 1..N : pc[self] = "check_y_again" /\ CheckYAgain(self)
    \/ \E self \in 1..N : pc[self] = "critical_section" /\ CriticalSection(self)

RaiseFlag(self) ==
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ x' = self
    /\ pc'[self] = "check_y"

CheckY(self) ==
    /\ IF y # 0 THEN
           /\ b' = [b EXCEPT ![self] = FALSE]
           /\ pc'[self] = "lower_flag_wait_y"
       ELSE
           /\ pc'[self] = "write_y"
       ENDIF

LowerFlagWaitY(self) ==
    /\ y = 0 => pc'[self] = "raise_flag"

WriteY(self) ==
    /\ y' = self
    /\ pc'[self] = "check_x"

CheckX(self) ==
    /\ IF x # self THEN
           /\ b' = [b EXCEPT ![self] = FALSE]
           /\ S' = [S EXCEPT ![self] = (1..N) \ {self}]
           /\ pc'[self] = "clear_flags_wait_others"
       ELSE
           /\ pc'[self] = "critical_section"
       ENDIF

ClearFlagsWaitOthers(self) ==
    /\ IF S[self] # {} THEN
           /\ \E other \in CHOOSE p \in S[self]: b[p] :
                /\ IF ~b[other] THEN
                       /\ S' = [S EXCEPT ![self] = S[self] \ {other}]
                   ELSE
                       /\ pc'[self] = "clear_flags_wait_others"
                   ENDIF
       ELSE
           /\ pc'[self] = "check_y_again"
       ENDIF

CheckYAgain(self) ==
    /\ IF y # self THEN
           /\ y = 0 => pc'[self] = "raise_flag"
       ELSE
           /\ pc'[self] = "critical_section"
       ENDIF

CriticalSection(self) ==
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc'[self] = "raise_flag"

WF_pc == 
    WF_<<pc>>

Invariant ==
    \A p, q \in 1..N : p # q => ~(\E i \in 1..2: pc[p] = "critical_section" /\ pc[q] = "critical_section")

Liveness ==
    <>[] (\E p \in 1..N: pc[p] = "critical_section")
=============================================================================