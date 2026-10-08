---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, M

ASSUME /\ N \in Nat \ {0}
       /\ M \in Nat \ {0}
       /\ M < N

Procs == 1..N
Group1 == 1..M
Group2 == (M+1)..N

(*
--algorithm FastMutex
variables
    x = 0,
    y = 0,
    b = [i \in Procs |-> FALSE];

define
    MutualExclusion == \A i, j \in Procs : 
        (pc[i] = "cs" /\ pc[j] = "cs") => (i = j)
    
    SomeoneInCS == \E i \in Procs : pc[i] = "cs"
end define;

macro await(cond)
begin
    await cond;
end macro;

fair process proc1 \in Group1
begin
start1:
    while TRUE do
        ncs1:
            skip;
        
        enter1_1:
            b[self] := TRUE;
        
        enter1_2:
            x := self;
        
        enter1_3:
            if y /= 0 then
                enter1_3a:
                    b[self] := FALSE;
                enter1_3b:
                    await y = 0;
                    goto enter1_1;
            end if;
        
        enter1_4:
            y := self;
        
        enter1_5:
            if x /= self then
                enter1_5a:
                    b[self] := FALSE;
                enter1_5b:
                    await \A j \in Procs : ~b[j];
                enter1_5c:
                    if y /= self then
                        enter1_5d:
                            await y = 0;
                            goto enter1_1;
                    end if;
            end if;
        
        cs:
            skip;
        
        exit1:
            y := 0;
            b[self] := FALSE;
    end while;
end process;

fair process proc2 \in Group2
begin
start2:
    while TRUE do
        ncs2:
            skip;
        
        enter2_1:
            b[self] := TRUE;
        
        enter2_2:
            x := self;
        
        enter2_3:
            if y /= 0 then
                enter2_3a:
                    b[self] := FALSE;
                enter2_3b:
                    await y = 0;
                    goto enter2_1;
            end if;
        
        enter2_4:
            y := self;
        
        enter2_5:
            if x /= self then
                enter2_5a:
                    b[self] := FALSE;
                enter2_5b:
                    await \A j \in Procs : ~b[j];
                enter2_5c:
                    if y /= self then
                        enter2_5d:
                            await y = 0;
                            goto enter2_1;
                    end if;
            end if;
        
        cs2:
            skip;
        
        exit2:
            y := 0;
            b[self] := FALSE;
    end while;
end process;

end algorithm;
*)

\* BEGIN TRANSLATION
VARIABLES x, y, b, pc

(* define statement *)
MutualExclusion == \A i, j \in Procs :
    (pc[i] = "cs" /\ pc[j] = "cs") => (i = j)

SomeoneInCS == \E i \in Procs : pc[i] = "cs"


vars == << x, y, b, pc >>

ProcSet == (Group1) \cup (Group2)

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ b = [i \in Procs |-> FALSE]
        /\ pc = [self \in ProcSet |-> CASE self \in Group1 -> "start1"
                                        [] self \in Group2 -> "start2"]

start1(self) == /\ pc[self] = "start1"
                /\ pc' = [pc EXCEPT ![self] = "ncs1"]
                /\ UNCHANGED << x, y, b >>

ncs1(self) == /\ pc[self] = "ncs1"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "enter1_1"]
              /\ UNCHANGED << x, y, b >>

enter1_1(self) == /\ pc[self] = "enter1_1"
                  /\ b' = [b EXCEPT ![self] = TRUE]
                  /\ pc' = [pc EXCEPT ![self] = "enter1_2"]
                  /\ UNCHANGED << x, y >>

enter1_2(self) == /\ pc[self] = "enter1_2"
                  /\ x' = self
                  /\ pc' = [pc EXCEPT ![self] = "enter1_3"]
                  /\ UNCHANGED << y, b >>

enter1_3(self) == /\ pc[self] = "enter1_3"
                  /\ IF y /= 0
                        THEN /\ pc' = [pc EXCEPT ![self] = "enter1_3a"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "enter1_4"]
                  /\ UNCHANGED << x, y, b >>

enter1_3a(self) == /\ pc[self] = "enter1_3a"
                   /\ b' = [b EXCEPT ![self] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = "enter1_3b"]
                   /\ UNCHANGED << x, y >>

enter1_3b(self) == /\ pc[self] = "enter1_3b"
                   /\ y = 0
                   /\ pc' = [pc EXCEPT ![self] = "enter1_1"]
                   /\ UNCHANGED << x, y, b >>

enter1_4(self) == /\ pc[self] = "enter1_4"
                  /\ y' = self
                  /\ pc' = [pc EXCEPT ![self] = "enter1_5"]
                  /\ UNCHANGED << x, b >>

enter1_5(self) == /\ pc[self] = "enter1_5"
                  /\ IF x /= self
                        THEN /\ pc' = [pc EXCEPT ![self] = "enter1_5a"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                  /\ UNCHANGED << x, y, b >>

enter1_5a(self) == /\ pc[self] = "enter1_5a"
                   /\ b' = [b EXCEPT ![self] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = "enter1_5b"]
                   /\ UNCHANGED << x, y >>

enter1_5b(self) == /\ pc[self] = "enter1_5b"
                   /\ \A j \in Procs : ~b[j]
                   /\ pc' = [pc EXCEPT ![self] = "enter1_5c"]
                   /\ UNCHANGED << x, y, b >>

enter1_5c(self) == /\ pc[self] = "enter1_5c"
                   /\ IF y /= self
                         THEN /\ pc' = [pc EXCEPT ![self] = "enter1_5d"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                   /\ UNCHANGED << x, y, b >>

enter1_5d(self) == /\ pc[self] = "enter1_5d"
                   /\ y = 0
                   /\ pc' = [pc EXCEPT ![self] = "enter1_1"]
                   /\ UNCHANGED << x, y, b >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit1"]
            /\ UNCHANGED << x, y, b >>

exit1(self) == /\ pc[self] = "exit1"
               /\ y' = 0
               /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "start1"]
               /\ UNCHANGED x

proc1(self) == start1(self) \/ ncs1(self) \/ enter1_1(self) \/ enter1_2(self)
                  \/ enter1_3(self) \/ enter1_3a(self) \/ enter1_3b(self)
                  \/ enter1_4(self) \/ enter1_5(self) \/ enter1_5a(self)
                  \/ enter1_5b(self) \/ enter1_5c(self) \/ enter1_5d(self)
                  \/ cs(self) \/ exit1(self)

start2(self) == /\ pc[self] = "start2"
                /\ pc' = [pc EXCEPT ![self] = "ncs2"]
                /\ UNCHANGED << x, y, b >>

ncs2(self) == /\ pc[self] = "ncs2"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "enter2_1"]
              /\ UNCHANGED << x, y, b >>

enter2_1(self) == /\ pc[self] = "enter2_1"
                  /\ b' = [b EXCEPT ![self] = TRUE]
                  /\ pc' = [pc EXCEPT ![self] = "enter2_2"]
                  /\ UNCHANGED << x, y >>

enter2_2(self) == /\ pc[self] = "enter2_2"
                  /\ x' = self
                  /\ pc' = [pc EXCEPT ![self] = "enter2_3"]
                  /\ UNCHANGED << y, b >>

enter2_3(self) == /\ pc[self] = "enter2_3"
                  /\ IF y /= 0
                        THEN /\ pc' = [pc EXCEPT ![self] = "enter2_3a"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "enter2_4"]
                  /\ UNCHANGED << x, y, b >>

enter2_3a(self) == /\ pc[self] = "enter2_3a"
                   /\ b' = [b EXCEPT ![self] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = "enter2_3b"]
                   /\ UNCHANGED << x, y >>

enter2_3b(self) == /\ pc[self] = "enter2_3b"
                   /\ y = 0
                   /\ pc' = [pc EXCEPT ![self] = "enter2_1"]
                   /\ UNCHANGED << x, y, b >>

enter2_4(self) == /\ pc[self] = "enter2_4"
                  /\ y' = self
                  /\ pc' = [pc EXCEPT ![self] = "enter2_5"]
                  /\ UNCHANGED << x, b >>

enter2_5(self) == /\ pc[self] = "enter2_5"
                  /\ IF x /= self
                        THEN /\ pc' = [pc EXCEPT ![self] = "enter2_5a"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "cs2"]
                  /\ UNCHANGED << x, y, b >>

enter2_5a(self) == /\ pc[self] = "enter2_5a"
                   /\ b' = [b EXCEPT ![self] = FALSE]
                   /\ pc' = [pc EXCEPT ![self] = "enter2_5b"]
                   /\ UNCHANGED << x, y >>

enter2_5b(self) == /\ pc[self] = "enter2_5b"
                   /\ \A j \in Procs : ~b[j]
                   /\ pc' = [pc EXCEPT ![self] = "enter2_5c"]
                   /\ UNCHANGED << x, y, b >>

enter2_5c(self) == /\ pc[self] = "enter2_5c"
                   /\ IF y /= self
                         THEN /\ pc' = [pc EXCEPT ![self] = "enter2_5d"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "cs2"]
                   /\ UNCHANGED << x, y, b >>

enter2_5d(self) == /\ pc[self] = "enter2_5d"
                   /\ y = 0
                   /\ pc' = [pc EXCEPT ![self] = "enter2_1"]
                   /\ UNCHANGED << x, y, b >>

cs2(self) == /\ pc[self] = "cs2"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "exit2"]
             /\ UNCHANGED << x, y, b >>

exit2(self) == /\ pc[self] = "exit2"
               /\ y' = 0
               /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "start2"]
               /\ UNCHANGED x

proc2(self) == start2(self) \/ ncs2(self) \/ enter2_1(self) \/ enter2_2(self)
                  \/ enter2_3(self) \/ enter2_3a(self) \/ enter2_3b(self)
                  \/ enter2_4(self) \/ enter2_5(self) \/ enter2_5a(self)
                  \/ enter2_5b(self) \/ enter2_5c(self) \/ enter2_5d(self)
                  \/ cs2(self) \/ exit2(self)

Next == (\E self \in Group1: proc1(self))
           \/ (\E self \in Group2: proc2(self))

Spec == Init /\ [][Next]_vars /\ \A self \in Group1 : WF_vars(proc1(self))
                              /\ \A self \in Group2 : WF_vars(proc2(self))

\* END TRANSLATION

-----------------------------------------------------------------------------

InCS(i) == pc[i] \in {"cs", "cs2"}

TypeOK == /\ x \in Procs \cup {0}
          /\ y \in Procs \cup {0}
          /\ b \in [Procs -> BOOLEAN]
          /\ pc \in [Procs -> STRING]

MutexInvariant == \A i, j \in Procs : (InCS(i) /\ InCS(j)) => (i = j)

Liveness == []<>(\E i \in Procs : InCS(i))

==========================================================================