---------------------------- MODULE specification ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS defaultInitValue, Val

CONSTANTS Procs

Null == CHOOSE n : n \notin Val

Addr == 1..10

(*--algorithm DoubleEndedQueue
variables
    mem = [a \in Addr |-> [val |-> defaultInitValue, left |-> Null, right |-> Null]],
    LeftHat = Null,
    RightHat = Null,
    freelist = Addr,
    valBag = [v \in Val |-> 0];

define
    TypeOK ==
        /\ LeftHat \in Addr \cup {Null}
        /\ RightHat \in Addr \cup {Null}
        /\ freelist \subseteq Addr
        /\ \A v \in Val : valBag[v] >= 0
end define;

macro Alloc(result) begin
    if freelist /= {} then
        with a \in freelist do
            result := a;
            freelist := freelist \ {a};
        end with;
    else
        result := Null;
    end if;
end macro;

macro Free(addr) begin
    if addr /= Null then
        freelist := freelist \cup {addr};
    end if;
end macro;

procedure pushLeft(valL = defaultInitValue)
variables nodeL = Null, lhL = Null, rhL = Null;
begin
PL1:
    Alloc(nodeL);
PL2:
    if nodeL = Null then
        return;
    end if;
PL3:
    mem[nodeL].val := valL;
    mem[nodeL].left := Null;
PL4:
    lhL := LeftHat;
    rhL := RightHat;
PL5:
    if lhL = Null then
        mem[nodeL].right := Null;
PL6:
        if LeftHat = Null /\ RightHat = Null then
            LeftHat := nodeL;
            RightHat := nodeL;
            valBag[valL] := valBag[valL] + 1;
            return;
        else
            goto PL4;
        end if;
    else
PL7:
        mem[nodeL].right := lhL;
PL8:
        if LeftHat = lhL /\ mem[lhL].left = Null then
            LeftHat := nodeL;
            mem[lhL].left := nodeL;
            valBag[valL] := valBag[valL] + 1;
            return;
        else
            goto PL4;
        end if;
    end if;
end procedure;

procedure pushRight(valR = defaultInitValue)
variables nodeR = Null, lhR = Null, rhR = Null;
begin
PR1:
    Alloc(nodeR);
PR2:
    if nodeR = Null then
        return;
    end if;
PR3:
    mem[nodeR].val := valR;
    mem[nodeR].right := Null;
PR4:
    lhR := LeftHat;
    rhR := RightHat;
PR5:
    if rhR = Null then
        mem[nodeR].left := Null;
PR6:
        if LeftHat = Null /\ RightHat = Null then
            LeftHat := nodeR;
            RightHat := nodeR;
            valBag[valR] := valBag[valR] + 1;
            return;
        else
            goto PR4;
        end if;
    else
PR7:
        mem[nodeR].left := rhR;
PR8:
        if RightHat = rhR /\ mem[rhR].right = Null then
            RightHat := nodeR;
            mem[rhR].right := nodeR;
            valBag[valR] := valBag[valR] + 1;
            return;
        else
            goto PR4;
        end if;
    end if;
end procedure;

procedure popLeft()
variables lhPL = Null, rhPL = Null, resultPL = defaultInitValue, nxtPL = Null;
begin
OL1:
    lhPL := LeftHat;
    rhPL := RightHat;
OL2:
    if lhPL = Null then
        return;
    end if;
OL3:
    if lhPL = rhPL then
OL4:
        if LeftHat = lhPL /\ RightHat = rhPL then
            resultPL := mem[lhPL].val;
            LeftHat := Null;
            RightHat := Null;
            valBag[resultPL] := valBag[resultPL] - 1;
            Free(lhPL);
            return;
        else
            goto OL1;
        end if;
    else
OL5:
        nxtPL := mem[lhPL].right;
OL6:
        if nxtPL = Null then
            goto OL1;
        end if;
OL7:
        if LeftHat = lhPL /\ mem[nxtPL].left = lhPL then
            resultPL := mem[lhPL].val;
            LeftHat := nxtPL;
            mem[nxtPL].left := Null;
            valBag[resultPL] := valBag[resultPL] - 1;
            Free(lhPL);
            return;
        else
            goto OL1;
        end if;
    end if;
end procedure;

procedure popRight()
variables lhPR = Null, rhPR = Null, resultPR = defaultInitValue, nxtPR = Null;
begin
OR1:
    lhPR := LeftHat;
    rhPR := RightHat;
OR2:
    if rhPR = Null then
        return;
    end if;
OR3:
    if lhPR = rhPR then
OR4:
        if LeftHat = lhPR /\ RightHat = rhPR then
            resultPR := mem[rhPR].val;
            LeftHat := Null;
            RightHat := Null;
            valBag[resultPR] := valBag[resultPR] - 1;
            Free(rhPR);
            return;
        else
            goto OR1;
        end if;
    else
OR5:
        nxtPR := mem[rhPR].left;
OR6:
        if nxtPR = Null then
            goto OR1;
        end if;
OR7:
        if RightHat = rhPR /\ mem[nxtPR].right = rhPR then
            resultPR := mem[rhPR].val;
            RightHat := nxtPR;
            mem[nxtPR].right := Null;
            valBag[resultPR] := valBag[resultPR] - 1;
            Free(rhPR);
            return;
        else
            goto OR1;
        end if;
    end if;
end procedure;

fair process test \in Procs
variables myVal = defaultInitValue;
begin
T1:
    while TRUE do
        either
            with v \in Val do
                myVal := v;
            end with;
T2:
            call pushLeft(myVal);
        or
            with v \in Val do
                myVal := v;
            end with;
T3:
            call pushRight(myVal);
        or
T4:
            call popLeft();
        or
T5:
            call popRight();
        end either;
    end while;
end process;

end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "b6df6ba4" /\ chksum(tla) = "e23b00e4")
VARIABLES mem, LeftHat, RightHat, freelist, valBag, pc, stack

(* define statement *)
TypeOK ==
    /\ LeftHat \in Addr \cup {Null}
    /\ RightHat \in Addr \cup {Null}
    /\ freelist \subseteq Addr
    /\ \A v \in Val : valBag[v] >= 0

VARIABLES valL, nodeL, lhL, rhL, valR, nodeR, lhR, rhR, lhPL, rhPL, resultPL, 
          nxtPL, lhPR, rhPR, resultPR, nxtPR, myVal

vars == << mem, LeftHat, RightHat, freelist, valBag, pc, stack, valL, nodeL, 
           lhL, rhL, valR, nodeR, lhR, rhR, lhPL, rhPL, resultPL, nxtPL, lhPR, 
           rhPR, resultPR, nxtPR, myVal >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ mem = [a \in Addr |-> [val |-> defaultInitValue, left |-> Null, right |-> Null]]
        /\ LeftHat = Null
        /\ RightHat = Null
        /\ freelist = Addr
        /\ valBag = [v \in Val |-> 0]
        (* Procedure pushLeft *)
        /\ valL = [self \in ProcSet |-> defaultInitValue]
        /\ nodeL = [self \in ProcSet |-> Null]
        /\ lhL = [self \in ProcSet |-> Null]
        /\ rhL = [self \in ProcSet |-> Null]
        (* Procedure pushRight *)
        /\ valR = [self \in ProcSet |-> defaultInitValue]
        /\ nodeR = [self \in ProcSet |-> Null]
        /\ lhR = [self \in ProcSet |-> Null]
        /\ rhR = [self \in ProcSet |-> Null]
        (* Procedure popLeft *)
        /\ lhPL = [self \in ProcSet |-> Null]
        /\ rhPL = [self \in ProcSet |-> Null]
        /\ resultPL = [self \in ProcSet |-> defaultInitValue]
        /\ nxtPL = [self \in ProcSet |-> Null]
        (* Procedure popRight *)
        /\ lhPR = [self \in ProcSet |-> Null]
        /\ rhPR = [self \in ProcSet |-> Null]
        /\ resultPR = [self \in ProcSet |-> defaultInitValue]
        /\ nxtPR = [self \in ProcSet |-> Null]
        (* Process test *)
        /\ myVal = [self \in Procs |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "T1"]

PL1(self) == /\ pc[self] = "PL1"
             /\ IF freelist /= {}
                   THEN /\ \E a \in freelist:
                             /\ nodeL' = [nodeL EXCEPT ![self] = a]
                             /\ freelist' = freelist \ {a}
                   ELSE /\ nodeL' = [nodeL EXCEPT ![self] = Null]
                        /\ UNCHANGED freelist
             /\ pc' = [pc EXCEPT ![self] = "PL2"]
             /\ UNCHANGED << mem, LeftHat, RightHat, valBag, stack, valL, lhL, 
                             rhL, valR, nodeR, lhR, rhR, lhPL, rhPL, resultPL, 
                             nxtPL, lhPR, rhPR, resultPR, nxtPR, myVal >>

PL2(self) == /\ pc[self] = "PL2"
             /\ IF nodeL[self] = Null
                   THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ nodeL' = [nodeL EXCEPT ![self] = Head(stack[self]).nodeL]
                        /\ lhL' = [lhL EXCEPT ![self] = Head(stack[self]).lhL]
                        /\ rhL' = [rhL EXCEPT ![self] = Head(stack[self]).rhL]
                        /\ valL' = [valL EXCEPT ![self] = Head(stack[self]).valL]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "PL3"]
                        /\ UNCHANGED << stack, valL, nodeL, lhL, rhL >>
             /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, valR, 
                             nodeR, lhR, rhR, lhPL, rhPL, resultPL, nxtPL, 
                             lhPR, rhPR, resultPR, nxtPR, myVal >>

PL3(self) == /\ pc[self] = "PL3"
             /\ mem' = [mem EXCEPT ![nodeL[self]].val = valL[self],
                                   ![nodeL[self]].left = Null]
             /\ pc' = [pc EXCEPT ![self] = "PL4"]
             /\ UNCHANGED << LeftHat, RightHat, freelist, valBag, stack, valL, 
                             nodeL, lhL, rhL, valR, nodeR, lhR, rhR, lhPL, 
                             rhPL, resultPL, nxtPL, lhPR, rhPR, resultPR, 
                             nxtPR, myVal >>

PL4(self) == /\ pc[self] = "PL4"
             /\ lhL' = [lhL EXCEPT ![self] = LeftHat]
             /\ rhL' = [rhL EXCEPT ![self] = RightHat]
             /\ pc' = [pc EXCEPT ![self] = "PL5"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, stack, 
                             valL, nodeL, valR, nodeR, lhR, rhR, lhPL, rhPL, 
                             resultPL, nxtPL, lhPR, rhPR, resultPR, nxtPR, 
                             myVal >>

PL5(self) == /\ pc[self] = "PL5"
             /\ IF lhL[self] = Null
                   THEN /\ mem' = [mem EXCEPT ![nodeL[self]].right = Null]
                        /\ pc' = [pc EXCEPT ![self] = "PL6"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "PL7"]
                        /\ mem' = mem
             /\ UNCHANGED << LeftHat, RightHat, freelist, valBag, stack, valL, 
                             nodeL, lhL, rhL, valR, nodeR, lhR, rhR, lhPL, 
                             rhPL, resultPL, nxtPL, lhPR, rhPR, resultPR, 
                             nxtPR, myVal >>

PL6(self) == /\ pc[self] = "PL6"
             /\ IF LeftHat = Null /\ RightHat = Null
                   THEN /\ LeftHat' = nodeL[self]
                        /\ RightHat' = nodeL[self]
                        /\ valBag' = [valBag EXCEPT ![valL[self]] = valBag[valL[self]] + 1]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ nodeL' = [nodeL EXCEPT ![self] = Head(stack[self]).nodeL]
                        /\ lhL' = [lhL EXCEPT ![self] = Head(stack[self]).lhL]
                        /\ rhL' = [rhL EXCEPT ![self] = Head(stack[self]).rhL]
                        /\ valL' = [valL EXCEPT ![self] = Head(stack[self]).valL]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "PL4"]
                        /\ UNCHANGED << LeftHat, RightHat, valBag, stack, valL, 
                                        nodeL, lhL, rhL >>
             /\ UNCHANGED << mem, freelist, valR, nodeR, lhR, rhR, lhPL, rhPL, 
                             resultPL, nxtPL, lhPR, rhPR, resultPR, nxtPR, 
                             myVal >>

PL7(self) == /\ pc[self] = "PL7"
             /\ mem' = [mem EXCEPT ![nodeL[self]].right = lhL[self]]
             /\ pc' = [pc EXCEPT ![self] = "PL8"]
             /\ UNCHANGED << LeftHat, RightHat, freelist, valBag, stack, valL, 
                             nodeL, lhL, rhL, valR, nodeR, lhR, rhR, lhPL, 
                             rhPL, resultPL, nxtPL, lhPR, rhPR, resultPR, 
                             nxtPR, myVal >>

PL8(self) == /\ pc[self] = "PL8"
             /\ IF LeftHat = lhL[self] /\ mem[lhL[self]].left = Null
                   THEN /\ LeftHat' = nodeL[self]
                        /\ mem' = [mem EXCEPT ![lhL[self]].left = nodeL[self]]
                        /\ valBag' = [valBag EXCEPT ![valL[self]] = valBag[valL[self]] + 1]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ nodeL' = [nodeL EXCEPT ![self] = Head(stack[self]).nodeL]
                        /\ lhL' = [lhL EXCEPT ![self] = Head(stack[self]).lhL]
                        /\ rhL' = [rhL EXCEPT ![self] = Head(stack[self]).rhL]
                        /\ valL' = [valL EXCEPT ![self] = Head(stack[self]).valL]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "PL4"]
                        /\ UNCHANGED << mem, LeftHat, valBag, stack, valL, 
                                        nodeL, lhL, rhL >>
             /\ UNCHANGED << RightHat, freelist, valR, nodeR, lhR, rhR, lhPL, 
                             rhPL, resultPL, nxtPL, lhPR, rhPR, resultPR, 
                             nxtPR, myVal >>

pushLeft(self) == PL1(self) \/ PL2(self) \/ PL3(self) \/ PL4(self)
                     \/ PL5(self) \/ PL6(self) \/ PL7(self) \/ PL8(self)

PR1(self) == /\ pc[self] = "PR1"
             /\ IF freelist /= {}
                   THEN /\ \E a \in freelist:
                             /\ nodeR' = [nodeR EXCEPT ![self] = a]
                             /\ freelist' = freelist \ {a}
                   ELSE /\ nodeR' = [nodeR EXCEPT ![self] = Null]
                        /\ UNCHANGED freelist
             /\ pc' = [pc EXCEPT ![self] = "PR2"]
             /\ UNCHANGED << mem, LeftHat, RightHat, valBag, stack, valL, 
                             nodeL, lhL, rhL, valR, lhR, rhR, lhPL, rhPL, 
                             resultPL, nxtPL, lhPR, rhPR, resultPR, nxtPR, 
                             myVal >>

PR2(self) == /\ pc[self] = "PR2"
             /\ IF nodeR[self] = Null
                   THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ nodeR' = [nodeR EXCEPT ![self] = Head(stack[self]).nodeR]
                        /\ lhR' = [lhR EXCEPT ![self] = Head(stack[self]).lhR]
                        /\ rhR' = [rhR EXCEPT ![self] = Head(stack[self]).rhR]
                        /\ valR' = [valR EXCEPT ![self] = Head(stack[self]).valR]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "PR3"]
                        /\ UNCHANGED << stack, valR, nodeR, lhR, rhR >>
             /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, valL, 
                             nodeL, lhL, rhL, lhPL, rhPL, resultPL, nxtPL, 
                             lhPR, rhPR, resultPR, nxtPR, myVal >>

PR3(self) == /\ pc[self] = "PR3"
             /\ mem' = [mem EXCEPT ![nodeR[self]].val = valR[self],
                                   ![nodeR[self]].right = Null]
             /\ pc' = [pc EXCEPT ![self] = "PR4"]
             /\ UNCHANGED << LeftHat, RightHat, freelist, valBag, stack, valL, 
                             nodeL, lhL, rhL, valR, nodeR, lhR, rhR, lhPL, 
                             rhPL, resultPL, nxtPL, lhPR, rhPR, resultPR, 
                             nxtPR, myVal >>

PR4(self) == /\ pc[self] = "PR4"
             /\ lhR' = [lhR EXCEPT ![self] = LeftHat]
             /\ rhR' = [rhR EXCEPT ![self] = RightHat]
             /\ pc' = [pc EXCEPT ![self] = "PR5"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, stack, 
                             valL, nodeL, lhL, rhL, valR, nodeR, lhPL, rhPL, 
                             resultPL, nxtPL, lhPR, rhPR, resultPR, nxtPR, 
                             myVal >>

PR5(self) == /\ pc[self] = "PR5"
             /\ IF rhR[self] = Null
                   THEN /\ mem' = [mem EXCEPT ![nodeR[self]].left = Null]
                        /\ pc' = [pc EXCEPT ![self] = "PR6"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "PR7"]
                        /\ mem' = mem
             /\ UNCHANGED << LeftHat, RightHat, freelist, valBag, stack, valL, 
                             nodeL, lhL, rhL, valR, nodeR, lhR, rhR, lhPL, 
                             rhPL, resultPL, nxtPL, lhPR, rhPR, resultPR, 
                             nxtPR, myVal >>

PR6(self) == /\ pc[self] = "PR6"
             /\ IF LeftHat = Null /\ RightHat = Null
                   THEN /\ LeftHat' = nodeR[self]
                        /\ RightHat' = nodeR[self]
                        /\ valBag' = [valBag EXCEPT ![valR[self]] = valBag[valR[self]] + 1]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ nodeR' = [nodeR EXCEPT ![self] = Head(stack[self]).nodeR]
                        /\ lhR' = [lhR EXCEPT ![self] = Head(stack[self]).lhR]
                        /\ rhR' = [rhR EXCEPT ![self] = Head(stack[self]).rhR]
                        /\ valR' = [valR EXCEPT ![self] = Head(stack[self]).valR]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "PR4"]
                        /\ UNCHANGED << LeftHat, RightHat, valBag, stack, valR, 
                                        nodeR, lhR, rhR >>
             /\ UNCHANGED << mem, freelist, valL, nodeL, lhL, rhL, lhPL, rhPL, 
                             resultPL, nxtPL, lhPR, rhPR, resultPR, nxtPR, 
                             myVal >>

PR7(self) == /\ pc[self] = "PR7"
             /\ mem' = [mem EXCEPT ![nodeR[self]].left = rhR[self]]
             /\ pc' = [pc EXCEPT ![self] = "PR8"]
             /\ UNCHANGED << LeftHat, RightHat, freelist, valBag, stack, valL, 
                             nodeL, lhL, rhL, valR, nodeR, lhR, rhR, lhPL, 
                             rhPL, resultPL, nxtPL, lhPR, rhPR, resultPR, 
                             nxtPR, myVal >>

PR8(self) == /\ pc[self] = "PR8"
             /\ IF RightHat = rhR[self] /\ mem[rhR[self]].right = Null
                   THEN /\ RightHat' = nodeR[self]
                        /\ mem' = [mem EXCEPT ![rhR[self]].right = nodeR[self]]
                        /\ valBag' = [valBag EXCEPT ![valR[self]] = valBag[valR[self]] + 1]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ nodeR' = [nodeR EXCEPT ![self] = Head(stack[self]).nodeR]
                        /\ lhR' = [lhR EXCEPT ![self] = Head(stack[self]).lhR]
                        /\ rhR' = [rhR EXCEPT ![self] = Head(stack[self]).rhR]
                        /\ valR' = [valR EXCEPT ![self] = Head(stack[self]).valR]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "PR4"]
                        /\ UNCHANGED << mem, RightHat, valBag, stack, valR, 
                                        nodeR, lhR, rhR >>
             /\ UNCHANGED << LeftHat, freelist, valL, nodeL, lhL, rhL, lhPL, 
                             rhPL, resultPL, nxtPL, lhPR, rhPR, resultPR, 
                             nxtPR, myVal >>

pushRight(self) == PR1(self) \/ PR2(self) \/ PR3(self) \/ PR4(self)
                      \/ PR5(self) \/ PR6(self) \/ PR7(self) \/ PR8(self)

OL1(self) == /\ pc[self] = "OL1"
             /\ lhPL' = [lhPL EXCEPT ![self] = LeftHat]
             /\ rhPL' = [rhPL EXCEPT ![self] = RightHat]
             /\ pc' = [pc EXCEPT ![self] = "OL2"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, stack, 
                             valL, nodeL, lhL, rhL, valR, nodeR, lhR, rhR, 
                             resultPL, nxtPL, lhPR, rhPR, resultPR, nxtPR, 
                             myVal >>

OL2(self) == /\ pc[self] = "OL2"
             /\ IF lhPL[self] = Null
                   THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ lhPL' = [lhPL EXCEPT ![self] = Head(stack[self]).lhPL]
                        /\ rhPL' = [rhPL EXCEPT ![self] = Head(stack[self]).rhPL]
                        /\ resultPL' = [resultPL EXCEPT ![self] = Head(stack[self]).resultPL]
                        /\ nxtPL' = [nxtPL EXCEPT ![self] = Head(stack[self]).nxtPL]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "OL3"]
                        /\ UNCHANGED << stack, lhPL, rhPL, resultPL, nxtPL >>
             /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, valL, 
                             nodeL, lhL, rhL, valR, nodeR, lhR, rhR, lhPR, 
                             rhPR, resultPR, nxtPR, myVal >>

OL3(self) == /\ pc[self] = "OL3"
             /\ IF lhPL[self] = rhPL[self]
                   THEN /\ pc' = [pc EXCEPT ![self] = "OL4"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "OL5"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, stack, 
                             valL, nodeL, lhL, rhL, valR, nodeR, lhR, rhR, 
                             lhPL, rhPL, resultPL, nxtPL, lhPR, rhPR, resultPR, 
                             nxtPR, myVal >>

OL4(self) == /\ pc[self] = "OL4"
             /\ IF LeftHat = lhPL[self] /\ RightHat = rhPL[self]
                   THEN /\ resultPL' = [resultPL EXCEPT ![self] = mem[lhPL[self]].val]
                        /\ LeftHat' = Null
                        /\ RightHat' = Null
                        /\ valBag' = [valBag EXCEPT ![resultPL'[self]] = valBag[resultPL'[self]] - 1]
                        /\ IF lhPL[self] /= Null
                              THEN /\ freelist' = (freelist \cup {lhPL[self]})
                              ELSE /\ UNCHANGED freelist
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ lhPL' = [lhPL EXCEPT ![self] = Head(stack[self]).lhPL]
                        /\ rhPL' = [rhPL EXCEPT ![self] = Head(stack[self]).rhPL]
                        /\ nxtPL' = [nxtPL EXCEPT ![self] = Head(stack[self]).nxtPL]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "OL1"]
                        /\ UNCHANGED << LeftHat, RightHat, freelist, valBag, 
                                        stack, lhPL, rhPL, resultPL, nxtPL >>
             /\ UNCHANGED << mem, valL, nodeL, lhL, rhL, valR, nodeR, lhR, rhR, 
                             lhPR, rhPR, resultPR, nxtPR, myVal >>

OL5(self) == /\ pc[self] = "OL5"
             /\ nxtPL' = [nxtPL EXCEPT ![self] = mem[lhPL[self]].right]
             /\ pc' = [pc EXCEPT ![self] = "OL6"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, stack, 
                             valL, nodeL, lhL, rhL, valR, nodeR, lhR, rhR, 
                             lhPL, rhPL, resultPL, lhPR, rhPR, resultPR, nxtPR, 
                             myVal >>

OL6(self) == /\ pc[self] = "OL6"
             /\ IF nxtPL[self] = Null
                   THEN /\ pc' = [pc EXCEPT ![self] = "OL1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "OL7"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, stack, 
                             valL, nodeL, lhL, rhL, valR, nodeR, lhR, rhR, 
                             lhPL, rhPL, resultPL, nxtPL, lhPR, rhPR, resultPR, 
                             nxtPR, myVal >>

OL7(self) == /\ pc[self] = "OL7"
             /\ IF LeftHat = lhPL[self] /\ mem[nxtPL[self]].left = lhPL[self]
                   THEN /\ resultPL' = [resultPL EXCEPT ![self] = mem[lhPL[self]].val]
                        /\ LeftHat' = nxtPL[self]
                        /\ mem' = [mem EXCEPT ![nxtPL[self]].left = Null]
                        /\ valBag' = [valBag EXCEPT ![resultPL'[self]] = valBag[resultPL'[self]] - 1]
                        /\ IF lhPL[self] /= Null
                              THEN /\ freelist' = (freelist \cup {lhPL[self]})
                              ELSE /\ UNCHANGED freelist
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ lhPL' = [lhPL EXCEPT ![self] = Head(stack[self]).lhPL]
                        /\ rhPL' = [rhPL EXCEPT ![self] = Head(stack[self]).rhPL]
                        /\ nxtPL' = [nxtPL EXCEPT ![self] = Head(stack[self]).nxtPL]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "OL1"]
                        /\ UNCHANGED << mem, LeftHat, freelist, valBag, stack, 
                                        lhPL, rhPL, resultPL, nxtPL >>
             /\ UNCHANGED << RightHat, valL, nodeL, lhL, rhL, valR, nodeR, lhR, 
                             rhR, lhPR, rhPR, resultPR, nxtPR, myVal >>

popLeft(self) == OL1(self) \/ OL2(self) \/ OL3(self) \/ OL4(self)
                    \/ OL5(self) \/ OL6(self) \/ OL7(self)

OR1(self) == /\ pc[self] = "OR1"
             /\ lhPR' = [lhPR EXCEPT ![self] = LeftHat]
             /\ rhPR' = [rhPR EXCEPT ![self] = RightHat]
             /\ pc' = [pc EXCEPT ![self] = "OR2"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, stack, 
                             valL, nodeL, lhL, rhL, valR, nodeR, lhR, rhR, 
                             lhPL, rhPL, resultPL, nxtPL, resultPR, nxtPR, 
                             myVal >>

OR2(self) == /\ pc[self] = "OR2"
             /\ IF rhPR[self] = Null
                   THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ lhPR' = [lhPR EXCEPT ![self] = Head(stack[self]).lhPR]
                        /\ rhPR' = [rhPR EXCEPT ![self] = Head(stack[self]).rhPR]
                        /\ resultPR' = [resultPR EXCEPT ![self] = Head(stack[self]).resultPR]
                        /\ nxtPR' = [nxtPR EXCEPT ![self] = Head(stack[self]).nxtPR]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "OR3"]
                        /\ UNCHANGED << stack, lhPR, rhPR, resultPR, nxtPR >>
             /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, valL, 
                             nodeL, lhL, rhL, valR, nodeR, lhR, rhR, lhPL, 
                             rhPL, resultPL, nxtPL, myVal >>

OR3(self) == /\ pc[self] = "OR3"
             /\ IF lhPR[self] = rhPR[self]
                   THEN /\ pc' = [pc EXCEPT ![self] = "OR4"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "OR5"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, stack, 
                             valL, nodeL, lhL, rhL, valR, nodeR, lhR, rhR, 
                             lhPL, rhPL, resultPL, nxtPL, lhPR, rhPR, resultPR, 
                             nxtPR, myVal >>

OR4(self) == /\ pc[self] = "OR4"
             /\ IF LeftHat = lhPR[self] /\ RightHat = rhPR[self]
                   THEN /\ resultPR' = [resultPR EXCEPT ![self] = mem[rhPR[self]].val]
                        /\ LeftHat' = Null
                        /\ RightHat' = Null
                        /\ valBag' = [valBag EXCEPT ![resultPR'[self]] = valBag[resultPR'[self]] - 1]
                        /\ IF rhPR[self] /= Null
                              THEN /\ freelist' = (freelist \cup {rhPR[self]})
                              ELSE /\ UNCHANGED freelist
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ lhPR' = [lhPR EXCEPT ![self] = Head(stack[self]).lhPR]
                        /\ rhPR' = [rhPR EXCEPT ![self] = Head(stack[self]).rhPR]
                        /\ nxtPR' = [nxtPR EXCEPT ![self] = Head(stack[self]).nxtPR]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "OR1"]
                        /\ UNCHANGED << LeftHat, RightHat, freelist, valBag, 
                                        stack, lhPR, rhPR, resultPR, nxtPR >>
             /\ UNCHANGED << mem, valL, nodeL, lhL, rhL, valR, nodeR, lhR, rhR, 
                             lhPL, rhPL, resultPL, nxtPL, myVal >>

OR5(self) == /\ pc[self] = "OR5"
             /\ nxtPR' = [nxtPR EXCEPT ![self] = mem[rhPR[self]].left]
             /\ pc' = [pc EXCEPT ![self] = "OR6"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, stack, 
                             valL, nodeL, lhL, rhL, valR, nodeR, lhR, rhR, 
                             lhPL, rhPL, resultPL, nxtPL, lhPR, rhPR, resultPR, 
                             myVal >>

OR6(self) == /\ pc[self] = "OR6"
             /\ IF nxtPR[self] = Null
                   THEN /\ pc' = [pc EXCEPT ![self] = "OR1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "OR7"]
             /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, stack, 
                             valL, nodeL, lhL, rhL, valR, nodeR, lhR, rhR, 
                             lhPL, rhPL, resultPL, nxtPL, lhPR, rhPR, resultPR, 
                             nxtPR, myVal >>

OR7(self) == /\ pc[self] = "OR7"
             /\ IF RightHat = rhPR[self] /\ mem[nxtPR[self]].right = rhPR[self]
                   THEN /\ resultPR' = [resultPR EXCEPT ![self] = mem[rhPR[self]].val]
                        /\ RightHat' = nxtPR[self]
                        /\ mem' = [mem EXCEPT ![nxtPR[self]].right = Null]
                        /\ valBag' = [valBag EXCEPT ![resultPR'[self]] = valBag[resultPR'[self]] - 1]
                        /\ IF rhPR[self] /= Null
                              THEN /\ freelist' = (freelist \cup {rhPR[self]})
                              ELSE /\ UNCHANGED freelist
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ lhPR' = [lhPR EXCEPT ![self] = Head(stack[self]).lhPR]
                        /\ rhPR' = [rhPR EXCEPT ![self] = Head(stack[self]).rhPR]
                        /\ nxtPR' = [nxtPR EXCEPT ![self] = Head(stack[self]).nxtPR]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "OR1"]
                        /\ UNCHANGED << mem, RightHat, freelist, valBag, stack, 
                                        lhPR, rhPR, resultPR, nxtPR >>
             /\ UNCHANGED << LeftHat, valL, nodeL, lhL, rhL, valR, nodeR, lhR, 
                             rhR, lhPL, rhPL, resultPL, nxtPL, myVal >>

popRight(self) == OR1(self) \/ OR2(self) \/ OR3(self) \/ OR4(self)
                     \/ OR5(self) \/ OR6(self) \/ OR7(self)

T1(self) == /\ pc[self] = "T1"
            /\ \/ /\ \E v \in Val:
                       myVal' = [myVal EXCEPT ![self] = v]
                  /\ pc' = [pc EXCEPT ![self] = "T2"]
               \/ /\ \E v \in Val:
                       myVal' = [myVal EXCEPT ![self] = v]
                  /\ pc' = [pc EXCEPT ![self] = "T3"]
               \/ /\ pc' = [pc EXCEPT ![self] = "T4"]
                  /\ UNCHANGED myVal
               \/ /\ pc' = [pc EXCEPT ![self] = "T5"]
                  /\ UNCHANGED myVal
            /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, stack, 
                            valL, nodeL, lhL, rhL, valR, nodeR, lhR, rhR, lhPL, 
                            rhPL, resultPL, nxtPL, lhPR, rhPR, resultPR, nxtPR >>

T2(self) == /\ pc[self] = "T2"
            /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "pushLeft",
                                                        pc        |->  "T1",
                                                        nodeL     |->  nodeL[self],
                                                        lhL       |->  lhL[self],
                                                        rhL       |->  rhL[self],
                                                        valL      |->  valL[self] ] >>
                                                    \o stack[self]]
               /\ valL' = [valL EXCEPT ![self] = myVal[self]]
            /\ nodeL' = [nodeL EXCEPT ![self] = Null]
            /\ lhL' = [lhL EXCEPT ![self] = Null]
            /\ rhL' = [rhL EXCEPT ![self] = Null]
            /\ pc' = [pc EXCEPT ![self] = "PL1"]
            /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, valR, 
                            nodeR, lhR, rhR, lhPL, rhPL, resultPL, nxtPL, lhPR, 
                            rhPR, resultPR, nxtPR, myVal >>

T3(self) == /\ pc[self] = "T3"
            /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "pushRight",
                                                        pc        |->  "T1",
                                                        nodeR     |->  nodeR[self],
                                                        lhR       |->  lhR[self],
                                                        rhR       |->  rhR[self],
                                                        valR      |->  valR[self] ] >>
                                                    \o stack[self]]
               /\ valR' = [valR EXCEPT ![self] = myVal[self]]
            /\ nodeR' = [nodeR EXCEPT ![self] = Null]
            /\ lhR' = [lhR EXCEPT ![self] = Null]
            /\ rhR' = [rhR EXCEPT ![self] = Null]
            /\ pc' = [pc EXCEPT ![self] = "PR1"]
            /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, valL, 
                            nodeL, lhL, rhL, lhPL, rhPL, resultPL, nxtPL, lhPR, 
                            rhPR, resultPR, nxtPR, myVal >>

T4(self) == /\ pc[self] = "T4"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "popLeft",
                                                     pc        |->  "T1",
                                                     lhPL      |->  lhPL[self],
                                                     rhPL      |->  rhPL[self],
                                                     resultPL  |->  resultPL[self],
                                                     nxtPL     |->  nxtPL[self] ] >>
                                                 \o stack[self]]
            /\ lhPL' = [lhPL EXCEPT ![self] = Null]
            /\ rhPL' = [rhPL EXCEPT ![self] = Null]
            /\ resultPL' = [resultPL EXCEPT ![self] = defaultInitValue]
            /\ nxtPL' = [nxtPL EXCEPT ![self] = Null]
            /\ pc' = [pc EXCEPT ![self] = "OL1"]
            /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, valL, 
                            nodeL, lhL, rhL, valR, nodeR, lhR, rhR, lhPR, rhPR, 
                            resultPR, nxtPR, myVal >>

T5(self) == /\ pc[self] = "T5"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "popRight",
                                                     pc        |->  "T1",
                                                     lhPR      |->  lhPR[self],
                                                     rhPR      |->  rhPR[self],
                                                     resultPR  |->  resultPR[self],
                                                     nxtPR     |->  nxtPR[self] ] >>
                                                 \o stack[self]]
            /\ lhPR' = [lhPR EXCEPT ![self] = Null]
            /\ rhPR' = [rhPR EXCEPT ![self] = Null]
            /\ resultPR' = [resultPR EXCEPT ![self] = defaultInitValue]
            /\ nxtPR' = [nxtPR EXCEPT ![self] = Null]
            /\ pc' = [pc EXCEPT ![self] = "OR1"]
            /\ UNCHANGED << mem, LeftHat, RightHat, freelist, valBag, valL, 
                            nodeL, lhL, rhL, valR, nodeR, lhR, rhR, lhPL, rhPL, 
                            resultPL, nxtPL, myVal >>

test(self) == T1(self) \/ T2(self) \/ T3(self) \/ T4(self) \/ T5(self)

Next == (\E self \in ProcSet:  \/ pushLeft(self) \/ pushRight(self)
                               \/ popLeft(self) \/ popRight(self))
           \/ (\E self \in Procs: test(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : /\ WF_vars(test(self))
                               /\ WF_vars(pushLeft(self))
                               /\ WF_vars(pushRight(self))
                               /\ WF_vars(popLeft(self))
                               /\ WF_vars(popRight(self))

\* END TRANSLATION

Liveness == \A self \in Procs : []<>(pc[self] = "T1")

=============================================================================