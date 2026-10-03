```tla+
---------------------------- MODULE specification ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS defaultInitValue, Val

CONSTANTS Procs, Addr, NullAddr

(* Memory node record type: [val: Val, left: Addr, right: Addr] *)

(*--algorithm DoubleEndedQueue
variables
    mem = [a \in Addr |-> [val |-> defaultInitValue, left |-> NullAddr, right |-> NullAddr]],
    LHat = NullAddr,
    RHat = NullAddr,
    freelist = Addr,
    valBag = [v \in Val |-> 0];

define
    TypeOK ==
        /\ LHat \in Addr \cup {NullAddr}
        /\ RHat \in Addr \cup {NullAddr}
        /\ \A v \in Val : valBag[v] >= 0
end define;

macro Allocate(result) begin
    await freelist /= {};
    with a \in freelist do
        result := a;
        freelist := freelist \ {a};
    end with;
end macro;

macro Free(a) begin
    freelist := freelist \cup {a};
end macro;

procedure pushLeft(valL = defaultInitValue)
variables nodeL = NullAddr, oldLHat = NullAddr, oldRHat = NullAddr;
begin
PL1: Allocate(nodeL);
PL2: mem := [mem EXCEPT ![nodeL].val = valL, ![nodeL].left = NullAddr];
PL3: oldLHat := LHat;
     oldRHat := RHat;
PL4: if oldLHat = NullAddr then
        mem := [mem EXCEPT ![nodeL].right = NullAddr];
PL5:    if LHat = NullAddr /\ RHat = NullAddr then
            LHat := nodeL;
            RHat := nodeL;
            valBag := [valBag EXCEPT ![valL] = @ + 1];
            return;
        else
            goto PL3;
        end if;
     else
        mem := [mem EXCEPT ![nodeL].right = oldLHat];
PL6:    if LHat = oldLHat /\ mem[oldLHat].left = NullAddr then
            mem := [mem EXCEPT ![oldLHat].left = nodeL];
            LHat := nodeL;
            valBag := [valBag EXCEPT ![valL] = @ + 1];
            return;
        else
            goto PL3;
        end if;
     end if;
end procedure;

procedure pushRight(valR = defaultInitValue)
variables nodeR = NullAddr, oldLHatR = NullAddr, oldRHatR = NullAddr;
begin
PR1: Allocate(nodeR);
PR2: mem := [mem EXCEPT ![nodeR].val = valR, ![nodeR].right = NullAddr];
PR3: oldLHatR := LHat;
     oldRHatR := RHat;
PR4: if oldRHatR = NullAddr then
        mem := [mem EXCEPT ![nodeR].left = NullAddr];
PR5:    if LHat = NullAddr /\ RHat = NullAddr then
            LHat := nodeR;
            RHat := nodeR;
            valBag := [valBag EXCEPT ![valR] = @ + 1];
            return;
        else
            goto PR3;
        end if;
     else
        mem := [mem EXCEPT ![nodeR].left = oldRHatR];
PR6:    if RHat = oldRHatR /\ mem[oldRHatR].right = NullAddr then
            mem := [mem EXCEPT ![oldRHatR].right = nodeR];
            RHat := nodeR;
            valBag := [valBag EXCEPT ![valR] = @ + 1];
            return;
        else
            goto PR3;
        end if;
     end if;
end procedure;

procedure popLeft()
variables oldLHatPL = NullAddr, oldRHatPL = NullAddr, nodeValL = defaultInitValue, nextL = NullAddr;
begin
POL1: oldLHatPL := LHat;
      oldRHatPL := RHat;
POL2: if oldLHatPL = NullAddr then
         return;
      end if;
POL3: if oldLHatPL = oldRHatPL then
POL4:    if LHat = oldLHatPL /\ RHat = oldRHatPL then
            nodeValL := mem[oldLHatPL].val;
            LHat := NullAddr;
            RHat := NullAddr;
            valBag := [valBag EXCEPT ![nodeValL] = @ - 1];
            Free(oldLHatPL);
            return;
         else
            goto POL1;
         end if;
      else
         nextL := mem[oldLHatPL].right;
POL5:    if nextL /= NullAddr then
            if LHat = oldLHatPL /\ mem[nextL].left = oldLHatPL then
               nodeValL := mem[oldLHatPL].val;
               mem := [mem EXCEPT ![nextL].left = NullAddr];
               LHat := nextL;
               valBag := [valBag EXCEPT ![nodeValL] = @ - 1];
               Free(oldLHatPL);
               return;
            else
               goto POL1;
            end if;
         else
            goto POL1;
         end if;
      end if;
end procedure;

procedure popRight()
variables oldLHatPR = NullAddr, oldRHatPR = NullAddr, nodeValR = defaultInitValue, nextR = NullAddr;
begin
POR1: oldLHatPR := LHat;
      oldRHatPR := RHat;
POR2: if oldRHatPR = NullAddr then
         return;
      end if;
POR3: if oldLHatPR = oldRHatPR then
POR4:    if LHat = oldLHatPR /\ RHat = oldRHatPR then
            nodeValR := mem[oldRHatPR].val;
            LHat := NullAddr;
            RHat := NullAddr;
            valBag := [valBag EXCEPT ![nodeValR] = @ - 1];
            Free(oldRHatPR);
            return;
         else
            goto POR1;
         end if;
      else
         nextR := mem[oldRHatPR].left;
POR5:    if nextR /= NullAddr then
            if RHat = oldRHatPR /\ mem[nextR].right = oldRHatPR then
               nodeValR := mem[oldRHatPR].val;
               mem := [mem EXCEPT ![nextR].right = NullAddr];
               RHat := nextR;
               valBag := [valBag EXCEPT ![nodeValR] = @ - 1];
               Free(oldRHatPR);
               return;
            else
               goto POR1;
            end if;
         else
            goto POR1;
         end if;
      end if;
end procedure;

fair process test \in Procs
variables localVal = defaultInitValue;
begin
T1: while TRUE do
      either
        with v \in Val do
          localVal := v;
        end with;
T2:     call pushLeft(localVal);
      or
        with v \in Val do
          localVal := v;
        end with;
T3:     call pushRight(localVal);
      or
T4:     call popLeft();
      or
T5:     call popRight();
      end either;
    end while;
end process;

end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES mem, LHat, RHat, freelist, valBag, pc, stack

(* define statement *)
TypeOK ==
    /\ LHat \in Addr \cup {NullAddr}
    /\ RHat \in Addr \cup {NullAddr}
    /\ \A v \in Val : valBag[v] >= 0

VARIABLES valL, nodeL, oldLHat, oldRHat, valR, nodeR, oldLHatR, oldRHatR, 
          oldLHatPL, oldRHatPL, nodeValL, nextL, oldLHatPR, oldRHatPR, 
          nodeValR, nextR, localVal

vars == << mem, LHat, RHat, freelist, valBag, pc, stack, valL, nodeL, oldLHat, 
           oldRHat, valR, nodeR, oldLHatR, oldRHatR, oldLHatPL, oldRHatPL, 
           nodeValL, nextL, oldLHatPR, oldRHatPR, nodeValR, nextR, localVal >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ mem = [a \in Addr |-> [val |-> defaultInitValue, left |-> NullAddr, right |-> NullAddr]]
        /\ LHat = NullAddr
        /\ RHat = NullAddr
        /\ freelist = Addr
        /\ valBag = [v \in Val |-> 0]
        (* Procedure pushLeft *)
        /\ valL = [self \in ProcSet |-> defaultInitValue]
        /\ nodeL = [self \in ProcSet |-> NullAddr]
        /\ oldLHat = [self \in ProcSet |-> NullAddr]
        /\ oldRHat = [self \in ProcSet |-> NullAddr]
        (* Procedure pushRight *)
        /\ valR = [self \in ProcSet |-> defaultInitValue]
        /\ nodeR = [self \in ProcSet |-> NullAddr]
        /\ oldLHatR = [self \in ProcSet |-> NullAddr]
        /\ oldRHatR = [self \in ProcSet |-> NullAddr]
        (* Procedure popLeft *)
        /\ oldLHatPL = [self \in ProcSet |-> NullAddr]
        /\ oldRHatPL = [self \in ProcSet |-> NullAddr]
        /\ nodeValL = [self \in ProcSet |-> defaultInitValue]
        /\ nextL = [self \in ProcSet |-> NullAddr]
        (* Procedure popRight *)
        /\ oldLHatPR = [self \in ProcSet |-> NullAddr]
        /\ oldRHatPR = [self \in ProcSet |-> NullAddr]
        /\ nodeValR = [self \in ProcSet |-> defaultInitValue]
        /\ nextR = [self \in ProcSet |-> NullAddr]
        (* Process test *)
        /\ localVal = [self \in Procs |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "T1"]

PL1(self) == /\ pc[self] = "PL1"
             /\ freelist /= {}
             /\ \E a \in freelist:
                  /\ nodeL' = [nodeL EXCEPT ![self] = a]
                  /\ freelist' = freelist \ {a}
             /\ pc' = [pc EXCEPT ![self] = "PL2"]
             /\ UNCHANGED << mem, LHat, RHat, valBag, stack, valL, oldLHat, 
                             oldRHat, valR, nodeR, oldLHatR, oldRHatR, 
                             oldLHatPL, oldRHatPL, nodeValL, nextL, oldLHatPR, 
                             oldRHatPR, nodeValR, nextR, localVal >>

PL2(self) == /\ pc[self] = "PL2"
             /\ mem' = [mem EXCEPT ![nodeL[self]].val = valL[self], ![nodeL[self]].left = NullAddr]
             /\ pc' = [pc EXCEPT ![self] = "PL3"]
             /\ UNCHANGED << LHat, RHat, freelist, valBag, stack, valL, nodeL, 
                             oldLHat, oldRHat, valR, nodeR, oldLHatR, oldRHatR, 
                             oldLHatPL, oldRHatPL, nodeValL, nextL, oldLHatPR, 
                             oldRHatPR, nodeValR, nextR, localVal >>

PL3(self) == /\ pc[self] = "PL3"
             /\ oldLHat' = [oldLHat EXCEPT ![self] = LHat]
             /\ oldRHat' = [oldRHat EXCEPT ![self] = RHat]
             /\ pc' = [pc EXCEPT ![self] = "PL4"]
             /\ UNCHANGED << mem, LHat, RHat, freelist, valBag, stack, valL, 
                             nodeL, valR, nodeR, oldLHatR, oldRHatR, oldLHatPL, 
                             oldRHatPL, nodeValL, nextL, oldLHatPR, oldRHatPR, 
                             nodeValR, nextR, localVal >>

PL4(self) == /\ pc[self] = "PL4"
             /\ IF oldLHat[self] = NullAddr
                   THEN /\ mem' = [mem EXCEPT ![nodeL[self]].right = NullAddr]
                        /\ pc' = [pc EXCEPT ![self] = "PL5"]
                   ELSE /\ mem' = [mem EXCEPT ![nodeL[self]].right = oldLHat[self]]
                        /\ pc' = [pc EXCEPT ![self] = "PL6"]
             /\ UNCHANGED << LHat, RHat, freelist, valBag, stack, valL, nodeL, 
                             oldLHat, oldRHat, valR, nodeR, oldLHatR, oldRHatR, 
                             oldLHatPL, oldRHatPL, nodeValL, nextL, oldLHatPR, 
                             oldRHatPR, nodeValR, nextR, localVal >>

PL5(self) == /\ pc[self] = "PL5"
             /\ IF LHat = NullAddr /\ RHat = NullAddr
                   THEN /\ LHat' = nodeL[self]
                        /\ RHat' = nodeL[self]
                        /\ valBag' = [valBag EXCEPT ![valL[self]] = @ + 1]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ nodeL' = [nodeL EXCEPT ![self] = Head(stack[self]).nodeL]
                        /\ oldLHat' = [oldLHat EXCEPT ![self] = Head(stack[self]).oldLHat]
                        /\ oldRHat' = [oldRHat EXCEPT ![self] = Head(stack[self]).oldRHat]
                        /\ valL' = [valL EXCEPT ![self] = Head(stack[self]).valL]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "PL3"]
                        /\ UNCHANGED << LHat, RHat, valBag, stack, valL, nodeL, 
                                        oldLHat, oldRHat >>
             /\ UNCHANGED << mem, freelist, valR, nodeR, oldLHatR, oldRHatR, 
                             oldLHatPL, oldRHatPL, nodeValL, nextL, oldLHatPR, 
                             oldRHat