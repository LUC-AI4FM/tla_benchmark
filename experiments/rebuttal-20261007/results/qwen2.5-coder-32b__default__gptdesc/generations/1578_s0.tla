------------------------------- MODULE DoubleEndedQueue ------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS NumProcesses, MaxAddress

VARIABLES mem, leftHat, rightHat, freeList, valBag, pc

(*--algorithm double_ended_queue
variables 
  mem = [a \in 1..MaxAddress |-> <<NIL, NIL>>],  (* Memory mapping from addresses to node records *)
  leftHat = 0,                                    (* Left hat pointer *)
  rightHat = 0,                                   (* Right hat pointer *)
  freeList = 1..MaxAddress,                       (* Free list for allocation *)
  valBag = {},                                    (* Multiset-like consistency check *)
  pc = [p \in 1..NumProcesses |-> "T1"]           (* Program counters for each process *)

process (P \in 1..NumProcesses)
begin
T1: either
      await freeList /= {}
      with addr \in freeList do
        mem[addr] := <<NIL, NIL>>;
        freeList := freeList \ {addr};
        pc[P] := "pushLeft";
    or
      await freeList /= {}
      with addr \in freeList do
        mem[addr] := <<NIL, NIL>>;
        freeList := freeList \ {addr};
        pc[P] := "pushRight";
    or
      pc[P] := "popLeft"
    or
      pc[P] := "popRight"
  end either;

pushLeft:
  with oldLeftHat \in Nat,
       newLeftHat \in Nat,
       addr \in freeList do
    oldLeftHat := leftHat;
    newLeftHat := addr;
    if \/ mem[oldLeftHat][2] = NIL
       \/ /\ mem[oldLeftHat][2] # NIL
          /\ mem[mem[oldLeftHat][2]][1] = oldLeftHat then
      mem[newLeftHat] := <<NIL, oldLeftHat>>;
      leftHat := newLeftHat;
      valBag := valBag \cup {P};
      freeList := freeList \ {addr};
    pc[P] := "T1";

pushRight:
  with oldRightHat \in Nat,
       newRightHat \in Nat,
       addr \in freeList do
    oldRightHat := rightHat;
    newRightHat := addr;
    if \/ mem[oldRightHat][1] = NIL
       \/ /\ mem[oldRightHat][1] # NIL
          /\ mem[mem[oldRightHat][1]][2] = oldRightHat then
      mem[newRightHat] := <<oldRightHat, NIL>>;
      rightHat := newRightHat;
      valBag := valBag \cup {P};
      freeList := freeList \ {addr};
    pc[P] := "T1";

popLeft:
  with oldLeftHat \in Nat,
       newLeftHat \in Nat do
    oldLeftHat := leftHat;
    if mem[oldLeftHat][2] # NIL then
      newLeftHat := mem[oldLeftHat][2];
      valBag := valBag \ {P};
      freeList := freeList \cup {oldLeftHat};
      leftHat := newLeftHat;
    pc[P] := "T1";

popRight:
  with oldRightHat \in Nat,
       newRightHat \in Nat do
    oldRightHat := rightHat;
    if mem[oldRightHat][1] # NIL then
      newRightHat := mem[oldRightHat][1];
      valBag := valBag \ {P};
      freeList := freeList \cup {oldRightHat};
      rightHat := newRightHat;
    pc[P] := "T1";
end process;

end algorithm *)

Init == /\ mem = [a \in 1..MaxAddress |-> <<NIL, NIL>>]
        /\ leftHat = 0
        /\ rightHat = 0
        /\ freeList = 1..MaxAddress
        /\ valBag = {}
        /\ pc = [p \in 1..NumProcesses |-> "T1"]

Next == \/ \E P \in 1..NumProcesses : pc[P] = "T1" /\ PushLeftEnabled(P) /\ PushLeftAction(P)
        \/ \E P \in 1..NumProcesses : pc[P] = "T1" /\ PushRightEnabled(P) /\ PushRightAction(P)
        \/ \E P \in 1..NumProcesses : pc[P] = "T1" /\ PopLeftEnabled(P) /\ PopLeftAction(P)
        \/ \E P \in 1..NumProcesses : pc[P] = "T1" /\ PopRightEnabled(P) /\ PopRightAction(P)

PushLeftEnabled(P) == freeList /= {}

PushLeftAction(P) ==
  LET oldLeftHat == leftHat
      newLeftHat == CHOOSE addr \in freeList : TRUE
  IN \/ mem[oldLeftHat][2] = NIL
     \/ /\ mem[oldLeftHat][2] # NIL
        /\ mem[mem[oldLeftHat][2]][1] = oldLeftHat
    /\ mem[newLeftHat] := <<NIL, oldLeftHat>>
    /\ leftHat := newLeftHat
    /\ valBag := valBag \cup {P}
    /\ freeList := freeList \ {newLeftHat}
    /\ pc[P] := "T1"

PushRightEnabled(P) == freeList /= {}

PushRightAction(P) ==
  LET oldRightHat == rightHat
      newRightHat == CHOOSE addr \in freeList : TRUE
  IN \/ mem[oldRightHat][1] = NIL
     \/ /\ mem[oldRightHat][1] # NIL
        /\ mem[mem[oldRightHat][1]][2] = oldRightHat
    /\ mem[newRightHat] := <<oldRightHat, NIL>>
    /\ rightHat := newRightHat
    /\ valBag := valBag \cup {P}
    /\ freeList := freeList \ {newRightHat}
    /\ pc[P] := "T1"

PopLeftEnabled(P) == mem[leftHat][2] # NIL

PopLeftAction(P) ==
  LET oldLeftHat == leftHat
      newLeftHat == mem[oldLeftHat][2]
  IN valBag := valBag \ {P}
     /\ freeList := freeList \cup {oldLeftHat}
     /\ leftHat := newLeftHat
     /\ pc[P] := "T1"

PopRightEnabled(P) == mem[rightHat][1] # NIL

PopRightAction(P) ==
  LET oldRightHat == rightHat
      newRightHat == mem[oldRightHat][1]
  IN valBag := valBag \ {P}
     /\ freeList := freeList \cup {oldRightHat}
     /\ rightHat := newRightHat
     /\ pc[P] := "T1"

Spec ==
  /\ Init
  /\ [][Next]_<<mem, leftHat, rightHat, freeList, valBag, pc>>
  /\ WF_next(<<mem, leftHat, rightHat, freeList, valBag, pc>>)

WF_next(vars) == \A P \in 1..NumProcesses : WF_vars(pc[P], vars)

Liveness ==
  \A P \in 1..NumProcesses : <>[](pc[P] = "T1")

=============================================================================