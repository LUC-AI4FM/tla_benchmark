---- MODULE DoubleEndedQueue ----
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS MaxProc, MaxAddr

VARIABLES mem, leftHat, rightHat, freeList, valBag, procPC, procVar

(* --algorithm deq

variables 
    mem = [a \in 1..MaxAddr |-> <<NIL, NIL>>, a],  (* Memory mapping: address -> <<prev, next>> *)
    leftHat = 0,                                   (* Left end of the deque *)
    rightHat = 0,                                  (* Right end of the deque *)
    freeList = {1..MaxAddr},                       (* Free list for node allocation *)
    valBag = {},                                   (* Multiset consistency check *)
    procPC = [p \in 1..MaxProc |-> "T1"],          (* Program counters for each process *)
    procVar = [p \in 1..MaxProc |-> <<NIL, NIL>>]  (* Local variables for each process *)

process (P \in 1..MaxProc)
begin
T1: with (leftHat \/ rightHat \/ ~ freeList = {}) 
     do await leftHat \/ rightHat \/ ~ freeList = {}
        if /\ leftHat = 0
           /\ rightHat = 0
        then
            either
                procPC[P] := "pushLeft"
            or
                procPC[P] := "pushRight"
            end either;
        else
            if /\ leftHat # 0
               /\ rightHat # 0
            then
                either
                    procPC[P] := "popLeft"
                or
                    procPC[P] := "popRight"
                end either;
            else
                if leftHat = 0
                then
                    procPC[P] := "pushLeft"
                else
                    procPC[P] := "popLeft"
                end if;
            end if;
        end if;
    od;

pushLeft: 
    if ~ freeList = {} 
    then
        with (node \in freeList) 
        do
            mem[node] := <<NIL, leftHat>>;
            if leftHat # 0 
            then
                mem[leftHat][1] := node;
            end if;
            leftHat := node;
            valBag := valBag \cup {P};
            freeList := freeList \ {node};
        end with;
    end if;
    procPC[P] := "T1";

pushRight: 
    if ~ freeList = {} 
    then
        with (node \in freeList) 
        do
            mem[node] := <<rightHat, NIL>>;
            if rightHat # 0 
            then
                mem[rightHat][2] := node;
            end if;
            rightHat := node;
            valBag := valBag \cup {P};
            freeList := freeList \ {node};
        end with;
    end if;
    procPC[P] := "T1";

popLeft: 
    if leftHat # 0 
    then
        let 
            node == leftHat,
            nextNode == mem[node][2]
        in
            leftHat := nextNode;
            if nextNode # 0 
            then
                mem[nextNode][1] := NIL;
            end if;
            valBag := valBag \ {P};
            freeList := freeList \cup {node}
        end let;
    end if;
    procPC[P] := "T1";

popRight: 
    if rightHat # 0 
    then
        let 
            node == rightHat,
            prevNode == mem[node][1]
        in
            rightHat := prevNode;
            if prevNode # 0 
            then
                mem[prevNode][2] := NIL;
            end if;
            valBag := valBag \ {P};
            freeList := freeList \cup {node}
        end let;
    end if;
    procPC[P] := "T1";

end algorithm *)

Init == /\ mem = [a \in 1..MaxAddr |-> <<NIL, NIL>>, a]
        /\ leftHat = 0
        /\ rightHat = 0
        /\ freeList = {1..MaxAddr}
        /\ valBag = {}
        /\ procPC = [p \in 1..MaxProc |-> "T1"]
        /\ procVar = [p \in 1..MaxProc |-> <<NIL, NIL>>]

Next == \/ \E P \in 1..MaxProc : \/ procPC[P] = "T1" /\ [][P in T1]_<<P>>
            \/ procPC[P] = "pushLeft" /\ [][P in pushLeft]_<<P>>
            \/ procPC[P] = "pushRight" /\ [][P in pushRight]_<<P>>
            \/ procPC[P] = "popLeft" /\ [][P in popLeft]_<<P>>
            \/ procPC[P] = "popRight" /\ [][P in popRight]_<<P>>

Spec == Init /\ WF_next(Next)

WF_next(next) == \A S \in StateSets : next :> S \subseteq (S x S)

StateSets == {S \in SUBSET States: S /= {}}

States == {s \in [][mem, leftHat, rightHat, freeList, valBag, procPC, procVar] : TRUE}
====