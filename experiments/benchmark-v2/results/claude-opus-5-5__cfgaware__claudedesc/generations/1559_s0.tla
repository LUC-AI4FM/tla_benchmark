------------------------------ MODULE LockHS ------------------------------
(***************************************************************************)
(* A simple two-process Lock spec, augmented with a history variable      *)
(* h_turn and a stuttering variable s.  With these auxiliary variables    *)
(* each Lock behavior can be mapped to a behavior of Peterson's           *)
(* algorithm, whose entry into the critical section takes three steps.    *)
(***************************************************************************)
EXTENDS Integers

Procs == {0, 1}

Other(p) == 1 - p

(***************************************************************************)
(* Base Lock specification                                                 *)
(***************************************************************************)
VARIABLES pc, lock

vars == <<pc, lock>>

PCValues == {"l0", "l1", "cs", "l2"}

TypeOK == /\ pc \in [Procs -> PCValues]
          /\ lock \in BOOLEAN

Init == /\ pc = [p \in Procs |-> "l0"]
        /\ lock = FALSE

l0(p) == /\ pc[p] = "l0"
         /\ pc' = [pc EXCEPT ![p] = "l1"]
         /\ UNCHANGED lock

l1(p) == /\ pc[p] = "l1"
         /\ lock = FALSE
         /\ lock' = TRUE
         /\ pc' = [pc EXCEPT ![p] = "cs"]

cs(p) == /\ pc[p] = "cs"
         /\ pc' = [pc EXCEPT ![p] = "l2"]
         /\ UNCHANGED lock

l2(p) == /\ pc[p] = "l2"
         /\ lock' = FALSE
         /\ pc' = [pc EXCEPT ![p] = "l0"]

Next == \E p \in Procs : l0(p) \/ l1(p) \/ cs(p) \/ l2(p)

Spec == Init /\ [][Next]_vars

LockInv == \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(***************************************************************************)
(* Auxiliary variables: history variable h_turn and stuttering variable s *)
(***************************************************************************)
VARIABLES h_turn, s

top == [top |-> "top"]

StutterRecs == [id : {"l1"}, ctxt : Procs, val : {1, 2}]

(***************************************************************************)
(* PostStutter(A, ...): if no stuttering is in progress, perform A and    *)
(* start a stutter countdown at initVal; otherwise perform a stuttering   *)
(* step (leaving vars unchanged), decrementing the counter until bot.     *)
(***************************************************************************)
PostStutter(A, actionId, context, bot, initVal, decr(_)) ==
  IF s = top
    THEN /\ A
         /\ s' = IF initVal = bot
                   THEN top
                   ELSE [id |-> actionId, ctxt |-> context, val |-> initVal]
    ELSE /\ s.id = actionId
         /\ s.ctxt = context
         /\ UNCHANGED vars
         /\ s' = IF decr(s.val) = bot
                   THEN top
                   ELSE [s EXCEPT !.val = decr(s.val)]

varsHS == <<pc, lock, h_turn, s>>

InitHS == /\ Init
          /\ h_turn = 1
          /\ s = top

l0HS(p) == /\ s = top
           /\ l0(p)
           /\ UNCHANGED <<h_turn, s>>

l1HS(p) == /\ PostStutter(l1(p), "l1", p, 0, 2, LAMBDA j : j - 1)
           /\ h_turn' = IF s # top /\ s.val = 2 THEN Other(p) ELSE h_turn

csHS(p) == /\ s = top
           /\ cs(p)
           /\ UNCHANGED <<h_turn, s>>

l2HS(p) == /\ s = top
           /\ l2(p)
           /\ UNCHANGED <<h_turn, s>>

NextHS == \E p \in Procs : l0HS(p) \/ l1HS(p) \/ csHS(p) \/ l2HS(p)

SpecHS == InitHS /\ [][NextHS]_varsHS

TypeOKHS == /\ TypeOK
            /\ h_turn \in Procs
            /\ s \in {top} \cup StutterRecs

InvHS == /\ s # top =>
              /\ s.id = "l1"
              /\ s.ctxt \in Procs
              /\ pc[s.ctxt] = "cs"
              /\ s.val \in {1, 2}
              /\ (s.val = 1) => (h_turn = Other(s.ctxt))
         /\ lock = (\E p \in Procs : pc[p] \in {"cs", "l2"})
         /\ \A p, q \in Procs :
               (p # q) => ~(pc[p] \in {"cs", "l2"} /\ pc[q] \in {"cs", "l2"})

(***************************************************************************)
(* Refinement mapping to Peterson's algorithm                              *)
(***************************************************************************)
pc_translation ==
  [p \in Procs |->
     IF s # top /\ s.ctxt = p
       THEN IF s.val = 2 THEN "a2" ELSE "a3"
       ELSE CASE pc[p] = "l0" -> "a0"
              [] pc[p] = "l1" -> "a1"
              [] pc[p] = "cs" -> "cs"
              [] pc[p] = "l2" -> "a4"]

c_translation == [p \in Procs |-> pc[p] \in {"cs", "l2"}]

(***************************************************************************)
(* Peterson's algorithm P, expressed over the translated variables         *)
(* (pc <- pc_translation, c <- c_translation, turn <- h_turn).             *)
(***************************************************************************)
Ppc   == pc_translation
Pc    == c_translation
Pturn == h_turn

Pvars == <<Ppc, Pc, Pturn>>

PInit == /\ Ppc = [p \in Procs |-> "a0"]
         /\ Pc = [p \in Procs |-> FALSE]
         /\ Pturn \in Procs

Pa0(p) == /\ Ppc[p] = "a0"
          /\ Ppc' = [Ppc EXCEPT ![p] = "a1"]
          /\ Pc' = Pc
          /\ Pturn' = Pturn

Pa1(p) == /\ Ppc[p] = "a1"
          /\ Ppc' = [Ppc EXCEPT ![p] = "a2"]
          /\ Pc' = [Pc EXCEPT ![p] = TRUE]
          /\ Pturn' = Pturn

Pa2(p) == /\ Ppc[p] = "a2"
          /\ Ppc' = [Ppc EXCEPT ![p] = "a3"]
          /\ Pc' = Pc
          /\ Pturn' = Other(p)

Pa3(p) == /\ Ppc[p] = "a3"
          /\ (~Pc[Other(p)]) \/ (Pturn = p)
          /\ Ppc' = [Ppc EXCEPT ![p] = "cs"]
          /\ Pc' = Pc
          /\ Pturn' = Pturn

Pcs(p) == /\ Ppc[p] = "cs"
          /\ Ppc' = [Ppc EXCEPT ![p] = "a4"]
          /\ Pc' = Pc
          /\ Pturn' = Pturn

Pa4(p) == /\ Ppc[p] = "a4"
          /\ Ppc' = [Ppc EXCEPT ![p] = "a0"]
          /\ Pc' = [Pc EXCEPT ![p] = FALSE]
          /\ Pturn' = Pturn

PNext == \E p \in Procs :
           Pa0(p) \/ Pa1(p) \/ Pa2(p) \/ Pa3(p) \/ Pcs(p) \/ Pa4(p)

PSpec == PInit /\ [][PNext]_Pvars

THEOREM SpecHS => Spec
THEOREM SpecHS => PSpec
=============================================================================