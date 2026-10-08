------------------------------ MODULE LockHS ------------------------------
EXTENDS Lock, Stuttering

VARIABLES h_turn, s

Proc == {0, 1}

varsHS == << pc, flag, turn, c, h_turn, s >>

InitHS ==
  /\ Init
  /\ h_turn = 1
  /\ s = top

(*
  All non-l1 steps proceed only when there is no active stutter and
  leave the auxiliary variables unchanged.
*)
l0HS(p) ==
  /\ s = top
  /\ l0(p)
  /\ h_turn' = h_turn
  /\ s' = s

csHS(p) ==
  /\ s = top
  /\ cs(p)
  /\ h_turn' = h_turn
  /\ s' = s

l2HS(p) ==
  /\ s = top
  /\ l2(p)
  /\ h_turn' = h_turn
  /\ s' = s

(*
  Wrap the base l1 step with two stuttering steps.
  - First disjunct performs the base l1 step and begins stuttering.
  - Second disjunct is a pure stutter that records the history h_turn.
  - Third disjunct completes the stutter cycle.
*)
l1HS(p) ==
  \/
    /\ s = top
    /\ l1(p)
    /\ PostStutter(s, s')
    /\ s' = "pre"
    /\ h_turn' = h_turn
  \/
    /\ s = "pre"
    /\ PostStutter(s, s')
    /\ s' = "post"
    /\ UNCHANGED << pc, flag, turn, c >>
    /\ h_turn' = p
  \/
    /\ s = "post"
    /\ PostStutter(s, s')
    /\ s' = top
    /\ UNCHANGED << pc, flag, turn, c >>
    /\ h_turn' = h_turn

NextHS ==
  \E p \in Proc:
      l0HS(p) \/ l1HS(p) \/ csHS(p) \/ l2HS(p)

SpecHS ==
  InitHS /\ [][NextHS]_varsHS

(*
  Simple refinement-mapping helpers (not required by the model, but
  useful to document correspondence with Peterson).
*)
pc_translation(pcMap) ==
  [ p \in Proc |->
      CASE pcMap[p] = "l0" -> "try"
         [] pcMap[p] = "l1" -> "enter"
         [] pcMap[p] = "cs" -> "cs"
         [] pcMap[p] = "l2" -> "exit"
  ]

c_translation(cMap) == cMap

TypeOKHS ==
  /\ TypeOK
  /\ h_turn \in Proc
  /\ s \in SVals

(*
  Additional consistency conditions between the stuttering state and
  the lock control state.
*)
InvHS ==
  /\ s \in SVals
  /\ h_turn \in Proc
  /\ (s # top) => /\ pc[0] # "cs"
                 /\ pc[1] # "cs"

(*
  Mutual exclusion invariant is inherited from Lock as LockInv.
  The base safety property Spec is inherited from Lock as Spec.
*)

(*
  Instantiate a Peterson-specification module and expose its property
  as PSpec. This stands for the target property used in refinement.
*)
INSTANCE P

PSpec == P!PSpec

=============================================================================