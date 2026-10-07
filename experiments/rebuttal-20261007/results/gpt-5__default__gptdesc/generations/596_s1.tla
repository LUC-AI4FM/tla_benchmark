---- MODULE OneVarWF ----
EXTENDS Naturals

CONSTANTS CEXTrace

VARIABLES x

Init ==
  x = 0

Next ==
  \/ /\ x = 0
     /\ x' \in {1, 2}
  \/ /\ x # 0
     /\ x' = 0

Spec ==
  Init /\ [][Next]_x /\ WF_x(Next)

(*
 Safety invariants
*)
TypeInv ==
  x \in {0, 1, 2}

NonZeroIsOneOrTwo ==
  (x # 0) => x \in {1, 2}

(*
 Liveness properties
*)
EventuallyStabilizeAwayFrom1 ==
  <>[] (x # 1)

EventuallyStabilizeAwayFrom2 ==
  <>[] (x # 2)

EventualRepeatedReturnToZero ==
  []<> (x = 0)

NegEventuallyStabilizeAwayFrom1 ==
  ~EventuallyStabilizeAwayFrom1

(*
 A postcondition that checks a TLC-generated counterexample trace
 encoded as records, tuples, and sets.
 CEXTrace is a CONSTANT expected to be supplied by the TLC model.
*)
Post ==
  LET expected ==
        [ states |-> <<
            [ x |-> 0 ],
            [ x |-> 1 ],
            [ x |-> 0 ],
            [ x |-> 2 ],
            [ x |-> 0 ]
          >>,
          steps |-> { <<0, 1>>, <<1, 0>>, <<0, 2>>, <<2, 0>> },
          meta  |-> { [ len |-> 5 ],
                      [ vars |-> {"x"} ],
                      [ tag  |-> "cex" ] }
        ]
  IN CEXTrace = expected

====