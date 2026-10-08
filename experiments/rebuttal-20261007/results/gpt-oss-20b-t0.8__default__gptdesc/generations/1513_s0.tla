MODULE SimpleStateMachine
CONSTANTS Node, Red, Green

Color == {Red, Green}

VARIABLES activity, colors, tokenPos, tokenCol

ActivityType(a) == a ∈ [Node -> BOOLEAN]
ColorsType(c)   == c ∈ [Node -> Color]
TokenPosType(tp)== tp ∈ Node
TokenColType(tc)== tc ∈ Color

Init ==
  /\ ActivityType(activity)
  /\ ColorsType(colors)
  /\ TokenPosType(tokenPos)
  /\ TokenColType(tokenCol)

Next ==
  /\ ActivityType(activity')
  /\ ColorsType(colors')
  /\ TokenPosType(tokenPos')
  /\ TokenColType(tokenCol')

Spec == Init /\ [] [][Next]_vars

END MODULE