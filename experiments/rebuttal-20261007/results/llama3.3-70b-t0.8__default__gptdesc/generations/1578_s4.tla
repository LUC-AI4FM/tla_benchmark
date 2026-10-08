```tla
MODULE DequeSpec

EXTENDS Integers, TLC

CONSTANTS
  AddrSet,
  ValSet,
  NumProcs

VARIABLES
  mem,
  leftHat,
  rightHat,
  freelist,
  pc,
  valBag,
  localVars

Init ==
  /\ mem = [a \in AddrSet |-> [node|-> NULL, next|-> NULL, prev|-> NULL]]
  /\ leftHat = NULL
  /\ rightHat = NULL
  /\ freelist = AddrSet
  /\ pc = [i \in 1..NumProcs |-> "T1"]
  /\ valBag = {}
  /\ localVars = [i \in 1..NumProcs |-> <<NULL, NULL>>]

Next ==
  \/ \E i \in 1..NumProcs :
      IF pc[i] = "T1"
      THEN
        /\ pc' = [pc EXCEPT ![i] = "T2"]
        /\ localVars' = [localVars EXCEPT ![i] = <<NULL, NULL>>]
        /\ valBag' = valBag
        /\ mem' = mem
        /\ leftHat' = leftHat
        /\ rightHat' = rightHat
        /\ freelist' = freelist
      ELSEIF pc[i] = "T2"
      THEN
        /\ WITH v \in ValSet :
              /\ pc' = [pc EXCEPT ![i] = "PushLeft1"]
              /\ localVars' = [localVars EXCEPT ![i] = <<v, NULL>>]
              /\ valBag' = valBag \cup {v}
              /\ mem' = mem
              /\ leftHat' = leftHat
              /\ rightHat' = rightHat
              /\ freelist' = freelist
        \/ WITH v \in ValSet :
              /\ pc' = [pc EXCEPT ![i] = "PushRight1"]
              /\ localVars' = [localVars EXCEPT ![i] = <<v, NULL>>]
              /\ valBag' = valBag \cup {v}
              /\ mem' = mem
              /\ leftHat' = leftHat
              /\ rightHat' = rightHat
              /\ freelist' = freelist
        \/ WITH v \in ValSet :
              /\ pc' = [pc EXCEPT ![i] = "PopLeft1"]
              /\ localVars' = [localVars EXCEPT ![i] = <<NULL, v>>]
              /\ valBag' = valBag
              /\ mem' = mem
              /\ leftHat' = leftHat
              /\ rightHat' = rightHat
              /\ freelist' = freelist
        \/ WITH v \in ValSet :
              /\ pc' = [pc EXCEPT ![i] = "PopRight1"]
              /\ localVars' = [localVars EXCEPT ![i] = <<NULL, v>>]
              /\ valBag' = valBag
              /\ mem' = mem
              /\ leftHat' = leftHat
              /\ rightHat' = rightHat
              /\ freelist' = freelist
      ELSEIF pc[i] = "PushLeft1"
      THEN
        /\ WITH a \in freelist :
              /\ pc' = [pc EXCEPT ![i] = "PushLeft2"]
              /\ localVars' = [localVars EXCEPT ![i] = <<localVars[i][1], a>>]
              /\ valBag' = valBag
              /\ mem' = [mem EXCEPT ![a] = [node|-> localVars[i][1], next|-> NULL, prev|-> NULL]]
              /\ leftHat' = leftHat
              /\ rightHat' = rightHat
              /\ freelist' = freelist \ {a}
      ELSEIF pc[i] = "PushRight1"
      THEN
        /\ WITH a \in freelist :
              /\ pc' = [pc EXCEPT ![i] = "PushRight2"]
              /\ localVars' = [localVars EXCEPT ![i] = <<localVars[i][1], a>>]
              /\ valBag' = valBag
              /\ mem' = [mem EXCEPT ![a] = [node|-> localVars[i][1], next|-> NULL, prev|-> NULL]]
              /\ leftHat' = leftHat
              /\ rightHat' = rightHat
              /\ freelist' = freelist \ {a}
      ELSEIF pc[i] = "PopLeft1"
      THEN
        /\ IF leftHat # NULL
            THEN
              /\ WITH a = leftHat :
                    /\ pc' = [pc EXCEPT ![i] = "PopLeft2"]
                    /\ localVars' = [localVars EXCEPT ![i] = <<mem[a].node, a>>]
                    /\ valBag' = valBag \ {mem[a].node}
                    /\ mem' = mem
                    /\ leftHat' = leftHat
                    /\ rightHat' = rightHat
                    /\ freelist' = freelist \cup {a}
            ELSE
              /\ pc' = [pc EXCEPT ![i] = "T1"]
              /\ localVars' = [localVars EXCEPT ![i] = <<NULL, NULL>>]
              /\ valBag' = valBag
              /\ mem' = mem
              /\ leftHat' = leftHat
              /\ rightHat' = rightHat
              /\ freelist' = freelist
      ELSEIF pc[i] = "PopRight1"
      THEN
        /\ IF rightHat # NULL
            THEN
              /\ WITH a = rightHat :
                    /\ pc' = [pc EXCEPT ![i] = "PopRight2"]
                    /\ localVars' = [localVars EXCEPT ![i] = <<mem[a].node, a>>]
                    /\ valBag' = valBag \ {mem[a].node}
                    /\ mem' = mem
                    /\ leftHat' = leftHat
                    /\ rightHat' = rightHat
                    /\ freelist' = freelist \cup {a}
            ELSE
              /\ pc' = [pc EXCEPT ![i] = "T1"]
              /\ localVars' = [localVars EXCEPT ![i] = <<NULL, NULL>>]
              /\ valBag' = valBag
              /\ mem' = mem
              /\ leftHat' = leftHat
              /\ rightHat' = rightHat
              /\ freelist' = freelist

Spec ==
  Init /\ [][Next]_<<mem, leftHat, rightHat, freelist, pc, valBag, localVars>>

THEOREM Spec => []<>(pc[1] = "T1")
```