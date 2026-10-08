------------------------------- MODULE KeyValueStore -------------------------------

CONSTANTS Keys, Vals, MISSING, NIL

VARIABLES op, args, ret, dict, state

ASSUME \A k \in Keys : k \notin Vals /\ k /= MISSING /\ k /= NIL
ASSUME \A v \in Vals : v /= MISSING /\ v /= NIL

Init == 
  /\ op = NIL
  /\ args = NIL
  /\ ret = NIL
  /\ dict = [k \in Keys |-> MISSING]
  /\ state = "ready"

Next ==
  \/ /\ state = "ready"
     /\ op = NIL
     /\ args = NIL
     /\ \/ /\ op' \in {"get", "insert", "update", "delete"}
        /\ args' \in (Keys \X Vals) \cup Keys
        /\ ret' = NIL
        /\ dict' = dict
        /\ state' = "working"
  \/ /\ state = "working"
     /\ op /= NIL
     /\ args /= NIL
     /\ \/ /\ op = "get"
        /\ LET key == Fst(args)
           val == dict[key]
         IN /\ ret' \in Vals \cup {MISSING}
            /\ ret' = val
            /\ dict' = dict
            /\ state' = "ready"
     \/ /\ op = "insert"
        /\ LET key == Fst(args)
           val == Snd(args)
         IN /\ ret' \in {"ok", "error"}
            /\ (dict[key] = MISSING => dict' = [dict EXCEPT ![key] = val] /\ ret' = "ok")
            /\ (dict[key] /= MISSING => dict' = dict /\ ret' = "error")
            /\ state' = "ready"
     \/ /\ op = "update"
        /\ LET key == Fst(args)
           val == Snd(args)
         IN /\ ret' \in {"ok", "error"}
            /\ (dict[key] /= MISSING => dict' = [dict EXCEPT ![key] = val] /\ ret' = "ok")
            /\ (dict[key] = MISSING => dict' = dict /\ ret' = "error")
            /\ state' = "ready"
     \/ /\ op = "delete"
        /\ LET key == args
         IN /\ ret' = "ok"
            /\ dict' = [dict EXCEPT ![key] = MISSING]
            /\ state' = "ready"

TypeOK ==
  /\ op \in {"get", "insert", "update", "delete"} \cup {NIL}
  /\ (op = NIL => args = NIL)
  /\ (op /= NIL => args \in (Keys \X Vals) \cup Keys)
  /\ ret \in Vals \cup {MISSING, "ok", "error", NIL}
  /\ dict \in [Keys -> Vals \cup {MISSING}]
  /\ state \in {"ready", "working"}

Spec == Init /\ [][Next]_<<op, args, ret, dict, state>> \/ WF_next(<<op>>, {"delete"})

WF_next(vars, ops) ==
  \A op \in ops : \E i \in 1..Len(vars) :
    \A s \in StateSuchThat(vars, i - 1) :
      \E s' \in StateSuchThat(vars, i) :
        /\ vars[i] = op
        /\ NextEnabled(s)
        /\ [][Next]_vars => <s, s'> \in Next

StateSuchThat(vars, n) ==
  {s \in [op \in {"get", "insert", "update", "delete"} \cup {NIL},
          args \in (Keys \X Vals) \cup Keys,
          ret \in Vals \cup {MISSING, "ok", "error", NIL},
          dict \in [Keys -> Vals \cup {MISSING}],
          state \in {"ready", "working"}] :
     /\ n = 0 \/ vars[n] = s[op]
     /\ TypeOK}

NextEnabled(s) ==
  /\ s[state] = "ready"
  /\ s[op] = NIL
  /\ s[args] = NIL

=============================================================================