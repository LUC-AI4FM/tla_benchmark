------------------------------ MODULE RollingDeploy ------------------------------

EXTENDS TLC, Naturals

(*
This PlusCal-style description (informal, not translated here) models a rolling
deployment coordinated with a load balancer:

fair process (Server \in Servers)
  begin
    SWait:
      await req[self] /\ self \notin lb /\ status[self] = "idle";
      status[self] := "updating";
    SFinish:
      status[self] := "updated";
      req[self] := FALSE;
    SDone:
      skip;
  end process;

fair process Coordinator
  variables cur;
  begin
    CNext:
      if \E s \in Servers: ~done[s] /\ s \in lb then
        with s \in {x \in Servers: ~done[x] /\ x \in lb} do
          cur := s;
        end with;
        lb := lb \ {cur};
        req[cur] := TRUE;
        goto CWait;
      else
        goto CDone;
      end if;
    CWait:
      await status[cur] = "updated";
      lb := lb \cup {cur};
      done[cur] := TRUE;
      goto CNext;
    CDone:
      skip;
  end process;

The temporal specification checks Init, Next, and weak fairness for both
the per-server update process and the coordinator. Termination is defined
as eventual completion of all processes.
*)

CONSTANTS

Servers == {"s1", "s2", "s3"}

ProcIds == Servers \cup {"coord"}

\* State variables
VARIABLES lb, status, req, done, pc, cur

vars == << lb, status, req, done, pc, cur >>

StatusVals == {"idle", "updating", "updated"}

Init ==
  /\ lb = Servers
  /\ status = [s \in Servers |-> "idle"]
  /\ req = [s \in Servers |-> FALSE]
  /\ done = [s \in Servers |-> FALSE]
  /\ pc = [id \in ProcIds |-> IF id \in Servers THEN "SWait" ELSE "CNext"]
  /\ cur = [id \in ProcIds |-> CHOOSE s \in Servers: TRUE]

\* Server actions
SStart(p) ==
  /\ p \in Servers
  /\ pc[p] = "SWait"
  /\ req[p]
  /\ p \notin lb
  /\ status[p] = "idle"
  /\ status' = [status EXCEPT ![p] = "updating"]
  /\ pc' = [pc EXCEPT ![p] = "SFinish"]
  /\ UNCHANGED << lb, req, done, cur >>

SFinish(p) ==
  /\ p \in Servers
  /\ pc[p] = "SFinish"
  /\ status' = [status EXCEPT ![p] = "updated"]
  /\ req' = [req EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "SDone"]
  /\ UNCHANGED << lb, done, cur >>

\* Coordinator actions
CNext ==
  /\ pc["coord"] = "CNext"
  /\ ( \E s \in Servers: ~done[s] /\ s \in lb )
  /\ \E s \in Servers:
        /\ ~done[s] /\ s \in lb
        /\ lb' = lb \ {s}
        /\ req' = [req EXCEPT ![s] = TRUE]
        /\ cur' = [cur EXCEPT !["coord"] = s]
        /\ pc' = [pc EXCEPT !["coord"] = "CWait"]
        /\ UNCHANGED << status, done >>

CWait ==
  /\ pc["coord"] = "CWait"
  /\ LET s == cur["coord"] IN
       /\ status[s] = "updated"
       /\ lb' = lb \cup {s}
       /\ done' = [done EXCEPT ![s] = TRUE]
       /\ pc' = [ pc EXCEPT
                    !["coord"] = IF \A x \in Servers: done[x] THEN "CDone" ELSE "CNext"
                 ]
       /\ UNCHANGED << status, req, cur >>

\* Disjunction of all step actions
Next ==
  \/ \E p \in Servers: SStart(p)
  \/ \E p \in Servers: SFinish(p)
  \/ CNext
  \/ CWait

\* Per-process action groups for fairness
ServerProc(p) == SStart(p) \/ SFinish(p)
CoordProc == CNext \/ CWait

\* Temporal specification: Init, Next with stuttering, and weak fairness
Spec ==
  Init
  /\ [][Next]_vars
  /\ (\A p \in Servers: WF_vars(ServerProc(p)))
  /\ WF_vars(CoordProc)

\* Termination: eventually all processes reach their done labels
Termination ==
  <>[] ( (\A p \in Servers: pc[p] = "SDone") /\ pc["coord"] = "CDone" )

=============================================================================