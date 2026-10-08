MODULE RandomAccessBufferedFile
EXTENDS Naturals, Sequences, TLC

CONSTANTS BufSize, MaxFileSize, ArbitrarySymbol

VARIABLES buf, pos, mem, disk, len

vars == <<buf, pos, mem, disk, len>>

Init ==
  /\ buf = [i \in 1..BufSize |-> ArbitrarySymbol]
  /\ pos = 0
  /\ mem = [i \in 1..MaxFileSize |-> ArbitrarySymbol]
  /\ disk = mem
  /\ len = 0

Seek(n) ==
  /\ n >= 0 /\ n <= len
  /\ pos' = n
  /\ UNCHANGED <<buf, mem, disk, len>>

ReadOp ==
  /\ \E k \in Nat : (pos + k) <= len
  /\ UNCHANGED vars

Write(data) ==
  /\ data \in Seq(Nat)
  /\ LET k == Len(data) IN
     /\ (pos + k) <= MaxFileSize
     /\ buf' = [i \in 1..BufSize |-> IF i <= k THEN data[i] ELSE buf[i]]
     /\ mem' = [mem EXCEPT ![pos+i-1] = data[i] : i \in 1..k]
     /\ len' = Max(len, pos + k)
     /\ UNCHANGED <<disk>>

Flush ==
  /\ disk' = buf
  /\ UNCHANGED <<buf, pos, mem, len>>

SetLengthOp ==
  /\ \E newLen \in Nat : (newLen >= 0) /\ (newLen <= MaxFileSize)
  /\ LET oldLen == len IN
     /\ IF newLen < oldLen THEN
          disk' = [disk EXCEPT ![i] = ArbitrarySymbol : i \in newLen+1..oldLen]
        ELSE
          disk' = [disk EXCEPT ![i] = ArbitrarySymbol : i \in oldLen+1..newLen]
     /\ len' = newLen
  /\ UNCHANGED <<buf, pos, mem>>

Next ==
  \/ Seek(n)
  \/ ReadOp
  \/ Write(data)
  \/ Flush
  \/ SetLengthOp

Spec ==
  Init /\ [][Next]_vars

SafetyInvariants ==
  \A i \in 1..len : mem[i] = disk[i]
    /\ pos <= len

End MODULE