------------------------------- MODULE BufferedRAF -------------------------------

EXTENDS Naturals, Sequences

CONSTANTS
  Byte, \* Set of byte values
  MaxDisk, \* Maximum disk size (capacity)
  BufCap,  \* Buffer capacity (number of bytes)
  MaxIO,   \* Maximum size of a single Read/Write call
  Arb      \* Arbitrary symbol not in Byte, representing underspecified content

ASSUME
  /\ MaxDisk \in Nat /\ MaxDisk > 0
  /\ BufCap \in Nat /\ BufCap >= 0
  /\ MaxIO \in Nat
  /\ Arb \notin Byte

(*
  Utility definitions
*)
DiskDomain == 0..(MaxDisk - 1)

Indices(cap) ==
  IF cap \in Nat /\ cap > 0 THEN 0..(cap - 1) ELSE {}

Range(a, b) ==
  { i \in DiskDomain : a <= i /\ i < b }

ActiveIdx(bufStartX, bufEndX) ==
  { j \in Indices(BufCap) : j < (bufEndX - bufStartX) }

ReadSeqFrom(d, start, k) ==
  [ i \in 1..k |-> d[start + i - 1] ]

LogicalDiskState(dirtyX, bufStartX, bufEndX, bufX, diskX, lenX) ==
  [ i \in DiskDomain |->
      IF i < lenX THEN
        IF dirtyX /\ bufStartX <= i /\ i < bufEndX
        THEN bufX[i - bufStartX]
        ELSE diskX[i]
      ELSE diskX[i]
  ]

(*
  Variables
*)
VARIABLES
  pos, len, disk,
  bufStart, bufEnd, buf, dirty,
  ret, op,
  A_pos, A_len, A_disk,
  histOK

Vars == << pos, len, disk, bufStart, bufEnd, buf, dirty, ret, op, A_pos, A_len, A_disk, histOK >>

BufLen == bufEnd - bufStart

LogicalDisk == LogicalDiskState(dirty, bufStart, bufEnd, buf, disk, len)

(*
  Initial state
*)
Init ==
  /\ disk \in [DiskDomain -> (Byte \cup {Arb})]
  /\ len \in 0..MaxDisk
  /\ pos \in 0..len
  /\ bufStart = 0
  /\ bufEnd = 0
  /\ buf \in [Indices(BufCap) -> (Byte \cup {Arb})]
  /\ dirty = FALSE
  /\ ret = "None"
  /\ op = "Idle"
  /\ A_pos = pos
  /\ A_len = len
  /\ A_disk = LogicalDisk
  /\ histOK = TRUE

(*
  Actions
*)
SeekAct ==
  \E newPos \in 0..len:
    /\ op' = "Seek"
    /\ pos' = newPos
    /\ ret' = "OK"
    /\ histOK' = TRUE
    /\ A_pos' = newPos
    /\ A_len' = len
    /\ A_disk' = A_disk
    /\ UNCHANGED << len, disk, bufStart, bufEnd, buf, dirty >>

ReadAct ==
  \E n \in 0..MaxIO:
    LET k == IF n <= (len - pos) THEN n ELSE (len - pos) IN
    /\ op' = "Read"
    /\ ret' = ReadSeqFrom(LogicalDisk, pos, k)
    /\ pos' = pos + k
    /\ A_pos' = pos + k
    /\ A_len' = len
    /\ A_disk' = A_disk
    /\ histOK' = TRUE
    /\ UNCHANGED << len, disk, bufStart, bufEnd, buf, dirty >>

WriteAct ==
  \E b \in Seq(Byte):
    /\ Len(b) <= MaxIO
    /\ pos + Len(b) <= MaxDisk
    \E newStart \in 0..MaxDisk:
      \E newEnd \in newStart..MaxDisk:
        LET winLen == newEnd - newStart IN
        /\ winLen <= BufCap
        LET
          disk1 ==
            [ i \in DiskDomain |->
                IF dirty /\ bufStart <= i /\ i < bufEnd
                THEN buf[i - bufStart]
                ELSE disk[i]
            ]
          writeRange == { i \in DiskDomain : i >= pos /\ i < pos + Len(b) }
          inWindow(i) == newStart <= i /\ i < newEnd
          disk2 ==
            [ i \in DiskDomain |->
                IF (i \in writeRange) /\ ~inWindow(i)
                THEN b[i - pos + 1]
                ELSE disk1[i]
            ]
          bufNew ==
            [ j \in Indices(BufCap) |->
                IF j < winLen THEN
                  LET i == newStart + j IN
                    IF i \in writeRange
                    THEN b[i - pos + 1]
                    ELSE disk2[i]
                ELSE buf[j]
            ]
          lenNew == IF len >= pos + Len(b) THEN len ELSE pos + Len(b)
          dirtyNew == \E i \in writeRange : inWindow(i)
          posNew == pos + Len(b)
        IN
        /\ op' = "Write"
        /\ disk' = disk2
        /\ bufStart' = newStart
        /\ bufEnd' = newEnd
        /\ buf' = bufNew
        /\ len' = lenNew
        /\ pos' = posNew
        /\ dirty' = dirtyNew
        /\ ret' = "OK"
        /\ histOK' = TRUE
        /\ A_pos' = posNew
        /\ A_len' = lenNew
        /\ A_disk' = LogicalDiskState(dirtyNew, newStart, newEnd, bufNew, disk2, lenNew)

FlushAct ==
  LET diskFlushed ==
        [ i \in DiskDomain |->
            IF dirty /\ bufStart <= i /\ i < bufEnd
            THEN buf[i - bufStart]
            ELSE disk[i]
        ]
  IN
  /\ op' = "Flush"
  /\ disk' = diskFlushed
  /\ dirty' = FALSE
  /\ ret' = "OK"
  /\ A_pos' = pos
  /\ A_len' = len
  /\ A_disk' = LogicalDiskState(FALSE, bufStart, bufEnd, buf, diskFlushed, len)
  /\ histOK' = TRUE
  /\ UNCHANGED << pos, len, bufStart, bufEnd, buf >>

SetLengthAct ==
  \E newLen \in 0..MaxDisk:
    LET
      disk1 ==
        [ i \in DiskDomain |->
            IF dirty /\ bufStart <= i /\ i < bufEnd
            THEN buf[i - bufStart]
            ELSE disk[i]
        ]
      disk2 ==
        [ i \in DiskDomain |->
            IF newLen > len /\ len <= i /\ i < newLen
            THEN Arb
            ELSE disk1[i]
        ]
      newStart == IF bufStart <= newLen THEN bufStart ELSE newLen
      newEnd == IF bufEnd <= newLen THEN bufEnd ELSE newLen
      winLen == newEnd - newStart
      bufNew ==
        [ j \in Indices(BufCap) |->
            IF j < winLen THEN disk2[newStart + j] ELSE buf[j]
        ]
      posNew == IF pos <= newLen THEN pos ELSE newLen
    IN
    /\ op' = "SetLength"
    /\ disk' = disk2
    /\ len' = newLen
    /\ pos' = posNew
    /\ bufStart' = newStart
    /\ bufEnd' = newEnd
    /\ buf' = bufNew
    /\ dirty' = FALSE
    /\ ret' = "OK"
    /\ histOK' = TRUE
    /\ A_pos' = posNew
    /\ A_len' = newLen
    /\ A_disk' = LogicalDiskState(FALSE, newStart, newEnd, bufNew, disk2, newLen)

Next ==
  SeekAct \/ ReadAct \/ WriteAct \/ FlushAct \/ SetLengthAct

Spec ==
  Init /\ [][Next]_Vars

(*
  Safety invariants
*)
TypeInv ==
  /\ disk \in [DiskDomain -> (Byte \cup {Arb})]
  /\ len \in 0..MaxDisk
  /\ pos \in 0..len
  /\ bufStart \in 0..MaxDisk
  /\ bufEnd \in 0..MaxDisk
  /\ bufEnd >= bufStart
  /\ bufEnd - bufStart <= BufCap
  /\ buf \in [Indices(BufCap) -> (Byte \cup {Arb})]
  /\ dirty \in BOOLEAN
  /\ ret \in Seq(Byte) \cup {"OK", "None"}
  /\ op \in {"Idle", "Seek", "Read", "Write", "Flush", "SetLength"}
  /\ A_pos \in 0..MaxDisk
  /\ A_len \in 0..MaxDisk
  /\ A_disk \in [DiskDomain -> (Byte \cup {Arb})]

BufferInv ==
  /\ bufEnd <= MaxDisk
  /\ (~dirty) => \A j \in ActiveIdx(bufStart, bufEnd) : buf[j] = disk[bufStart + j]

AbstractMappingInv ==
  /\ A_pos = pos
  /\ A_len = len
  /\ A_disk = LogicalDisk

LogicalByteInv ==
  \A i \in { k \in DiskDomain : k < len } : LogicalDisk[i] \in (Byte \cup {Arb})

Inv == TypeInv /\ BufferInv /\ AbstractMappingInv /\ LogicalByteInv

=============================================================================