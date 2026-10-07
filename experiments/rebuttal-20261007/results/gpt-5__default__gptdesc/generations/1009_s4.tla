------------------------------ MODULE BufferedRandomAccessFile ------------------------------

EXTENDS Naturals, Integers, Sequences

CONSTANTS
  DataVals,
  ArbitrarySymbol,
  MaxLen,
  BufCap,
  MaxIO

ASSUME
  /\ ArbitrarySymbol \notin DataVals
  /\ MaxLen \in Nat
  /\ BufCap \in Nat \ {0}
  /\ MaxIO \in Nat

(*
  Utility sets and operators
*)
Values == DataVals \cup {ArbitrarySymbol}

Index(n) == IF n = 0 THEN {} ELSE 0..(n-1)

Min(a, b) == IF a <= b THEN a ELSE b
Max2(a, b) == IF a >= b THEN a ELSE b

Align(p) == (p \div BufCap) * BufCap

SubSeqFromFunc(f, start, count) ==
  [ i \in (IF count = 0 THEN {} ELSE 1..count) |-> f[start + (i - 1)] ]

MaxSet(S) == CHOOSE m \in S : \A x \in S : m >= x

(*
  State variables
*)
VARIABLES
  pos,            \* current logical file position (cursor)
  len,            \* current logical file length
  diskLen,        \* on-disk file length
  Disk,           \* on-disk contents: function Index(diskLen) -> Values
  bufStart,       \* file offset corresponding to buf[0]
  BufValidLen,    \* number of valid bytes in buffer window
  buf,            \* in-memory buffer: function Index(BufCap) -> Values
  dirtySet,       \* subset of 0..BufValidLen-1 indicating dirty bytes in buffer
  lastRead,       \* result of the most recent read operation (sequence of Values)
  opKind,         \* tag of the last operation performed
  opArg,          \* argument of the last operation (type depends on opKind)
  opRet,          \* return/result of the last operation (if any)
  prevAbsFile,    \* abstract file view of the state before the last step
  prevAbsLen,     \* abstract length before the last step
  prevAbsPos      \* abstract position before the last step

vars == << pos, len, diskLen, Disk, bufStart, BufValidLen, buf, dirtySet, lastRead, opKind, opArg, opRet, prevAbsFile, prevAbsLen, prevAbsPos >>

Tags == {"Init", "Seek", "Read", "Write", "Flush", "SetLength"}
Null == "None"

(*
  Concrete helpers over current state
*)
BaseVal(j) == IF j < diskLen THEN Disk[j] ELSE ArbitrarySymbol

InWindow(j) == /\ j >= bufStart /\ j < bufStart + BufValidLen
BufIdx(j) == j - bufStart

AbsFunc ==
  [ j \in Index(len) |->
      IF InWindow(j) /\ BufIdx(j) \in dirtySet
        THEN buf[BufIdx(j)]
        ELSE BaseVal(j)
  ]

(*
  Type and structural invariants
*)
TypeOK ==
  /\ len \in 0..MaxLen
  /\ pos \in 0..len
  /\ diskLen \in 0..MaxLen
  /\ Disk \in [Index(diskLen) -> Values]
  /\ bufStart \in 0..MaxLen
  /\ BufValidLen \in 0..BufCap
  /\ bufStart + BufValidLen <= len
  /\ buf \in [Index(BufCap) -> Values]
  /\ dirtySet \subseteq Index(BufValidLen)
  /\ lastRead \in Seq(Values)
  /\ Len(lastRead) <= MaxIO
  /\ opKind \in Tags
  /\ prevAbsLen \in 0..MaxLen
  /\ prevAbsPos \in 0..prevAbsLen
  /\ prevAbsFile \in [Index(prevAbsLen) -> Values]

GoodBufInv ==
  /\ bufStart + BufValidLen <= len
  /\ \A i \in Index(BufValidLen) :
        IF i \in dirtySet
          THEN TRUE
          ELSE buf[i] = BaseVal(bufStart + i)

(*
  Abstract-step-by-step refinement check:
  Each concrete step labeled by opKind must correspond to the abstract RAF semantics
  under the refinement mapping AbsFunc/len/pos.
*)
AbsStepOk ==
  IF opKind = "Init" THEN TRUE
  ELSE
    CASE
      opKind = "Seek" ->
        /\ len = prevAbsLen
        /\ AbsFunc = prevAbsFile
        /\ pos = Min(opArg, prevAbsLen)
    [] opKind = "Read" ->
        LET n == opArg
            bytes == Min(n, prevAbsLen - prevAbsPos)
            ret == SubSeqFromFunc(prevAbsFile, prevAbsPos, bytes)
        IN  /\ opRet = ret
            /\ len = prevAbsLen
            /\ AbsFunc = prevAbsFile
            /\ pos = prevAbsPos + bytes
    [] opKind = "Write" ->
        LET w == opArg
            m == Len(w)
            len1 == Max2(prevAbsLen, prevAbsPos + m)
            file1 ==
              [ j \in Index(len1) |->
                  IF j >= prevAbsPos /\ j < prevAbsPos + m
                    THEN w[1 + (j - prevAbsPos)]
                    ELSE IF j < prevAbsLen THEN prevAbsFile[j] ELSE ArbitrarySymbol
              ]
        IN  /\ len = len1
            /\ pos = prevAbsPos + m
            /\ AbsFunc = file1
    [] opKind = "Flush" ->
        /\ len = prevAbsLen
        /\ AbsFunc = prevAbsFile
        /\ pos = prevAbsPos
    [] opKind = "SetLength" ->
        LET newL == opArg
            file1 ==
              [ j \in Index(newL) |->
                  IF j < prevAbsLen THEN prevAbsFile[j] ELSE ArbitrarySymbol
              ]
        IN  /\ len = newL
            /\ pos = Min(prevAbsPos, newL)
            /\ AbsFunc = file1
    [] OTHER -> FALSE

(*
  Initialization
*)
Init ==
  /\ len = 0
  /\ pos = 0
  /\ diskLen = 0
  /\ Disk = [ i \in Index(diskLen) |-> ArbitrarySymbol ]
  /\ bufStart = 0
  /\ BufValidLen = 0
  /\ buf \in [ Index(BufCap) -> Values ]
  /\ dirtySet = {}
  /\ lastRead = <<>>
  /\ opKind = "Init"
  /\ opArg = Null
  /\ opRet = Null
  /\ prevAbsFile = AbsFunc
  /\ prevAbsLen = len
  /\ prevAbsPos = pos

(*
  Operations
*)
SeekOp ==
  \E newPos \in 0..MaxLen :
    /\ prevAbsFile' = AbsFunc
    /\ prevAbsLen' = len
    /\ prevAbsPos' = pos
    /\ pos' = Min(newPos, len)
    /\ UNCHANGED << len, diskLen, Disk, bufStart, BufValidLen, buf, dirtySet, lastRead >>
    /\ opKind' = "Seek"
    /\ opArg' = newPos
    /\ opRet' = Null

ReadOp ==
  \E n \in 0..MaxIO :
    LET bytes == Min(n, len - pos)
        ret == SubSeqFromFunc(AbsFunc, pos, bytes)
    IN
    /\ prevAbsFile' = AbsFunc
    /\ prevAbsLen' = len
    /\ prevAbsPos' = pos
    /\ pos' = pos + bytes
    /\ lastRead' = ret
    /\ UNCHANGED << len, diskLen, Disk, bufStart, BufValidLen, buf, dirtySet >>
    /\ opKind' = "Read"
    /\ opArg' = n
    /\ opRet' = ret

WriteOp ==
  \E w \in Seq(DataVals) :
    /\ Len(w) <= MaxIO
    /\ LET m == Len(w)
           newLen == Max2(len, pos + m)
           newBufStart == Align(pos)
           newValid == Min(BufCap, newLen - newBufStart)
           writeSetIdx == { i \in Index(newValid) :
                               LET j == newBufStart + i IN j >= pos /\ j < pos + m }
           bufNew ==
             [ i \in Index(BufCap) |->
                 IF i < newValid THEN
                   IF i \in writeSetIdx
                     THEN w[1 + (newBufStart + i) - pos]
                     ELSE (IF newBufStart + i < diskLen THEN Disk[newBufStart + i] ELSE ArbitrarySymbol)
                 ELSE buf[i]
             ]
       IN
       /\ prevAbsFile' = AbsFunc
       /\ prevAbsLen' = len
       /\ prevAbsPos' = pos
       /\ len' = newLen
       /\ pos' = pos + m
       /\ diskLen' = diskLen
       /\ Disk' = Disk
       /\ bufStart' = newBufStart
       /\ BufValidLen' = newValid
       /\ buf' = bufNew
       /\ dirtySet' = writeSetIdx
       /\ UNCHANGED lastRead
       /\ opKind' = "Write"
       /\ opArg' = w
       /\ opRet' = m

FlushOp ==
  LET writeIdxJ == { bufStart + i : i \in dirtySet }
      newDL == Max2(diskLen,
                    IF writeIdxJ = {} THEN diskLen ELSE 1 + MaxSet(writeIdxJ))
      DiskExt ==
        [ j \in Index(newDL) |->
            IF j < diskLen THEN Disk[j] ELSE ArbitrarySymbol
        ]
      DiskNew ==
        [ j \in Index(newDL) |->
            IF j \in writeIdxJ THEN buf[j - bufStart] ELSE DiskExt[j]
        ]
  IN
  /\ prevAbsFile' = AbsFunc
  /\ prevAbsLen' = len
  /\ prevAbsPos' = pos
  /\ diskLen' = newDL
  /\ Disk' = DiskNew
  /\ dirtySet' = {}
  /\ UNCHANGED << pos, len, bufStart, BufValidLen, buf, lastRead >>
  /\ opKind' = "Flush"
  /\ opArg' = Null
  /\ opRet' = Null

SetLengthOp ==
  \E newL \in 0..MaxLen :
    LET newValid == (IF newL <= bufStart THEN 0 ELSE Min(BufCap, newL - bufStart))
        bufAdj ==
          [ i \in Index(BufCap) |->
              IF i < newValid THEN
                IF i \in dirtySet
                  THEN buf[i]
                  ELSE (IF bufStart + i < diskLen THEN Disk[bufStart + i] ELSE ArbitrarySymbol)
              ELSE buf[i]
          ]
        dirtyAdj == { i \in dirtySet : i < newValid }
    IN
    /\ prevAbsFile' = AbsFunc
    /\ prevAbsLen' = len
    /\ prevAbsPos' = pos
    /\ len' = newL
    /\ pos' = Min(pos, newL)
    /\ buf' = bufAdj
    /\ BufValidLen' = newValid
    /\ dirtySet' = dirtyAdj
    /\ UNCHANGED << diskLen, Disk, bufStart, lastRead >>
    /\ opKind' = "SetLength"
    /\ opArg' = newL
    /\ opRet' = Null

Next ==
  SeekOp \/ ReadOp \/ WriteOp \/ FlushOp \/ SetLengthOp

Spec ==
  Init /\ [][Next]_vars

(*
  Safety properties (to be checked as invariants)
*)
InvType == TypeOK
InvBuf == GoodBufInv
RefinesByStep == AbsStepOk

=============================================================================