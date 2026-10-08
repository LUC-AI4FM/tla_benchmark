---- MODULE BufferedRandomAccessFile ----
EXTENDS Naturals

CONSTANTS MaxOffset, BuffSz, ArbitrarySymbol

ASSUME /\ MaxOffset \in Nat
       /\ MaxOffset >= 1
       /\ BuffSz \in Nat
       /\ BuffSz >= 1
       /\ BuffSz <= MaxOffset + 1

Symbols == {"Seek", "Read", "Write", "Flush", "SetLen"}

ASSUME ArbitrarySymbol \in Symbols

(*
  Basic domains and helpers
*)
Byte == 0..1
NoVal == "NoVal"

Offsets == 0..MaxOffset
MaxBuffStart == MaxOffset - BuffSz + 1

Min2(a, b) == IF a <= b THEN a ELSE b
Max2(a, b) == IF a >= b THEN a ELSE b

Range(a, b) == { i \in Nat : a <= i /\ i <= b }

NewBStart(p) ==
  LET lo == 0
      hi == MaxBuffStart
  IN Max2(lo, Min2(p, hi))

Covered == Range(BStart, BStart + BuffSz - 1)

LogAtWith(D, BS, B, i) ==
  IF i \in Range(BS, BS + BuffSz - 1) THEN B[i - BS] ELSE D[i]

LogC == [ i \in Offsets |-> LogAtWith(Disk, BStart, Buf, i) ]

(*
  State variables
*)
VARIABLES
  Disk,      \* Offsets -> Byte
  Len,       \* underlying (on-disk) length, in 0 .. MaxOffset+1
  LLen,      \* logical (client-visible) length, in 0 .. MaxOffset+1
  Buf,       \* 0..BuffSz-1 -> Byte
  BStart,    \* buffer window start in 0..MaxBuffStart
  Dirty,     \* BOOLEAN
  WriteSet,  \* subset of Offsets written in buffer (unflushed)
  Pos,       \* current position, in 0..MaxOffset+1
  RVal,      \* last read value, in Byte \cup {NoVal}
  WVal       \* last written value, in Byte \cup {NoVal}

vars == << Disk, Len, LLen, Buf, BStart, Dirty, WriteSet, Pos, RVal, WVal >>

(*
  Invariants and typing
*)
TypeOK ==
  /\ Disk \in [Offsets -> Byte]
  /\ Len \in 0..(MaxOffset + 1)
  /\ LLen \in 0..(MaxOffset + 1)
  /\ Len <= LLen
  /\ Buf \in [0..BuffSz - 1 -> Byte]
  /\ BStart \in 0..MaxBuffStart
  /\ Dirty \in BOOLEAN
  /\ WriteSet \subseteq Offsets
  /\ Pos \in 0..(MaxOffset + 1)
  /\ RVal \in (Byte \cup {NoVal})
  /\ WVal \in (Byte \cup {NoVal})

Inv2 ==
  /\ BStart \in 0..MaxBuffStart
  /\ BStart <= Pos
  /\ Pos <= BStart + BuffSz

Inv1 ==
  /\ LLen \in 0..(MaxOffset + 1)
  /\ Len \in 0..(MaxOffset + 1)
  /\ Len <= LLen
  /\ (~Dirty => Len = LLen)
  /\ \A i \in Offsets: LogC[i] = LogAtWith(Disk, BStart, Buf, i)

Inv3 ==
  \A i \in Covered: LogC[i] = Buf[i - BStart]

Inv4 ==
  \A i \in Offsets \ Covered: LogC[i] = Disk[i]

Inv5 ==
  Dirty => ( (\E i \in Covered: Buf[i - BStart] # Disk[i]) \/ (LLen # Len) )

Inv2CanAlwaysBeRestored ==
  /\ (Dirty => ENABLED Flush)
  /\ (\A p \in 0..LLen: ~Dirty => ENABLED SeekTo(p))
  /\ (Flush => ~Dirty')
  /\ ((~Dirty /\ SeekTo(Pos)) => Inv2')

(*
  Initialization
*)
Init ==
  \E d \in [Offsets -> Byte],
    l \in 0..(MaxOffset + 1),
    p \in 0..(MaxOffset + 1):
    LET bs == NewBStart(p) IN
    /\ Disk = d
    /\ Len = l
    /\ LLen = l
    /\ Pos = p
    /\ BStart = bs
    /\ Buf = [i \in 0..BuffSz - 1 |-> d[bs + i]]
    /\ Dirty = FALSE
    /\ WriteSet = {}
    /\ RVal = NoVal
    /\ WVal = NoVal

(*
  Actions
*)

Flush ==
  /\ Dirty
  /\ Disk' = [ i \in Offsets |-> IF i \in WriteSet THEN Buf[i - BStart] ELSE Disk[i] ]
  /\ Len'  = LLen
  /\ Dirty' = FALSE
  /\ WriteSet' = {}
  /\ UNCHANGED << Pos, BStart, Buf, RVal, WVal, LLen >>

SeekTo(p) ==
  /\ p \in 0..LLen
  /\ IF p \in Covered THEN
        /\ Pos' = p
        /\ UNCHANGED << Disk, Len, LLen, Buf, BStart, Dirty, WriteSet, RVal, WVal >>
     ELSE
        /\ Disk' = IF Dirty
                   THEN [ i \in Offsets |-> IF i \in WriteSet THEN Buf[i - BStart] ELSE Disk[i] ]
                   ELSE Disk
        /\ Len'  = IF Dirty THEN LLen ELSE Len
        /\ Dirty' = FALSE
        /\ WriteSet' = {}
        /\ BStart' = NewBStart(p)
        /\ Buf' = [ i \in 0..BuffSz - 1 |-> Disk'[BStart' + i] ]
        /\ Pos' = p
        /\ UNCHANGED << RVal, WVal, LLen >>

Seek == \E p \in 0..LLen: SeekTo(p)

Read1 ==
  /\ Pos < LLen
  /\ IF Pos \in Covered THEN
        /\ RVal' = Buf[Pos - BStart]
        /\ Pos' = Pos + 1
        /\ UNCHANGED << Disk, Len, LLen, Buf, BStart, Dirty, WriteSet, WVal >>
     ELSE
        LET newDisk == IF Dirty
                       THEN [ i \in Offsets |-> IF i \in WriteSet THEN Buf[i - BStart] ELSE Disk[i] ]
                       ELSE Disk,
            newLen  == IF Dirty THEN LLen ELSE Len,
            newB    == NewBStart(Pos),
            newBuf  == [ i \in 0..BuffSz - 1 |-> newDisk[newB + i] ]
        IN
        /\ Disk' = newDisk
        /\ Len'  = newLen
        /\ Dirty' = FALSE
        /\ WriteSet' = {}
        /\ BStart' = newB
        /\ Buf' = newBuf
        /\ RVal' = Buf'[Pos - BStart']
        /\ Pos' = Pos + 1
        /\ UNCHANGED << LLen, WVal >>

Write1 ==
  /\ Pos <= MaxOffset
  /\ \E w \in Byte:
       /\ WVal' = w
       /\ IF Pos \in Covered THEN
             /\ Buf' = [ Buf EXCEPT ![Pos - BStart] = WVal' ]
             /\ Dirty' = TRUE
             /\ WriteSet' = WriteSet \cup {Pos}
             /\ LLen' = Max2(LLen, Pos + 1)
             /\ Pos' = Pos + 1
             /\ UNCHANGED << Disk, Len, BStart, RVal >>
          ELSE
             LET newDisk == IF Dirty
                            THEN [ i \in Offsets |-> IF i \in WriteSet THEN Buf[i - BStart] ELSE Disk[i] ]
                            ELSE Disk,
                 newLen  == IF Dirty THEN LLen ELSE Len,
                 newB    == NewBStart(Pos),
                 newBuf  == [ i \in 0..BuffSz - 1 |-> newDisk[newB + i] ]
             IN
             /\ Disk' = newDisk
             /\ Len'  = newLen
             /\ BStart' = newB
             /\ Buf' = [ newBuf EXCEPT ![Pos - newB] = WVal' ]
             /\ Dirty' = TRUE
             /\ WriteSet' = {Pos}
             /\ LLen' = Max2(LLen, Pos + 1)
             /\ Pos' = Pos + 1
             /\ UNCHANGED << RVal >>

SetLen ==
  \E n \in 0..(MaxOffset + 1):
    /\ Disk' = IF Dirty
               THEN [ i \in Offsets |-> IF i \in WriteSet THEN Buf[i - BStart] ELSE Disk[i] ]
               ELSE Disk
    /\ Len' = n
    /\ LLen' = n
    /\ Dirty' = FALSE
    /\ WriteSet' = {}
    /\ UNCHANGED << BStart, Buf, Pos, RVal, WVal >>

Next ==
  Flush \/ Seek \/ Read1 \/ Write1 \/ SetLen

Spec == Init /\ [][Next]_vars

(*
  Correctness action properties
*)
FlushBufferCorrect ==
  /\ (Dirty => ENABLED Flush)
  /\ (Flush => ~Dirty')
  /\ (Flush => Len' = LLen)

SeekCorrect ==
  /\ \A p \in 0..LLen: (~Dirty /\ SeekTo(p)) => UNCHANGED << Disk, Len, LLen >>
  /\ \A p \in 0..LLen: SeekTo(p) => Pos' = p

SeekEstablishesInv2 ==
  \A p \in 0..LLen: (~Dirty /\ SeekTo(p)) => Inv2'

Read1Correct ==
  Read1 =>
    /\ Pos' = Pos + 1
    /\ RVal' = LogAtWith(Disk, BStart, Buf, Pos)
    /\ LLen' = LLen

Write1Correct ==
  Write1 =>
    /\ Pos' = Pos + 1
    /\ LLen' = Max2(LLen, Pos + 1)
    /\ Buf'[Pos' - 1 - BStart'] = WVal'

WriteAtMostCorrect == Write1Correct
ReadCorrect == Read1Correct

Safety == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ Inv4 /\ Inv5

====