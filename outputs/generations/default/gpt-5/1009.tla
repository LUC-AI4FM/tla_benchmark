---- MODULE RandomAccessFileAbs ----
EXTENDS Naturals, Sequences

CONSTANTS
    BYTE,
    ArbitrarySymbol,
    MAXPOS

AssumeArbNotByte == ArbitrarySymbol \notin BYTE

BYTESYM == BYTE \cup {ArbitrarySymbol}

(*
  Utility operators
*)
Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

IdxSet == 0..MAXPOS
LenSet == 0..(MAXPOS + 1)

IntRange(s, e) == { i \in Nat : s <= i /\ i < e }

ContentSeqFrom(f, start, k) ==
    [i \in 1..k |-> f[start + i - 1]]

WriteUpdate(acont, p, w, newLen) ==
    [ i \in IdxSet |->
        IF i < newLen THEN
           IF (p <= i) /\ (i < p + Len(w)) THEN w[i - p + 1]
           ELSE acont[i]
        ELSE
           ArbitrarySymbol
    ]

SetLengthUpdate(acont, oldLen, newLen) ==
    [ i \in IdxSet |->
        IF i < newLen THEN
            IF i < oldLen THEN acont[i] ELSE ArbitrarySymbol
        ELSE
            ArbitrarySymbol
    ]

VARIABLES
    apos,    \* current file pointer (0..alen)
    alen,    \* logical file length (0..MAXPOS+1)
    acont,   \* logical contents function 0..MAXPOS -> BYTESYM (beyond alen is ArbitrarySymbol)
    aret,    \* last returned value (sequence for read, null for others)
    aop,     \* last operation name
    aarg     \* last operation argument (n for read, w for write, p for seek, L for setLength)

ATypeInv ==
    /\ apos \in 0..alen
    /\ alen \in LenSet
    /\ acont \in [IdxSet -> BYTESYM]
    /\ \A i \in IntRange(alen, MAXPOS + 1) : acont[i] = ArbitrarySymbol
    /\ aop \in {"init","seek","read","write","flush","setLength"}
    /\ TRUE

AInit ==
    /\ alen \in LenSet
    /\ apos \in 0..alen
    /\ acont \in [IdxSet -> BYTESYM]
    /\ \A i \in IntRange(alen, MAXPOS + 1) : acont[i] = ArbitrarySymbol
    /\ aret = << >>
    /\ aop = "init"
    /\ aarg = "null"

ASeek ==
    \E p \in LenSet :
      /\ apos' = p
      /\ UNCHANGED << alen, acont >>
      /\ aret' = "null"
      /\ aop' = "seek"
      /\ aarg' = p

ARead ==
    \E n \in LenSet :
      LET k == Min(n, alen - apos) IN
      /\ aret' = ContentSeqFrom(acont, apos, k)
      /\ apos' = apos + k
      /\ UNCHANGED << alen, acont >>
      /\ aop' = "read"
      /\ aarg' = n

AWrite ==
    \E w \in Seq(BYTE) :
      LET m == Len(w) IN
      /\ apos + m \in LenSet
      /\ aret' = "null"
      /\ aop' = "write"
      /\ aarg' = w
      /\ LET newLen == Max(alen, apos + m) IN
         /\ alen' = newLen
         /\ acont' = WriteUpdate(acont, apos, w, newLen)
         /\ apos' = apos + m

AFlush ==
    /\ aret' = "null"
    /\ aop' = "flush"
    /\ aarg' = "null"
    /\ UNCHANGED << apos, alen, acont >>

ASetLength ==
    \E L \in LenSet :
      /\ alen' = L
      /\ apos' = IF apos <= L THEN apos ELSE L
      /\ acont' = SetLengthUpdate(acont, alen, L)
      /\ aret' = "null"
      /\ aop' = "setLength"
      /\ aarg' = L

ANext ==
    ASeek \/ ARead \/ AWrite \/ AFlush \/ ASetLength

AVars == << apos, alen, acont, aret, aop, aarg >>

ASpec == AInit /\ [][ANext]_AVars

=============================================================================