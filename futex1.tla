---- MODULE futex1 ----
EXTENDS Sequences

CONSTANTS Processes, Addresses, Free, Acquired, HasWaiters
Values == {Free, Acquired, HasWaiters}

(*--algorithm futex 

variables 
    mem = [x \in Addresses |-> Free],
    waitq = [x \in Addresses |-> <<>>],
    a \in Addresses,
    wake = {}; \* processes that have been sent a signal to wake up


macro cmpxchg(x, xwas, old, new) begin
    xwas := x;
    if x = old then 
        x := new;
    end if;
end macro;

macro atomic_exchange(x, xwas, new) begin
    xwas := x;
    x := new;
end macro;


procedure lock() 
variable lprev;
begin
L1: 
    cmpxchg(mem[a], lprev, Free, Acquired);
L2:
    if lprev /= Free then
        call futex_wait(a, lprev);
        goto L1;
    end if;
L3: return;
end procedure;

procedure futex_wait(addr, val) 
begin
WT1:
    \* Add the process to the wait queue for this address
    waitq[addr] := Append(waitq[addr], self);
WT2:
    await self \in wake;
    wake := wake \ {self};
    return;
end procedure;

procedure futex_wake(addr) 
variable p;
begin
WK1:
    p := Head(waitq[addr]);
    waitq[addr] := Tail(waitq[addr]);
WK2:
    wake := wake \union {p};
    return;
end procedure;

procedure unlock() 
variable uprev;
begin
U1: atomic_exchange(mem[a], uprev, Free);
    if uprev = HasWaiters then
        call futex_wake(a);
    end if;
U2: return;
end procedure;

process p \in Processes
begin
    ncs: skip;
    acq: call lock();
    cs: skip;
    rel: call unlock();
         goto ncs;
end process;

end algorithm;

*)
\* BEGIN TRANSLATION (chksum(pcal) = "b66f2ae9" /\ chksum(tla) = "786c1209")
\* Process p at line 74 col 1 changed to p_
\* Parameter addr of procedure futex_wait at line 42 col 22 changed to addr_
CONSTANT defaultInitValue
VARIABLES pc, mem, waitq, a, wake, stack, lprev, addr_, val, addr, p, uprev

vars == << pc, mem, waitq, a, wake, stack, lprev, addr_, val, addr, p, uprev
        >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ mem = [x \in Addresses |-> Free]
        /\ waitq = [x \in Addresses |-> <<>>]
        /\ a \in Addresses
        /\ wake = {}
        (* Procedure lock *)
        /\ lprev = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure futex_wait *)
        /\ addr_ = [ self \in ProcSet |-> defaultInitValue]
        /\ val = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure futex_wake *)
        /\ addr = [ self \in ProcSet |-> defaultInitValue]
        /\ p = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure unlock *)
        /\ uprev = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "ncs"]

L1(self) == /\ pc[self] = "L1"
            /\ lprev' = [lprev EXCEPT ![self] = mem[a]]
            /\ IF (mem[a]) = Free
                  THEN /\ mem' = [mem EXCEPT ![a] = Acquired]
                  ELSE /\ TRUE
                       /\ mem' = mem
            /\ pc' = [pc EXCEPT ![self] = "L2"]
            /\ UNCHANGED << waitq, a, wake, stack, addr_, val, addr, p, uprev >>

L2(self) == /\ pc[self] = "L2"
            /\ IF lprev[self] /= Free
                  THEN /\ /\ addr_' = [addr_ EXCEPT ![self] = a]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wait",
                                                                   pc        |->  "L1",
                                                                   addr_     |->  addr_[self],
                                                                   val       |->  val[self] ] >>
                                                               \o stack[self]]
                          /\ val' = [val EXCEPT ![self] = lprev[self]]
                       /\ pc' = [pc EXCEPT ![self] = "WT1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L3"]
                       /\ UNCHANGED << stack, addr_, val >>
            /\ UNCHANGED << mem, waitq, a, wake, lprev, addr, p, uprev >>

L3(self) == /\ pc[self] = "L3"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ lprev' = [lprev EXCEPT ![self] = Head(stack[self]).lprev]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << mem, waitq, a, wake, addr_, val, addr, p, uprev >>

lock(self) == L1(self) \/ L2(self) \/ L3(self)

WT1(self) == /\ pc[self] = "WT1"
             /\ waitq' = [waitq EXCEPT ![addr_[self]] = Append(waitq[addr_[self]], self)]
             /\ pc' = [pc EXCEPT ![self] = "WT2"]
             /\ UNCHANGED << mem, a, wake, stack, lprev, addr_, val, addr, p, 
                             uprev >>

WT2(self) == /\ pc[self] = "WT2"
             /\ self \in wake
             /\ wake' = wake \ {self}
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ addr_' = [addr_ EXCEPT ![self] = Head(stack[self]).addr_]
             /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << mem, waitq, a, lprev, addr, p, uprev >>

futex_wait(self) == WT1(self) \/ WT2(self)

WK1(self) == /\ pc[self] = "WK1"
             /\ p' = [p EXCEPT ![self] = Head(waitq[addr[self]])]
             /\ waitq' = [waitq EXCEPT ![addr[self]] = Tail(waitq[addr[self]])]
             /\ pc' = [pc EXCEPT ![self] = "WK2"]
             /\ UNCHANGED << mem, a, wake, stack, lprev, addr_, val, addr, 
                             uprev >>

WK2(self) == /\ pc[self] = "WK2"
             /\ wake' = (wake \union {p[self]})
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ p' = [p EXCEPT ![self] = Head(stack[self]).p]
             /\ addr' = [addr EXCEPT ![self] = Head(stack[self]).addr]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << mem, waitq, a, lprev, addr_, val, uprev >>

futex_wake(self) == WK1(self) \/ WK2(self)

U1(self) == /\ pc[self] = "U1"
            /\ uprev' = [uprev EXCEPT ![self] = mem[a]]
            /\ mem' = [mem EXCEPT ![a] = Free]
            /\ IF uprev'[self] = HasWaiters
                  THEN /\ /\ addr' = [addr EXCEPT ![self] = a]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wake",
                                                                   pc        |->  "U2",
                                                                   p         |->  p[self],
                                                                   addr      |->  addr[self] ] >>
                                                               \o stack[self]]
                       /\ p' = [p EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "WK1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "U2"]
                       /\ UNCHANGED << stack, addr, p >>
            /\ UNCHANGED << waitq, a, wake, lprev, addr_, val >>

U2(self) == /\ pc[self] = "U2"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ uprev' = [uprev EXCEPT ![self] = Head(stack[self]).uprev]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << mem, waitq, a, wake, lprev, addr_, val, addr, p >>

unlock(self) == U1(self) \/ U2(self)

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "acq"]
             /\ UNCHANGED << mem, waitq, a, wake, stack, lprev, addr_, val, 
                             addr, p, uprev >>

acq(self) == /\ pc[self] = "acq"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                      pc        |->  "cs",
                                                      lprev     |->  lprev[self] ] >>
                                                  \o stack[self]]
             /\ lprev' = [lprev EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "L1"]
             /\ UNCHANGED << mem, waitq, a, wake, addr_, val, addr, p, uprev >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "rel"]
            /\ UNCHANGED << mem, waitq, a, wake, stack, lprev, addr_, val, 
                            addr, p, uprev >>

rel(self) == /\ pc[self] = "rel"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                      pc        |->  "ncs",
                                                      uprev     |->  uprev[self] ] >>
                                                  \o stack[self]]
             /\ uprev' = [uprev EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "U1"]
             /\ UNCHANGED << mem, waitq, a, wake, lprev, addr_, val, addr, p >>

p_(self) == ncs(self) \/ acq(self) \/ cs(self) \/ rel(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ lock(self) \/ futex_wait(self)
                               \/ futex_wake(self) \/ unlock(self))
           \/ (\E self \in Processes: p_(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


====
