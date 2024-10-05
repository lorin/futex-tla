
---- MODULE futex4 ----
EXTENDS Naturals, Sequences

CONSTANTS Processes, Addresses, Free, Acquired, HasWaiters
Values == {Free, Acquired, HasWaiters}

(*--algorithm futex 

variables 
    mem = [x \in Addresses |-> Free],
    waitq = [x \in Addresses |-> <<>>], \* a map of addresses to wait queues
    qlock = {},  \* traditional mutex lock used by the kernel on the wait queue. 
    a \in Addresses,
    wake = {}; \* processes that have been sent a signal to wake up


macro atomic_compare_exchange(x, xwas, old, new) begin
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
variable lprev, lprev2;
begin
L1: atomic_compare_exchange(mem[a], lprev, Free, Acquired);
L2: if lprev /= Free then
L3:   atomic_compare_exchange(mem[a], lprev2, Acquired, HasWaiters);
      if lprev = HasWaiters \/ lprev2 /= Free then
L4:     call futex_wait(a, lprev);
      end if;
L5:   atomic_compare_exchange(mem[a], lprev, Free, HasWaiters);
L6:   if lprev /= Free then 
        goto L3;
      end if;
    end if;
L7: return;
end procedure;

procedure futex_wait(addr, val) 
begin
wt_acq: 
    await qlock = {};
     qlock := {self};
wt_valcheck: 
    if val /= mem[addr] then 
        qlock := {};
        return;
    end if;
    \* Add the process to the wait queue for this address
wt_enq:
     waitq[addr] := Append(waitq[addr], self);
     qlock := {};
wt_wait:
    await self \in wake;
    wake := wake \ {self};
    return;
end procedure;

procedure futex_wake(addr) 
variable p = {};
begin
wk_acq: 
     await qlock = {};
     qlock := {self};
wk_deq: 
     if waitq[addr] /= <<>> then
        p := {Head(waitq[addr])};
        waitq[addr] := Tail(waitq[addr]);
     end if;
wk_rel: 
    qlock := {};
wk_wake: 
    wake := wake \union p;
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
\* BEGIN TRANSLATION (chksum(pcal) = "80711736" /\ chksum(tla) = "16d2bf3a")
\* Process p at line 96 col 1 changed to p_
\* Parameter addr of procedure futex_wait at line 48 col 22 changed to addr_
CONSTANT defaultInitValue
VARIABLES pc, mem, waitq, qlock, a, wake, stack, lprev, lprev2, addr_, val, 
          addr, p, uprev

vars == << pc, mem, waitq, qlock, a, wake, stack, lprev, lprev2, addr_, val, 
           addr, p, uprev >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ mem = [x \in Addresses |-> Free]
        /\ waitq = [x \in Addresses |-> <<>>]
        /\ qlock = {}
        /\ a \in Addresses
        /\ wake = {}
        (* Procedure lock *)
        /\ lprev = [ self \in ProcSet |-> defaultInitValue]
        /\ lprev2 = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure futex_wait *)
        /\ addr_ = [ self \in ProcSet |-> defaultInitValue]
        /\ val = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure futex_wake *)
        /\ addr = [ self \in ProcSet |-> defaultInitValue]
        /\ p = [ self \in ProcSet |-> {}]
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
            /\ UNCHANGED << waitq, qlock, a, wake, stack, lprev2, addr_, val, 
                            addr, p, uprev >>

L2(self) == /\ pc[self] = "L2"
            /\ IF lprev[self] /= Free
                  THEN /\ pc' = [pc EXCEPT ![self] = "L3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L7"]
            /\ UNCHANGED << mem, waitq, qlock, a, wake, stack, lprev, lprev2, 
                            addr_, val, addr, p, uprev >>

L3(self) == /\ pc[self] = "L3"
            /\ lprev2' = [lprev2 EXCEPT ![self] = mem[a]]
            /\ IF (mem[a]) = Acquired
                  THEN /\ mem' = [mem EXCEPT ![a] = HasWaiters]
                  ELSE /\ TRUE
                       /\ mem' = mem
            /\ IF lprev[self] = HasWaiters \/ lprev2'[self] /= Free
                  THEN /\ pc' = [pc EXCEPT ![self] = "L4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L5"]
            /\ UNCHANGED << waitq, qlock, a, wake, stack, lprev, addr_, val, 
                            addr, p, uprev >>

L4(self) == /\ pc[self] = "L4"
            /\ /\ addr_' = [addr_ EXCEPT ![self] = a]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wait",
                                                        pc        |->  "L5",
                                                        addr_     |->  addr_[self],
                                                        val       |->  val[self] ] >>
                                                    \o stack[self]]
               /\ val' = [val EXCEPT ![self] = lprev[self]]
            /\ pc' = [pc EXCEPT ![self] = "wt_acq"]
            /\ UNCHANGED << mem, waitq, qlock, a, wake, lprev, lprev2, addr, p, 
                            uprev >>

L5(self) == /\ pc[self] = "L5"
            /\ lprev' = [lprev EXCEPT ![self] = mem[a]]
            /\ IF (mem[a]) = Free
                  THEN /\ mem' = [mem EXCEPT ![a] = HasWaiters]
                  ELSE /\ TRUE
                       /\ mem' = mem
            /\ pc' = [pc EXCEPT ![self] = "L6"]
            /\ UNCHANGED << waitq, qlock, a, wake, stack, lprev2, addr_, val, 
                            addr, p, uprev >>

L6(self) == /\ pc[self] = "L6"
            /\ IF lprev[self] /= Free
                  THEN /\ pc' = [pc EXCEPT ![self] = "L3"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "L7"]
            /\ UNCHANGED << mem, waitq, qlock, a, wake, stack, lprev, lprev2, 
                            addr_, val, addr, p, uprev >>

L7(self) == /\ pc[self] = "L7"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ lprev' = [lprev EXCEPT ![self] = Head(stack[self]).lprev]
            /\ lprev2' = [lprev2 EXCEPT ![self] = Head(stack[self]).lprev2]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << mem, waitq, qlock, a, wake, addr_, val, addr, p, 
                            uprev >>

lock(self) == L1(self) \/ L2(self) \/ L3(self) \/ L4(self) \/ L5(self)
                 \/ L6(self) \/ L7(self)

wt_acq(self) == /\ pc[self] = "wt_acq"
                /\ qlock = {}
                /\ qlock' = {self}
                /\ pc' = [pc EXCEPT ![self] = "wt_valcheck"]
                /\ UNCHANGED << mem, waitq, a, wake, stack, lprev, lprev2, 
                                addr_, val, addr, p, uprev >>

wt_valcheck(self) == /\ pc[self] = "wt_valcheck"
                     /\ IF val[self] /= mem[addr_[self]]
                           THEN /\ qlock' = {}
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ addr_' = [addr_ EXCEPT ![self] = Head(stack[self]).addr_]
                                /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "wt_enq"]
                                /\ UNCHANGED << qlock, stack, addr_, val >>
                     /\ UNCHANGED << mem, waitq, a, wake, lprev, lprev2, addr, 
                                     p, uprev >>

wt_enq(self) == /\ pc[self] = "wt_enq"
                /\ waitq' = [waitq EXCEPT ![addr_[self]] = Append(waitq[addr_[self]], self)]
                /\ qlock' = {}
                /\ pc' = [pc EXCEPT ![self] = "wt_wait"]
                /\ UNCHANGED << mem, a, wake, stack, lprev, lprev2, addr_, val, 
                                addr, p, uprev >>

wt_wait(self) == /\ pc[self] = "wt_wait"
                 /\ self \in wake
                 /\ wake' = wake \ {self}
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ addr_' = [addr_ EXCEPT ![self] = Head(stack[self]).addr_]
                 /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << mem, waitq, qlock, a, lprev, lprev2, addr, p, 
                                 uprev >>

futex_wait(self) == wt_acq(self) \/ wt_valcheck(self) \/ wt_enq(self)
                       \/ wt_wait(self)

wk_acq(self) == /\ pc[self] = "wk_acq"
                /\ qlock = {}
                /\ qlock' = {self}
                /\ pc' = [pc EXCEPT ![self] = "wk_deq"]
                /\ UNCHANGED << mem, waitq, a, wake, stack, lprev, lprev2, 
                                addr_, val, addr, p, uprev >>

wk_deq(self) == /\ pc[self] = "wk_deq"
                /\ IF waitq[addr[self]] /= <<>>
                      THEN /\ p' = [p EXCEPT ![self] = {Head(waitq[addr[self]])}]
                           /\ waitq' = [waitq EXCEPT ![addr[self]] = Tail(waitq[addr[self]])]
                      ELSE /\ TRUE
                           /\ UNCHANGED << waitq, p >>
                /\ pc' = [pc EXCEPT ![self] = "wk_rel"]
                /\ UNCHANGED << mem, qlock, a, wake, stack, lprev, lprev2, 
                                addr_, val, addr, uprev >>

wk_rel(self) == /\ pc[self] = "wk_rel"
                /\ qlock' = {}
                /\ pc' = [pc EXCEPT ![self] = "wk_wake"]
                /\ UNCHANGED << mem, waitq, a, wake, stack, lprev, lprev2, 
                                addr_, val, addr, p, uprev >>

wk_wake(self) == /\ pc[self] = "wk_wake"
                 /\ wake' = (wake \union p[self])
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ p' = [p EXCEPT ![self] = Head(stack[self]).p]
                 /\ addr' = [addr EXCEPT ![self] = Head(stack[self]).addr]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << mem, waitq, qlock, a, lprev, lprev2, addr_, 
                                 val, uprev >>

futex_wake(self) == wk_acq(self) \/ wk_deq(self) \/ wk_rel(self)
                       \/ wk_wake(self)

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
                       /\ p' = [p EXCEPT ![self] = {}]
                       /\ pc' = [pc EXCEPT ![self] = "wk_acq"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "U2"]
                       /\ UNCHANGED << stack, addr, p >>
            /\ UNCHANGED << waitq, qlock, a, wake, lprev, lprev2, addr_, val >>

U2(self) == /\ pc[self] = "U2"
            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
            /\ uprev' = [uprev EXCEPT ![self] = Head(stack[self]).uprev]
            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
            /\ UNCHANGED << mem, waitq, qlock, a, wake, lprev, lprev2, addr_, 
                            val, addr, p >>

unlock(self) == U1(self) \/ U2(self)

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "acq"]
             /\ UNCHANGED << mem, waitq, qlock, a, wake, stack, lprev, lprev2, 
                             addr_, val, addr, p, uprev >>

acq(self) == /\ pc[self] = "acq"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                      pc        |->  "cs",
                                                      lprev     |->  lprev[self],
                                                      lprev2    |->  lprev2[self] ] >>
                                                  \o stack[self]]
             /\ lprev' = [lprev EXCEPT ![self] = defaultInitValue]
             /\ lprev2' = [lprev2 EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "L1"]
             /\ UNCHANGED << mem, waitq, qlock, a, wake, addr_, val, addr, p, 
                             uprev >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "rel"]
            /\ UNCHANGED << mem, waitq, qlock, a, wake, stack, lprev, lprev2, 
                            addr_, val, addr, p, uprev >>

rel(self) == /\ pc[self] = "rel"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                      pc        |->  "ncs",
                                                      uprev     |->  uprev[self] ] >>
                                                  \o stack[self]]
             /\ uprev' = [uprev EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "U1"]
             /\ UNCHANGED << mem, waitq, qlock, a, wake, lprev, lprev2, addr_, 
                             val, addr, p >>

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

Stuck(x) == /\ pc[x] = "WT4"
            /\ p \notin wake
            /\ \A pp \in Processes \ {x} : pc[pp] = "ncs"

NoneStuck == ~ \E x \in Processes : Stuck(x)

====
