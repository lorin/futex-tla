
---- MODULE futex4 ----
EXTENDS Naturals, Sequences

CONSTANTS Processes, Addresses, Free, Acquired, Contended
Values == {Free, Acquired, Contended}

(*--algorithm futex 

variables 
    mem = [x \in Addresses |-> Free],
    waitq = [x \in Addresses |-> <<>>], \* a map of addresses to wait queues
    qlock = {},  \* traditional mutex lock used by the kernel on the wait queue. 
    a \in Addresses,
    wake = {}; \* processes that have been sent a signal to wake up


(******************************************************************************)
(*                                                                            *)
(* Atomics                                                                    *)
(*                                                                            *)
(******************************************************************************)

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

(******************************************************************************)
(*                                                                            *)
(* Locking                                                                    *)
(*                                                                            *)
(******************************************************************************)

procedure lock() 
variable lprev;
begin
Lcmpx1: 
    \* Attempt to acquire the lock
    atomic_compare_exchange(mem[a], lprev, Free, Acquired);
Ltest1: 
    if lprev /= Free then
Lcmpx2:   
        \* Mark the lock as contended, assuming it'is in the acquired state 
        atomic_compare_exchange(mem[a], lprev, Acquired, Contended);
        if lprev /= Free then
call_wait:     
        call futex_wait(a, Contended);
      end if;
Lcmpx3:   
        atomic_compare_exchange(mem[a], lprev, Free, Contended);
Ltest2:   
        if lprev /= Free then 
            goto Lcmpx2;
      end if;
    end if;
Lret: 
    return;
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


(******************************************************************************)
(*                                                                            *)
(* Unlocking                                                                  *)
(*                                                                            *)
(******************************************************************************)


procedure unlock() 
variable uprev;
begin
u_xch: 
    atomic_exchange(mem[a], uprev, Free);
u_wake:
    if uprev = Contended then
        call futex_wake(a);
    end if;
u_ret: 
    return;
end procedure;


procedure futex_wake(addr) 
variables nxt = {}
begin
wk_acq: 
     await qlock = {};
     qlock := {self};
wk_deq: 
     if waitq[addr] /= <<>> then
        nxt := {Head(waitq[addr])};
        waitq[addr] := Tail(waitq[addr]);
     end if;
wk_rel: 
    qlock := {};
wk_wake: 
    wake := wake \union nxt;
    return;
end procedure;

process proc \in Processes
begin
    ncs: skip;
    acq: call lock();
    cs: skip;
    rel: call unlock();
         goto ncs;
end process;

end algorithm;

*)
\* BEGIN TRANSLATION (chksum(pcal) = "3b5f683e" /\ chksum(tla) = "ed33c147")
\* Parameter addr of procedure futex_wait at line 69 col 22 changed to addr_
CONSTANT defaultInitValue
VARIABLES pc, mem, waitq, qlock, a, wake, stack, lprev, lprev2, uprev, addr_, 
          val, addr, nxt

vars == << pc, mem, waitq, qlock, a, wake, stack, lprev, lprev2, uprev, addr_, 
           val, addr, nxt >>

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
        (* Procedure unlock *)
        /\ uprev = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure futex_wait *)
        /\ addr_ = [ self \in ProcSet |-> defaultInitValue]
        /\ val = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure futex_wake *)
        /\ addr = [ self \in ProcSet |-> defaultInitValue]
        /\ nxt = [ self \in ProcSet |-> {}]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "ncs"]

Lcmpx1(self) == /\ pc[self] = "Lcmpx1"
                /\ lprev' = [lprev EXCEPT ![self] = mem[a]]
                /\ IF (mem[a]) = Free
                      THEN /\ mem' = [mem EXCEPT ![a] = Acquired]
                      ELSE /\ TRUE
                           /\ mem' = mem
                /\ pc' = [pc EXCEPT ![self] = "Ltest1"]
                /\ UNCHANGED << waitq, qlock, a, wake, stack, lprev2, uprev, 
                                addr_, val, addr, nxt >>

Ltest1(self) == /\ pc[self] = "Ltest1"
                /\ IF lprev[self] /= Free
                      THEN /\ pc' = [pc EXCEPT ![self] = "Lcmpx2"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Lret"]
                /\ UNCHANGED << mem, waitq, qlock, a, wake, stack, lprev, 
                                lprev2, uprev, addr_, val, addr, nxt >>

Lcmpx2(self) == /\ pc[self] = "Lcmpx2"
                /\ lprev2' = [lprev2 EXCEPT ![self] = mem[a]]
                /\ IF (mem[a]) = Acquired
                      THEN /\ mem' = [mem EXCEPT ![a] = Contended]
                      ELSE /\ TRUE
                           /\ mem' = mem
                /\ IF lprev[self] = Contended \/ lprev2'[self] /= Free
                      THEN /\ pc' = [pc EXCEPT ![self] = "call_wait"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Lcmpx3"]
                /\ UNCHANGED << waitq, qlock, a, wake, stack, lprev, uprev, 
                                addr_, val, addr, nxt >>

call_wait(self) == /\ pc[self] = "call_wait"
                   /\ /\ addr_' = [addr_ EXCEPT ![self] = a]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wait",
                                                               pc        |->  "Lcmpx3",
                                                               addr_     |->  addr_[self],
                                                               val       |->  val[self] ] >>
                                                           \o stack[self]]
                      /\ val' = [val EXCEPT ![self] = lprev[self]]
                   /\ pc' = [pc EXCEPT ![self] = "wt_acq"]
                   /\ UNCHANGED << mem, waitq, qlock, a, wake, lprev, lprev2, 
                                   uprev, addr, nxt >>

Lcmpx3(self) == /\ pc[self] = "Lcmpx3"
                /\ lprev' = [lprev EXCEPT ![self] = mem[a]]
                /\ IF (mem[a]) = Free
                      THEN /\ mem' = [mem EXCEPT ![a] = Contended]
                      ELSE /\ TRUE
                           /\ mem' = mem
                /\ pc' = [pc EXCEPT ![self] = "Ltest2"]
                /\ UNCHANGED << waitq, qlock, a, wake, stack, lprev2, uprev, 
                                addr_, val, addr, nxt >>

Ltest2(self) == /\ pc[self] = "Ltest2"
                /\ IF lprev[self] /= Free
                      THEN /\ pc' = [pc EXCEPT ![self] = "Lcmpx2"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Lret"]
                /\ UNCHANGED << mem, waitq, qlock, a, wake, stack, lprev, 
                                lprev2, uprev, addr_, val, addr, nxt >>

Lret(self) == /\ pc[self] = "Lret"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ lprev' = [lprev EXCEPT ![self] = Head(stack[self]).lprev]
              /\ lprev2' = [lprev2 EXCEPT ![self] = Head(stack[self]).lprev2]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << mem, waitq, qlock, a, wake, uprev, addr_, val, 
                              addr, nxt >>

lock(self) == Lcmpx1(self) \/ Ltest1(self) \/ Lcmpx2(self)
                 \/ call_wait(self) \/ Lcmpx3(self) \/ Ltest2(self)
                 \/ Lret(self)

u_xch(self) == /\ pc[self] = "u_xch"
               /\ uprev' = [uprev EXCEPT ![self] = mem[a]]
               /\ mem' = [mem EXCEPT ![a] = Free]
               /\ pc' = [pc EXCEPT ![self] = "u_wake"]
               /\ UNCHANGED << waitq, qlock, a, wake, stack, lprev, lprev2, 
                               addr_, val, addr, nxt >>

u_wake(self) == /\ pc[self] = "u_wake"
                /\ IF uprev[self] = Contended
                      THEN /\ /\ addr' = [addr EXCEPT ![self] = a]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wake",
                                                                       pc        |->  "u_ret",
                                                                       nxt       |->  nxt[self],
                                                                       addr      |->  addr[self] ] >>
                                                                   \o stack[self]]
                           /\ nxt' = [nxt EXCEPT ![self] = {}]
                           /\ pc' = [pc EXCEPT ![self] = "wk_acq"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "u_ret"]
                           /\ UNCHANGED << stack, addr, nxt >>
                /\ UNCHANGED << mem, waitq, qlock, a, wake, lprev, lprev2, 
                                uprev, addr_, val >>

u_ret(self) == /\ pc[self] = "u_ret"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ uprev' = [uprev EXCEPT ![self] = Head(stack[self]).uprev]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << mem, waitq, qlock, a, wake, lprev, lprev2, 
                               addr_, val, addr, nxt >>

unlock(self) == u_xch(self) \/ u_wake(self) \/ u_ret(self)

wt_acq(self) == /\ pc[self] = "wt_acq"
                /\ qlock = {}
                /\ qlock' = {self}
                /\ pc' = [pc EXCEPT ![self] = "wt_valcheck"]
                /\ UNCHANGED << mem, waitq, a, wake, stack, lprev, lprev2, 
                                uprev, addr_, val, addr, nxt >>

wt_valcheck(self) == /\ pc[self] = "wt_valcheck"
                     /\ IF val[self] /= mem[addr_[self]]
                           THEN /\ qlock' = {}
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ addr_' = [addr_ EXCEPT ![self] = Head(stack[self]).addr_]
                                /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "wt_enq"]
                                /\ UNCHANGED << qlock, stack, addr_, val >>
                     /\ UNCHANGED << mem, waitq, a, wake, lprev, lprev2, uprev, 
                                     addr, nxt >>

wt_enq(self) == /\ pc[self] = "wt_enq"
                /\ waitq' = [waitq EXCEPT ![addr_[self]] = Append(waitq[addr_[self]], self)]
                /\ qlock' = {}
                /\ pc' = [pc EXCEPT ![self] = "wt_wait"]
                /\ UNCHANGED << mem, a, wake, stack, lprev, lprev2, uprev, 
                                addr_, val, addr, nxt >>

wt_wait(self) == /\ pc[self] = "wt_wait"
                 /\ self \in wake
                 /\ wake' = wake \ {self}
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ addr_' = [addr_ EXCEPT ![self] = Head(stack[self]).addr_]
                 /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << mem, waitq, qlock, a, lprev, lprev2, uprev, 
                                 addr, nxt >>

futex_wait(self) == wt_acq(self) \/ wt_valcheck(self) \/ wt_enq(self)
                       \/ wt_wait(self)

wk_acq(self) == /\ pc[self] = "wk_acq"
                /\ qlock = {}
                /\ qlock' = {self}
                /\ pc' = [pc EXCEPT ![self] = "wk_deq"]
                /\ UNCHANGED << mem, waitq, a, wake, stack, lprev, lprev2, 
                                uprev, addr_, val, addr, nxt >>

wk_deq(self) == /\ pc[self] = "wk_deq"
                /\ IF waitq[addr[self]] /= <<>>
                      THEN /\ nxt' = [nxt EXCEPT ![self] = {Head(waitq[addr[self]])}]
                           /\ waitq' = [waitq EXCEPT ![addr[self]] = Tail(waitq[addr[self]])]
                      ELSE /\ TRUE
                           /\ UNCHANGED << waitq, nxt >>
                /\ pc' = [pc EXCEPT ![self] = "wk_rel"]
                /\ UNCHANGED << mem, qlock, a, wake, stack, lprev, lprev2, 
                                uprev, addr_, val, addr >>

wk_rel(self) == /\ pc[self] = "wk_rel"
                /\ qlock' = {}
                /\ pc' = [pc EXCEPT ![self] = "wk_wake"]
                /\ UNCHANGED << mem, waitq, a, wake, stack, lprev, lprev2, 
                                uprev, addr_, val, addr, nxt >>

wk_wake(self) == /\ pc[self] = "wk_wake"
                 /\ wake' = (wake \union nxt[self])
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ nxt' = [nxt EXCEPT ![self] = Head(stack[self]).nxt]
                 /\ addr' = [addr EXCEPT ![self] = Head(stack[self]).addr]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << mem, waitq, qlock, a, lprev, lprev2, uprev, 
                                 addr_, val >>

futex_wake(self) == wk_acq(self) \/ wk_deq(self) \/ wk_rel(self)
                       \/ wk_wake(self)

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "acq"]
             /\ UNCHANGED << mem, waitq, qlock, a, wake, stack, lprev, lprev2, 
                             uprev, addr_, val, addr, nxt >>

acq(self) == /\ pc[self] = "acq"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lock",
                                                      pc        |->  "cs",
                                                      lprev     |->  lprev[self],
                                                      lprev2    |->  lprev2[self] ] >>
                                                  \o stack[self]]
             /\ lprev' = [lprev EXCEPT ![self] = defaultInitValue]
             /\ lprev2' = [lprev2 EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "Lcmpx1"]
             /\ UNCHANGED << mem, waitq, qlock, a, wake, uprev, addr_, val, 
                             addr, nxt >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "rel"]
            /\ UNCHANGED << mem, waitq, qlock, a, wake, stack, lprev, lprev2, 
                            uprev, addr_, val, addr, nxt >>

rel(self) == /\ pc[self] = "rel"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "unlock",
                                                      pc        |->  "ncs",
                                                      uprev     |->  uprev[self] ] >>
                                                  \o stack[self]]
             /\ uprev' = [uprev EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "u_xch"]
             /\ UNCHANGED << mem, waitq, qlock, a, wake, lprev, lprev2, addr_, 
                             val, addr, nxt >>

proc(self) == ncs(self) \/ acq(self) \/ cs(self) \/ rel(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ lock(self) \/ unlock(self)
                               \/ futex_wait(self) \/ futex_wake(self))
           \/ (\E self \in Processes: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Stuck(x) == /\ pc[x] = "wt_wait"
            /\ nxt \notin wake
            /\ \A p \in Processes \ {x} : pc[p] = "ncs"


NoneStuck == ~ \E x \in Processes : Stuck(x)

====
