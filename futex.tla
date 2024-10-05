---- MODULE futex ----
(******************************************************************************)
(* Model that implements mutexes using futexes                                *)
(* Locking algorithm is based on Ulrich Drepper's paper "Futexes are tricky"  *)
(******************************************************************************)
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

macro atomic_compare_exchange(x, oldval, expecting, newval) begin
    oldval := x;
    if x = expecting then
        x := newval;
    end if;
end macro;

macro atomic_exchange(x, oldval, newval) begin
    oldval := x;
    x := newval;
end macro;

(******************************************************************************)
(*                                                                            *)
(* Locking                                                                    *)
(*                                                                            *)
(******************************************************************************)

procedure acquire_lock()
variable lprev;
begin
           \* Attempt to acquire the lock
Lcmpx1:    atomic_compare_exchange(mem[a], lprev, Free, Acquired);
Ltest:     while lprev # Free do
              \* Mark the lock as contended, assuming it's in the acquired state
Lcmpx2:       atomic_compare_exchange(mem[a], lprev, Acquired, Contended);
              if lprev # Free then
call_wait:        call futex_wait(a, Contended);
              end if;
              \* Attempt to acquire the lock again
Lcmpx3:       atomic_compare_exchange(mem[a], lprev, Free, Contended);
           end while;
            \* if we reach here, we have the lock
Lret:      return;
end procedure;


procedure futex_wait(addr, val)
begin
wt_acq:       await qlock = {};
              qlock := {self};
wt_valcheck:  if val /= mem[addr] then
                qlock := {};
                return;
              end if;
              \* Add the process to the wait queue for this address
wt_enq:       waitq[addr] := Append(waitq[addr], self);
              qlock := {};
wt_wait:      await self \in wake;
              wake := wake \ {self};
              return;
end procedure;


(******************************************************************************)
(*                                                                            *)
(* Unlocking                                                                  *)
(*                                                                            *)
(******************************************************************************)


procedure release_lock()
variable uprev;
begin
u_xch:  atomic_exchange(mem[a], uprev, Free);
u_wake: if uprev = Contended then
           call futex_wake(a);
        end if;
u_ret:  return;
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
    acq: call acquire_lock();
    cs: skip;
    rel: call release_lock();
         goto ncs;
end process;

end algorithm;

*)
\* BEGIN TRANSLATION (chksum(pcal) = "f81c78d" /\ chksum(tla) = "1583eac1")
\* Parameter addr of procedure futex_wait at line 64 col 22 changed to addr_
CONSTANT defaultInitValue
VARIABLES pc, mem, waitq, qlock, a, wake, stack, lprev, addr_, val, uprev, 
          addr, nxt

vars == << pc, mem, waitq, qlock, a, wake, stack, lprev, addr_, val, uprev, 
           addr, nxt >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ mem = [x \in Addresses |-> Free]
        /\ waitq = [x \in Addresses |-> <<>>]
        /\ qlock = {}
        /\ a \in Addresses
        /\ wake = {}
        (* Procedure acquire_lock *)
        /\ lprev = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure futex_wait *)
        /\ addr_ = [ self \in ProcSet |-> defaultInitValue]
        /\ val = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure release_lock *)
        /\ uprev = [ self \in ProcSet |-> defaultInitValue]
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
                /\ pc' = [pc EXCEPT ![self] = "Ltest"]
                /\ UNCHANGED << waitq, qlock, a, wake, stack, addr_, val, 
                                uprev, addr, nxt >>

Ltest(self) == /\ pc[self] = "Ltest"
               /\ IF lprev[self] /= Free
                     THEN /\ pc' = [pc EXCEPT ![self] = "Lcmpx2"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Lret"]
               /\ UNCHANGED << mem, waitq, qlock, a, wake, stack, lprev, addr_, 
                               val, uprev, addr, nxt >>

Lcmpx2(self) == /\ pc[self] = "Lcmpx2"
                /\ lprev' = [lprev EXCEPT ![self] = mem[a]]
                /\ IF (mem[a]) = Acquired
                      THEN /\ mem' = [mem EXCEPT ![a] = Contended]
                      ELSE /\ TRUE
                           /\ mem' = mem
                /\ IF lprev'[self] /= Free
                      THEN /\ pc' = [pc EXCEPT ![self] = "call_wait"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "Lcmpx3"]
                /\ UNCHANGED << waitq, qlock, a, wake, stack, addr_, val, 
                                uprev, addr, nxt >>

call_wait(self) == /\ pc[self] = "call_wait"
                   /\ /\ addr_' = [addr_ EXCEPT ![self] = a]
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "futex_wait",
                                                               pc        |->  "Lcmpx3",
                                                               addr_     |->  addr_[self],
                                                               val       |->  val[self] ] >>
                                                           \o stack[self]]
                      /\ val' = [val EXCEPT ![self] = Contended]
                   /\ pc' = [pc EXCEPT ![self] = "wt_acq"]
                   /\ UNCHANGED << mem, waitq, qlock, a, wake, lprev, uprev, 
                                   addr, nxt >>

Lcmpx3(self) == /\ pc[self] = "Lcmpx3"
                /\ lprev' = [lprev EXCEPT ![self] = mem[a]]
                /\ IF (mem[a]) = Free
                      THEN /\ mem' = [mem EXCEPT ![a] = Contended]
                      ELSE /\ TRUE
                           /\ mem' = mem
                /\ pc' = [pc EXCEPT ![self] = "Ltest"]
                /\ UNCHANGED << waitq, qlock, a, wake, stack, addr_, val, 
                                uprev, addr, nxt >>

Lret(self) == /\ pc[self] = "Lret"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ lprev' = [lprev EXCEPT ![self] = Head(stack[self]).lprev]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << mem, waitq, qlock, a, wake, addr_, val, uprev, 
                              addr, nxt >>

acquire_lock(self) == Lcmpx1(self) \/ Ltest(self) \/ Lcmpx2(self)
                         \/ call_wait(self) \/ Lcmpx3(self) \/ Lret(self)

wt_acq(self) == /\ pc[self] = "wt_acq"
                /\ qlock = {}
                /\ qlock' = {self}
                /\ pc' = [pc EXCEPT ![self] = "wt_valcheck"]
                /\ UNCHANGED << mem, waitq, a, wake, stack, lprev, addr_, val, 
                                uprev, addr, nxt >>

wt_valcheck(self) == /\ pc[self] = "wt_valcheck"
                     /\ IF val[self] /= mem[addr_[self]]
                           THEN /\ qlock' = {}
                                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ addr_' = [addr_ EXCEPT ![self] = Head(stack[self]).addr_]
                                /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "wt_enq"]
                                /\ UNCHANGED << qlock, stack, addr_, val >>
                     /\ UNCHANGED << mem, waitq, a, wake, lprev, uprev, addr, 
                                     nxt >>

wt_enq(self) == /\ pc[self] = "wt_enq"
                /\ waitq' = [waitq EXCEPT ![addr_[self]] = Append(waitq[addr_[self]], self)]
                /\ qlock' = {}
                /\ pc' = [pc EXCEPT ![self] = "wt_wait"]
                /\ UNCHANGED << mem, a, wake, stack, lprev, addr_, val, uprev, 
                                addr, nxt >>

wt_wait(self) == /\ pc[self] = "wt_wait"
                 /\ self \in wake
                 /\ wake' = wake \ {self}
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ addr_' = [addr_ EXCEPT ![self] = Head(stack[self]).addr_]
                 /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << mem, waitq, qlock, a, lprev, uprev, addr, nxt >>

futex_wait(self) == wt_acq(self) \/ wt_valcheck(self) \/ wt_enq(self)
                       \/ wt_wait(self)

u_xch(self) == /\ pc[self] = "u_xch"
               /\ uprev' = [uprev EXCEPT ![self] = mem[a]]
               /\ mem' = [mem EXCEPT ![a] = Free]
               /\ pc' = [pc EXCEPT ![self] = "u_wake"]
               /\ UNCHANGED << waitq, qlock, a, wake, stack, lprev, addr_, val, 
                               addr, nxt >>

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
                /\ UNCHANGED << mem, waitq, qlock, a, wake, lprev, addr_, val, 
                                uprev >>

u_ret(self) == /\ pc[self] = "u_ret"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ uprev' = [uprev EXCEPT ![self] = Head(stack[self]).uprev]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << mem, waitq, qlock, a, wake, lprev, addr_, val, 
                               addr, nxt >>

release_lock(self) == u_xch(self) \/ u_wake(self) \/ u_ret(self)

wk_acq(self) == /\ pc[self] = "wk_acq"
                /\ qlock = {}
                /\ qlock' = {self}
                /\ pc' = [pc EXCEPT ![self] = "wk_deq"]
                /\ UNCHANGED << mem, waitq, a, wake, stack, lprev, addr_, val, 
                                uprev, addr, nxt >>

wk_deq(self) == /\ pc[self] = "wk_deq"
                /\ IF waitq[addr[self]] /= <<>>
                      THEN /\ nxt' = [nxt EXCEPT ![self] = {Head(waitq[addr[self]])}]
                           /\ waitq' = [waitq EXCEPT ![addr[self]] = Tail(waitq[addr[self]])]
                      ELSE /\ TRUE
                           /\ UNCHANGED << waitq, nxt >>
                /\ pc' = [pc EXCEPT ![self] = "wk_rel"]
                /\ UNCHANGED << mem, qlock, a, wake, stack, lprev, addr_, val, 
                                uprev, addr >>

wk_rel(self) == /\ pc[self] = "wk_rel"
                /\ qlock' = {}
                /\ pc' = [pc EXCEPT ![self] = "wk_wake"]
                /\ UNCHANGED << mem, waitq, a, wake, stack, lprev, addr_, val, 
                                uprev, addr, nxt >>

wk_wake(self) == /\ pc[self] = "wk_wake"
                 /\ wake' = (wake \union nxt[self])
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ nxt' = [nxt EXCEPT ![self] = Head(stack[self]).nxt]
                 /\ addr' = [addr EXCEPT ![self] = Head(stack[self]).addr]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << mem, waitq, qlock, a, lprev, addr_, val, 
                                 uprev >>

futex_wake(self) == wk_acq(self) \/ wk_deq(self) \/ wk_rel(self)
                       \/ wk_wake(self)

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "acq"]
             /\ UNCHANGED << mem, waitq, qlock, a, wake, stack, lprev, addr_, 
                             val, uprev, addr, nxt >>

acq(self) == /\ pc[self] = "acq"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "acquire_lock",
                                                      pc        |->  "cs",
                                                      lprev     |->  lprev[self] ] >>
                                                  \o stack[self]]
             /\ lprev' = [lprev EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "Lcmpx1"]
             /\ UNCHANGED << mem, waitq, qlock, a, wake, addr_, val, uprev, 
                             addr, nxt >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "rel"]
            /\ UNCHANGED << mem, waitq, qlock, a, wake, stack, lprev, addr_, 
                            val, uprev, addr, nxt >>

rel(self) == /\ pc[self] = "rel"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "release_lock",
                                                      pc        |->  "ncs",
                                                      uprev     |->  uprev[self] ] >>
                                                  \o stack[self]]
             /\ uprev' = [uprev EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "u_xch"]
             /\ UNCHANGED << mem, waitq, qlock, a, wake, lprev, addr_, val, 
                             addr, nxt >>

proc(self) == ncs(self) \/ acq(self) \/ cs(self) \/ rel(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ acquire_lock(self) \/ futex_wait(self)
                               \/ release_lock(self) \/ futex_wake(self))
           \/ (\E self \in Processes: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

MutualExclusion == \A p1,p2 \in Processes : pc[p1]="cs" /\ pc[p2]="cs" => p1=p2

Stuck(x) == /\ pc[x] = "wt_wait"
            /\ x \notin wake
            /\ \A p \in Processes \ {x} : pc[p] = "ncs"

NoneStuck == ~ \E x \in Processes : Stuck(x)

LockIsHeld == mem[a] /= Free
ProcessAttemptingToAcquireLock(p) == pc[p] \in {"Lcmpx1", "Ltest", "Lcmpx2", "call_wait", "Lcmpx3", "wt_acq", "wt_valcheck", "wt_enq", "wt_wait"}
Contention == LockIsHeld /\ \E p \in Processes : ProcessAttemptingToAcquireLock(p)

OnlyWaitUnderContention == \E p \in Processes : pc[p]="call_wait" => Contention


InAcquireLock(p) == pc[p] \in {"Lcmpx1", "Ltest", "Lcmpx2", "call_wait", "Lcmpx3", "Lret"}
InFutexWait(p) == pc[p] \in {"wt_acq", "wt_valcheck", "wt_enq", "wt_wait"}
InReleaseLockBeforeRelease(p) == pc[p] \in {"u_xch"}
InReleaseLockAfterRelease(p) == pc[p] \in {"u_wake", "u_ret"}
InFutexWake(p) == pc[p] \in {"wk_acq", "wk_deq", "wk_rel", "wk_wake"}

lockBar == {p \in Processes: \/ pc[p] \in {"cs", "rel"}
                             \/ InReleaseLockBeforeRelease(p)}


pcBar == [p \in Processes |->
            CASE pc[p] = "ncs"                 -> "ncs"
              [] pc[p] = "cs"                  -> "cs"
              [] pc[p] = "acq"                 -> "acq"
              [] InAcquireLock(p)              -> "acq"
              [] InFutexWait(p)                -> "acq"
              [] pc[p] = "rel"                 -> "rel"
              [] InReleaseLockBeforeRelease(p) -> "rel"
              [] InReleaseLockAfterRelease(p)  -> "ncs"
              [] InFutexWake(p)                -> "ncs"
]

Alias == [
    pc |-> pc,
    pcBar |-> pcBar,
    futex |-> mem[a],
    val |-> val,
    lockBar |-> lockBar
]

mutex == INSTANCE mutex WITH lock <- lockBar, pc <- pcBar

ImplementsMutex == mutex!Spec

====
