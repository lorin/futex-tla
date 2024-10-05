---- MODULE mutex ----
CONSTANT Processes

(*--algorithm MutualExclusion

variables lock = {};

process proc \in Processes 
begin

ncs:  skip;
acq:  await lock = {};
      lock := {self};
cs:   skip;
rel:  lock := lock \ {self};
      goto ncs;
end process;

end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "5e1306a3" /\ chksum(tla) = "551b377b")
VARIABLES pc, lock

vars == << pc, lock >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ lock = {}
        /\ pc = [self \in ProcSet |-> "ncs"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "acq"]
             /\ lock' = lock

acq(self) == /\ pc[self] = "acq"
             /\ lock' = {self}
             /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "rel"]
            /\ lock' = lock

rel(self) == /\ pc[self] = "rel"
             /\ lock' = lock \ {self}
             /\ pc' = [pc EXCEPT ![self] = "ncs"]

proc(self) == ncs(self) \/ acq(self) \/ cs(self) \/ rel(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Processes: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

InCriticalSection(p) == pc[p] = "cs"

MutualExclusion == \A p1,p2 \in Processes : InCriticalSection(p1) /\ InCriticalSection(p2) => p1 = p2

====
