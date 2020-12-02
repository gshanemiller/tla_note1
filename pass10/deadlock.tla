----------------------------- MODULE deadlock ------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT N

(*--algorithm phil

\* Philosophers are numbered 0..N-1
\* For each philosopher i there is one
\* process who's name is i. N is the total
\* number of philosophers.
\*
\* The ith fork is equal to N if available
\* otherwise fork[i]=p and p is the philosopher
\* who's using the fork with p \in [0..N-1]

\* Initially all forks are available
variable fork = [k \in 0..N-1 |-> N],

define
    \* For philosopher i, the left fork is the ith fork
    LeftF(i) == i

    \* For philopspher i, the right fork is i-i
    \* unless wrap around (modulos) is needed
    RightF(i) == IF (i=0) THEN (N-1) ELSE (i-1)
    
    \* Predicate: is the ith fork unused/available?
    forkAvailable(i) == fork[i]=N
end define;

fair process Philopspher \in 0..(N-1)
variable state = "Thinking"; 
begin
loop:
    while (TRUE)
    do
        either
H:          if (state="Thinking")
            then 
                \* Now hungry
                state:="Hungry";
      	    end if;
        or 
P:          if (state="Hungry")
            then
                \* Get right fork
                await(forkAvailable(RightF(self)));
                fork[RightF(self)]:=self;
                \* Get left fork
E:              await(forkAvailable(LeftF(self)));
		        fork[LeftF(self)]:=self;
                \* Now eating
		        state:="Eating";
            end if;
        or 
T:          if (state="Eating")
            then
                \* Return forks and think
                state:="Thinking";
                fork[LeftF(self)]:=N;
R:              fork[RightF(self)]:=N;
            end if;
        end either;
    end while;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "8aff8b59" /\ chksum(tla) = "39e1cb3b")
VARIABLES fork, pc

(* define statement *)
LeftF(i) == i



RightF(i) == IF (i=0) THEN (N-1) ELSE (i-1)


forkAvailable(i) == fork[i]=N

VARIABLE state

vars == << fork, pc, state >>

ProcSet == (0..(N-1))

Init == (* Global variables *)
        /\ fork = [k \in 0..N-1 |-> N]
        (* Process Philopspher *)
        /\ state = [self \in 0..(N-1) |-> "Thinking"]
        /\ pc = [self \in ProcSet |-> "loop"]

loop(self) == /\ pc[self] = "loop"
              /\ \/ /\ pc' = [pc EXCEPT ![self] = "H"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "P"]
                 \/ /\ pc' = [pc EXCEPT ![self] = "T"]
              /\ UNCHANGED << fork, state >>

H(self) == /\ pc[self] = "H"
           /\ IF (state[self]="Thinking")
                 THEN /\ state' = [state EXCEPT ![self] = "Hungry"]
                 ELSE /\ TRUE
                      /\ state' = state
           /\ pc' = [pc EXCEPT ![self] = "loop"]
           /\ fork' = fork

P(self) == /\ pc[self] = "P"
           /\ IF (state[self]="Hungry")
                 THEN /\ (forkAvailable(RightF(self)))
                      /\ fork' = [fork EXCEPT ![RightF(self)] = self]
                      /\ pc' = [pc EXCEPT ![self] = "E"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "loop"]
                      /\ fork' = fork
           /\ state' = state

E(self) == /\ pc[self] = "E"
           /\ (forkAvailable(LeftF(self)))
           /\ fork' = [fork EXCEPT ![LeftF(self)] = self]
           /\ state' = [state EXCEPT ![self] = "Eating"]
           /\ pc' = [pc EXCEPT ![self] = "loop"]

T(self) == /\ pc[self] = "T"
           /\ IF (state[self]="Eating")
                 THEN /\ state' = [state EXCEPT ![self] = "Thinking"]
                      /\ fork' = [fork EXCEPT ![LeftF(self)] = N]
                      /\ pc' = [pc EXCEPT ![self] = "R"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "loop"]
                      /\ UNCHANGED << fork, state >>

R(self) == /\ pc[self] = "R"
           /\ fork' = [fork EXCEPT ![RightF(self)] = N]
           /\ pc' = [pc EXCEPT ![self] = "loop"]
           /\ state' = state

Philopspher(self) == loop(self) \/ H(self) \/ P(self) \/ E(self) \/ T(self)
                        \/ R(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 0..(N-1): Philopspher(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 0..(N-1) : WF_vars(Philopspher(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Tue Nov 24 15:39:56 EST 2020 by smiller
\* Created Sun Nov 08 20:07:06 EST 2020 by smiller
