Inductive Var := m | n | i | x | sum.
Scheme Equality for Var.

(* Environment *)
Definition Env := Var -> nat.
Definition env1 : Env :=
  fun x =>
    if (Var_eq_dec x n)
    then 10
    else 0.
Check env1.

Compute (env1 sum). (* env1(sum) *)

Definition update (env : Env)
           (x : Var) (v : nat) : Env :=
  fun y =>
    if (Var_eq_dec y x)
    then v
    else (env y).

Notation "S [ V /' X ]" := (update S X V) (at level 0).

Definition env2 := env1 [ 1045 /' n ].
Compute (env2 n).

Inductive AExp :=
| avar : Var -> AExp
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| amin : AExp -> AExp -> AExp.

Notation "A +' B" := (aplus A B) (at level 48).
Notation "A -' B" := (amin A B) (at level 47).
Notation "A *' B" := (amul A B) (at level 46).
Coercion anum : nat >-> AExp.
Coercion avar : Var >-> AExp.

Reserved Notation "A =[ S ]=> N" (at level 70).

Inductive aeval : AExp -> Env -> nat -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n (* <n,sigma> => <n> *) 
| var : forall v sigma, avar v =[ sigma ]=> (sigma v) (* <v,sigma> => sigma(x) *)
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 + i2 ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 * i2 ->
    a1 *' a2 =[sigma]=> n
| scadere : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = i1 - i2 ->
    a1 -' a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp.

Notation "A <=' B" := (blessthan A B) (at level 53).
Reserved Notation "B ={ S }=> B'" (at level 70).

Inductive beval : BExp -> Env -> bool -> Prop :=
| e_true : forall sigma, btrue ={ sigma }=> true
| e_false : forall sigma, bfalse ={ sigma }=> false
| e_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = Nat.leb i1 i2 ->
    a1 <=' a2 ={ sigma }=> b
| e_greaterthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = Nat.leb i2 i1 ->
    a1 <=' a2 ={ sigma }=> b
| e_nottrue : forall b sigma,
    b ={ sigma }=> true ->
    (bnot b) ={ sigma }=> false
| e_notfalse : forall b sigma,
    b ={ sigma }=> false ->
    (bnot b) ={ sigma }=> true
| e_andtrue : forall b1 b2 sigma t,
    b1 ={ sigma }=> true ->
    b2 ={ sigma }=> t ->
    band b1 b2 ={ sigma }=> t
| e_andfalse : forall b1 b2 sigma,
    b1 ={ sigma }=> false ->
    band b1 b2 ={ sigma }=> false
where "B ={ S }=> B'" := (beval B S B').

Inductive Stmt :=
| assignment : Var -> AExp -> Stmt
| sequence : Stmt -> Stmt -> Stmt
| while : BExp -> Stmt -> Stmt
| ifthen : BExp -> Stmt -> Stmt -> Stmt.

Notation "X ::= A" := (assignment X A) (at level 50).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 90).


Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).
Check update.
Inductive eval : Stmt -> Env -> Env -> Prop :=
| e_assignment: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x i) ->
    (x ::= a) -{ sigma }-> sigma'
| e_seq : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_ifthenfalse : forall b s1 s2 sigma,
     b ={ sigma }=> false ->
    ifthen b s1 s2 -{ sigma }-> sigma 
| e_ifthentrue : forall b s1 s2 sigma sigma',
     b ={ sigma }=> true ->
    ifthen b s1 s2 -{ sigma }-> sigma'
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').



