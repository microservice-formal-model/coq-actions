Require Import String.
Require Import List.

Inductive types : Set := 
| Boolean : types
| ID : types
.

Inductive ioh : Set :=
| Input : ioh
| Output : ioh
| Internal : ioh
.

Inductive actionInput : Type :=
| inputEvent: nat -> list types -> string -> nat -> nat -> actionInput
.

Inductive actionOutput : Type :=
| outputEvent : nat -> list (nat + bool) -> string -> nat -> nat -> actionOutput
.

Fixpoint eq_types_payloads (l:list types)(l':list (nat + bool)) : Prop := 
  match l,l' with 
    | ID :: ts, (inl _) :: vs => eq_types_payloads ts vs 
    | Boolean :: ts, (inr _) :: vs => eq_types_payloads ts vs
    | nil,nil => True 
    | _,_ => False
  end.

Definition eq_in_out (i:actionInput)(o:actionOutput) := 
  match i,o with
  | (inputEvent n ts name tid sid),(outputEvent n' pes' name' tid' sid') => 
    n=n' /\ name=name' /\ tid=tid' /\ sid=sid' /\ eq_types_payloads ts pes'
  end
.

Notation "A =io= B" := (eq_in_out A B)(at level 25, left associativity).

Inductive actionMatch : Type :=
| matchEvent : forall (tid sid : nat)(i : actionInput)(o: actionOutput), i =io= o -> actionMatch
.

Inductive dbacc : Set := 
| Delete : dbacc
| Read : dbacc 
| Create : dbacc
| Update : dbacc 
.

Inductive actionDB : Type := 
| dbAccess : nat -> nat -> dbacc -> nat -> actionDB
.

Inductive actionGuard : Type :=
| guard : nat -> nat -> bool -> actionGuard
.

Inductive action : ioh -> Type := 
| input : actionInput -> action Input
| output: actionOutput -> action Output
| matches : actionMatch -> action Internal
| db : actionDB -> action Internal
| gu : actionGuard -> action Internal
.

Definition s_equal_depth_io {t1 t2:ioh} (a:action t1)(b:action t2) : Prop :=
  match a,b with 
    | input (inputEvent n ts name tid sid), input (inputEvent n' ts' name' tid' sid') => 
      n=n' /\ ts = ts' /\ name=name' /\ tid = tid' /\ sid = sid'
    | output (outputEvent n pes name tid sid),output (outputEvent n' pes' name' tid' sid') => 
      n = n' /\ tid = tid' /\ sid = sid' /\ name = name' /\ pes = pes'
    | _,_ => False
  end.


Definition s_equal {t1 t2:ioh} (a:action t1)(b:action t2) : Prop :=
  match a,b with 
    | input (inputEvent n ts name tid sid), input (inputEvent n' ts' name' tid' sid') => 
      n=n' /\ ts = ts' /\ name=name' /\ tid = tid' /\ sid = sid'
    | output (outputEvent n pes name tid sid),output (outputEvent n' pes' name' tid' sid') => 
      n = n' /\ tid = tid' /\ sid = sid' /\ name = name' /\ pes = pes'
    | matches (matchEvent tid sid ai ao eq_proof), matches (matchEvent tid' sid' ai' ao' eq_proof') => 
      tid = tid' /\ sid = sid' /\ s_equal_depth_io (input ai) (input ai') /\ s_equal_depth_io (output ao) (output ao')
    | db (dbAccess tid sid op id),db (dbAccess tid' sid' op' id') => 
      tid=tid'/\sid=sid'/\op=op'/\id=id'
    | gu (guard tid sid b),gu (guard tid' sid' b') => 
      tid=tid'/\sid=sid'/\b=b'
    | _,_ => False
  end.

Notation "A =s= B" := (s_equal A B)(at level 25, left associativity).

Fixpoint eq_sig_pl_pl (l:list (nat + bool))(l':list (nat + bool)) : Prop := 
  match l,l' with 
    | ((inl _) :: ls) ,((inl _) :: ls' ) => eq_sig_pl_pl ls ls'
    | ((inr _) :: ls) ,((inr _) :: ls' ) => eq_sig_pl_pl ls ls'
    | nil,nil => True
    | _,_ => False 
  end.

Definition sig_eq_actions (a:action Output)(b:action Output) : Prop := 
  match a,b with 
    | output (outputEvent n vs name tid sid),output (outputEvent n' vs' name' tid' sid') =>
      n=n' /\ name=name' /\ tid=tid' /\ sid=sid' /\ eq_sig_pl_pl vs vs'
    | _,_ => False
  end.

Notation "A <-o-> B" := (sig_eq_actions A B)(at level 25, left associativity).

Definition equiv_act {t1 t2:ioh}(a:action t1)(b:action t2) : Prop :=
  a =s= b \/ 
  ( match a,b with 
  | input (a_internal), output (b_internal) => a_internal =io= b_internal
  | output (a_internal), input (b_internal) => b_internal =io= a_internal
  | output (_) as a', output (_) as b' => a'<-o-> b'
  (* p' is carried here, because for the transitivity proof we need to know the i' is input output equal to o' *)
  | matches (matchEvent tid sid i o p), matches (matchEvent tid' sid' i' o' p') =>
      ((input i) =s= (input i') \/ i =io= o') \/ ((output o) =s= (output o') \/ i' =io= o \/ (output o) <-o-> (output o'))
  | matches (matchEvent tid sid i o p), input i' => (input i') =s= (input i) \/ i' =io= o
  | input i, matches (matchEvent tid sid i' o' p) => (input i) =s= (input i') \/ i =io= o'
  | matches (matchEvent tid sid i o p), output o' => output o =s= output o' \/ output o <-o-> output o' \/ i =io= o'
  | output o, matches (matchEvent tid sid i' o' p) => output o =s= output o' \/ output o <-o-> output o' \/ i' =io= o
  | _,_ => False
  end
  )
.

Notation "A <--> B" := (equiv_act A B)(at level 25, left associativity).














