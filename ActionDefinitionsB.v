Require Import ActionDefinitions.
Require Import Nat.
Require Import String.
Require Import List.
Require Import Bool.
Require Import ActionStructuralEquality.

Fixpoint list_eq {T:Type}(f:T->T->bool)(ts ts': list T): bool := 
  match ts, ts' with 
  | nil,nil => true
  | t1 :: tss, t2 :: tss' => f t1 t2 && list_eq f tss tss'
  | _,_ => false 
  end.

Definition eqiohb (i1 i2 : ioh) : bool := 
  match i1, i2 with
  | Input,Input => true
  | Output, Output => true
  | Internal, Internal => true
  | _,_ => false
  end.

Definition eqtypesb (t1 t2: types) : bool :=
  match t1, t2 with
  | Boolean, Boolean => true
  | ID, ID => true
  | _,_ => false
  end.

Definition eqdbaccb (db db' : dbacc) :=
  match db, db' with
  | Delete, Delete => true
  | Read, Read => true
  | Create, Create => true
  | Update, Update => true
  | _,_ => false 
  end.

Definition s_equal_depth_iob {t1 t2:ioh} (a:action t1)(b:action t2) : bool :=
  match a,b with 
    | input (inputEvent n ts name tid sid), input (inputEvent n' ts' name' tid' sid') => 
      Nat.eqb n n' && Nat.eqb tid tid' && Nat.eqb sid sid' && String.eqb name name' && 
       list_eq (fun t1 t2 => eqtypesb t1 t2) ts ts'
    | output (outputEvent n pes name tid sid),output (outputEvent n' pes' name' tid' sid') => 
      Nat.eqb n n' && Nat.eqb tid tid' && Nat.eqb sid sid' && String.eqb name name' && 
    list_eq (fun p1 p2 => 
      match p1,p2 with 
      | inl p, inl p' => Nat.eqb p p'
      | inr p, inr p' => Bool.eqb p p'
      | _,_ => false
      end
    ) pes pes'
    | _,_ => false
  end.

Definition s_equalb {t1 t2 :ioh} (a : action t1)(b : action t2) : bool := 
  match a,b with 
  | input (inputEvent n ts name tid sid), input (inputEvent n' ts' name' tid' sid') =>
     Nat.eqb n n' && Nat.eqb tid tid' && Nat.eqb sid sid' && String.eqb name name' && 
       list_eq (fun t1 t2 => eqtypesb t1 t2) ts ts'
  | output (outputEvent n pes name tid sid),output (outputEvent n' pes' name' tid' sid') => 
     Nat.eqb n n' && Nat.eqb tid tid' && Nat.eqb sid sid' && String.eqb name name' && 
    list_eq (fun p1 p2 => 
      match p1,p2 with 
      | inl p, inl p' => Nat.eqb p p'
      | inr p, inr p' => Bool.eqb p p'
      | _,_ => false
      end
    ) pes pes'
  | matches (matchEvent tid sid ai ao eq_proof), matches (matchEvent tid' sid' ai' ao' eq_proof') => 
   Nat.eqb tid tid' && Nat.eqb sid sid' && s_equal_depth_iob (input ai) (input ai') && s_equal_depth_iob (output ao) (output ao')
  | db (dbAccess tid sid op id),db (dbAccess tid' sid' op' id') => 
    Nat.eqb tid tid' && Nat.eqb sid sid' && eqdbaccb op op' && Nat.eqb id id'
  | gu (guard tid sid b),gu (guard tid' sid' b') => 
    Nat.eqb tid tid' && Nat.eqb sid sid' && Bool.eqb b b'
  | _,_ => false
  end.

Lemma list_eq_eq_types : forall l :list types, list_eq (fun t1 t2 : types => eqtypesb t1 t2) l l = true.
Proof.
intros l.
induction l.
- simpl; reflexivity.
- simpl. simpl. apply andb_true_intro. split. 
  + destruct a; simpl; auto.
  + exact IHl.
Qed.

Lemma list_eq_eq_payloads : forall l:list (nat + bool), list_eq
  (fun p1 p2 : nat + bool =>
   match p1 with
   | inl p => match p2 with
              | inl p' => p =? p'
              | inr _ => false
              end
   | inr p => match p2 with
              | inl _ => false
              | inr p' => eqb p p'
              end
   end) l l = true.
Proof.
intros l.
induction l.
  - simpl; reflexivity.
  - simpl. apply andb_true_intro. split.
    + destruct a.
      * auto using PeanoNat.Nat.eqb_refl.
      * auto using eqb_reflx.
    + exact IHl.
Qed.

Lemma s_equalb_refl {t:ioh} : forall (a:action t), s_equalb a a = true.
intros a.
destruct a,a. 
- simpl. Search (_ && _ = true).
  repeat (apply andb_true_intro; split); try auto using PeanoNat.Nat.eqb_refl.
  + auto using String.eqb_refl.
  + auto using list_eq_eq_types.
- simpl. repeat (apply andb_true_intro; split); try auto using PeanoNat.Nat.eqb_refl;
   try auto using String.eqb_refl.
   auto using list_eq_eq_payloads.
- simpl. repeat (apply andb_true_intro; split); try auto using PeanoNat.Nat.eqb_refl.
  + destruct i; repeat (apply andb_true_intro; split); try auto using PeanoNat.Nat.eqb_refl;
   try auto using String.eqb_refl.
   * auto using list_eq_eq_types.
  + destruct o; repeat (apply andb_true_intro; split); try auto using PeanoNat.Nat.eqb_refl;
   try auto using String.eqb_refl.   
   * auto using list_eq_eq_payloads.
- simpl. repeat (apply andb_true_intro; split); try auto using PeanoNat.Nat.eqb_refl.
  destruct d; simpl; auto.
- simpl. repeat (apply andb_true_intro; split); try auto using PeanoNat.Nat.eqb_refl.
  auto using eqb_reflx.
Qed.

Lemma list_eq_app {T : Type} : forall (a a':T)(l l0 : list T), a = a' /\ l = l0 -> (a :: l) = (a' :: l0).  
Proof.
intros a a'.
intros l l0 [H0 H1].
rewrite H0, H1.
reflexivity.
Qed.


Lemma list_eq_eqtypes_impl_true : forall (l l0 : list types), list_eq (fun t1 t2 : types => eqtypesb t1 t2) l l0 = true -> l = l0. 
Proof.
induction l.
- intros l0 H.
  + destruct l0.
    * trivial.
    * inversion H.
- intros l0 H.
  + destruct l0.
    * inversion H.
    * inversion H. apply (list_eq_app).
      apply andb_prop in H; destruct H as [A0 A1].
      split.
      ** destruct a,t; try reflexivity; inversion A0.
      ** exact (IHl l0 A1).
Qed. 

Lemma list_eq_nat_bool_impl_true : forall (l l0:list(nat + bool)), list_eq (fun p1 p2 => 
      match p1,p2 with 
      | inl p, inl p' => Nat.eqb p p'
      | inr p, inr p' => Bool.eqb p p'
      | _,_ => false
      end
    ) l l0 = true -> l = l0. 
Proof.
induction l.
- intros l0 H.
  + simpl in H. destruct l0; try trivial; inversion H. 
- intros l0 H. destruct l0. 
  + inversion H.
  + apply list_eq_app. inversion H.
    apply andb_prop in H1; destruct H1 as [A0 A1].
    clear H.
    split.
    * destruct a, s.
      ** apply EqNat.beq_nat_true_stt in A0. rewrite A0. reflexivity.
      ** inversion A0.
      ** inversion A0.
      ** apply eqb_prop in A0. rewrite A0. reflexivity.
    * destruct a, s; try (apply IHl; exact A1); inversion A1.
Qed.

Lemma eqdbaccb_prop : forall (d d' : dbacc), (eqdbaccb d d' = true ) -> d = d'.    
Proof.
intros d d' H.
destruct d,d'; try reflexivity; inversion H.
Qed.

Lemma s_equal_brefl {t1 t2 : ioh} : forall (a:action t1)(b:action t2), a =s= b <-> (s_equalb a b = true).
Proof.
intros a b.
split.
- destruct a, b, a0, a; intros H; try (simpl in H; contradiction); simpl in H; try(
  destruct H as [H0 [H1 [H2 [H3 H4]]]]; 
  subst; auto using s_equalb_refl).
  + destruct i0,i,o0,o. destruct H as [H0 [H1 [[H2 [H3 [H4 [H5 H6]]]] [H7 [H8 [H9 [H10 H11]]]]]]].
    simpl. subst. repeat (apply andb_true_intro; split); try auto using PeanoNat.Nat.eqb_refl;
   try auto using String.eqb_refl; try auto using list_eq_eq_payloads; try auto using list_eq_eq_types.
  + destruct H as [H0 [H1 [H2 H3]]]. simpl. subst. repeat (apply andb_true_intro; split); try auto using PeanoNat.Nat.eqb_refl.
    destruct d; simpl; auto.
  + destruct H as [H0 [H1 H2]]. simpl. subst. repeat (apply andb_true_intro; split); try auto using PeanoNat.Nat.eqb_refl.
    auto using eqb_reflx.
- intros H.
  destruct a,b; destruct a, a0; inversion H; clear H.
  + apply andb_prop in H1; destruct H1 as [H1 H2].
    apply andb_prop in H1; destruct H1 as [H1 H3].
    apply andb_prop in H1; destruct H1 as [H1 H4].
    apply andb_prop in H1; destruct H1 as [H1 H5].
    simpl; repeat (split; auto using EqNat.beq_nat_true_stt). 
    * auto using list_eq_eqtypes_impl_true.
    * apply String.eqb_eq; auto.
  +  apply andb_prop in H1; destruct H1 as [H1 H2].
     apply andb_prop in H1; destruct H1 as [H1 H3].
    apply andb_prop in H1; destruct H1 as [H1 H4].
    apply andb_prop in H1; destruct H1 as [H1 H5].
    simpl; repeat (split; auto using EqNat.beq_nat_true_stt).
    * apply String.eqb_eq; auto.
    * auto using list_eq_nat_bool_impl_true. 
  + destruct i,o,i0,o0. simpl.
    apply andb_prop in H1; destruct H1 as [H1 H2].
    apply andb_prop in H1; destruct H1 as [H1 H3].
    apply andb_prop in H1; destruct H1 as [H1 H4].
    apply andb_prop in H3; destruct H3 as [H3 H5].
    apply andb_prop in H3; destruct H3 as [H3 H6].
    apply andb_prop in H3; destruct H3 as [H3 H7].
    apply andb_prop in H3; destruct H3 as [H3 H8].
    apply andb_prop in H2; destruct H2 as [H2 H9]. 
    apply andb_prop in H2; destruct H2 as [H2 H10].
    apply andb_prop in H2; destruct H2 as [H2 H11].
    apply andb_prop in H2; destruct H2 as [H2 H12].
    apply EqNat.beq_nat_true_stt in H1,H4, H3, H8, H7, H2, H12, H11.
    apply String.eqb_eq in H6, H10.
    apply list_eq_nat_bool_impl_true in H9.
    apply list_eq_eqtypes_impl_true in H5.
    repeat (split; eauto using eq_trans).
  + apply andb_prop in H1; destruct H1 as [H1 H2].
    apply andb_prop in H1; destruct H1 as [H1 H3].
    apply andb_prop in H1; destruct H1 as [H1 H4].
    apply EqNat.beq_nat_true_stt in H1, H4, H2.
    apply eqdbaccb_prop in H3.
    simpl; repeat (split; auto).
  + apply andb_prop in H1; destruct H1 as [H1 H2].
    apply andb_prop in H1; destruct H1 as [H1 H3].
    apply eqb_prop in H2.
    apply EqNat.beq_nat_true_stt in H1, H3. 
    simpl; repeat (split; auto).
Qed.

Notation "A =s?= B" := (s_equalb A B)(at level 25, left associativity).

Fixpoint eq_types_payloadsb (l:list types)(l':list (nat + bool)) : bool := 
  match l,l' with 
    | ID :: ts, (inl _) :: vs => eq_types_payloadsb ts vs 
    | Boolean :: ts, (inr _) :: vs => eq_types_payloadsb ts vs
    | nil,nil => true 
    | _,_ => false
  end.

Definition eq_in_outb (i:actionInput)(o:actionOutput) := 
  match i,o with
  | (inputEvent n ts name tid sid),(outputEvent n' pes' name' tid' sid') => 
    (n =? n')%nat && (name =? name')%string && (tid =? tid')%nat && (sid =? sid')%nat && eq_types_payloadsb ts pes'
  end
.

Notation "A =io?= B" := (eq_in_outb A B)(at level 25, left associativity).

Fixpoint eq_sig_pl_plb (l:list (nat + bool))(l':list (nat + bool)) : bool := 
  match l,l' with 
    | ((inl _) :: ls) ,((inl _) :: ls' ) => eq_sig_pl_plb ls ls'
    | ((inr _) :: ls) ,((inr _) :: ls' ) => eq_sig_pl_plb ls ls'
    | nil,nil => true
    | _,_ => false 
  end.

Definition sig_eq_actionsb (a:action Output)(b:action Output) : bool := 
  match a,b with 
    | output (outputEvent n vs name tid sid),output (outputEvent n' vs' name' tid' sid') =>
      (n=?n')%nat && (name=?name')%string && (tid=?tid')%nat && (sid=?sid')%nat && eq_sig_pl_plb vs vs'
    | _,_ => false
  end.

Notation "A <-o?-> B" := (sig_eq_actionsb A B)(at level 25, left associativity).

Definition equiv_actb {t1 t2:ioh}(a:action t1)(b:action t2) : bool :=
  a =s?= b || 
  ( match a,b with 
  | input (a_internal), output (b_internal) => a_internal =io?= b_internal
  | output (a_internal), input (b_internal) => b_internal =io?= a_internal
  | output (_) as a', output (_) as b' => a'<-o?-> b'
  (* p' is carried here, because for the transitivity proof we need to know the i' is input output equal to o' *)
  | matches (matchEvent tid sid i o p), matches (matchEvent tid' sid' i' o' p') =>
      ((input i) =s?= (input i') || i =io?= o') || ((output o) =s?= (output o') || i' =io?= o || (output o) <-o?-> (output o'))
  | matches (matchEvent tid sid i o p), input i' => (input i') =s?= (input i) || i' =io?= o
  | input i, matches (matchEvent tid sid i' o' p) => (input i) =s?= (input i') || i =io?= o'
  | matches (matchEvent tid sid i o p), output o' => output o =s?= output o' || output o <-o?-> output o' || i =io?= o'
  | output o, matches (matchEvent tid sid i' o' p) => output o =s?= output o' || output o <-o?-> output o' || i' =io?= o
  | _,_ => false
  end
  )
.

Notation "A <--?> B" := (equiv_actb A B)(at level 25, left associativity).

Theorem eq_types_payloadsb_refl : forall (l : list types)(l' : list (nat + bool)), eq_types_payloadsb l l' = true <-> eq_types_payloads l l'.
Proof.
induction l.
- intros l'. split.
  -- intros H. destruct l'.
    --- simpl; trivial.
    --- inversion H.
  -- intros H. destruct l'.
    --- simpl; trivial.
    --- inversion H.
- intros l'; split.
  -- intros H. destruct l',a.
    --- inversion H.
    --- inversion H.
    --- destruct s.
      + inversion H.
      + simpl in *. apply IHl in H. trivial.
    --- destruct s.
      + simpl in *. apply IHl in H. trivial.
      + inversion H.
  -- intros H. destruct l',a.
    --- inversion H.
    --- inversion H.
    --- destruct s.
      + inversion H.
      + simpl in *; apply IHl in H; trivial.
    --- destruct s.
      + simpl in *; apply IHl in H; trivial.
      + inversion H.
Qed.


Theorem eq_in_outb_refl : forall (a:actionInput)(b:actionOutput), a =io?= b = true <-> a =io= b.
Proof.
intros a b.
split.
- intros H. destruct a,b. simpl in *. 
  apply andb_prop in H; destruct H as [H H1].
  apply andb_prop in H; destruct H as [H H2].
  apply andb_prop in H; destruct H as [H H3].
  apply andb_prop in H; destruct H as [H H4].
  apply EqNat.beq_nat_true_stt in H, H3, H2.
  apply String.eqb_eq in H4.
  apply eq_types_payloadsb_refl in H1.
  repeat( split; trivial).
- intros H. destruct a,b. simpl in *.
  destruct H as [H0 [H1 [H2 [H3 H4]]]].
  repeat (apply andb_true_intro; split); 
  try eauto using PeanoNat.Nat.eqb_refl.
  apply String.eqb_eq. auto.
  apply eq_types_payloadsb_refl. auto.
Qed.
  
Require Import Coq.Program.Equality.

Lemma eq_sig_pl_plb_refl : forall (l l' : list (nat + bool)), eq_sig_pl_plb l l' = true <-> eq_sig_pl_pl l l'.
Proof.
induction l.
- intros l'. split. 
  -- intros H. destruct l'.
    + simpl; trivial.
    + inversion H.
  -- intros H. destruct l'.
    + simpl; trivial.
    + simpl in H; contradiction.
- intros l'. split; intros H; destruct l'.
    + simpl in H. destruct a; inversion H.
    + destruct a,s; try ( inversion H); simpl in *; apply IHl; auto.
    + simpl in H. destruct a; inversion H.
    + destruct a,s; try ( inversion H); simpl in *; apply IHl; auto.
Qed.

Theorem sig_eq_actionsb_refl : forall (a b : action Output), a <-o?-> b = true <-> a <-o-> b.
Proof.
intros a b.
split.
- intros H. dependent destruction a. dependent destruction b.
  destruct a,a0. simpl in *.
  apply andb_prop in H; destruct H as [H H1].
  apply andb_prop in H; destruct H as [H H2].
  apply andb_prop in H; destruct H as [H H3].
  apply andb_prop in H; destruct H as [H H4].
  apply EqNat.beq_nat_true_stt in H,H3,H2.
  apply String.eqb_eq in H4.
  apply eq_sig_pl_plb_refl in H1.
  repeat (split; auto).
- intros H. dependent destruction a. dependent destruction b.
  destruct a,a0. simpl in *.
  destruct H as [H [H1 [H2 [H3 H4]]]].
  repeat (apply andb_true_intro; split);
  try eauto using PeanoNat.Nat.eqb_refl.
  apply String.eqb_eq. auto.
  apply eq_sig_pl_plb_refl. auto.
Qed.
  

Theorem equiv_actb_refl {t1 t2 : ioh} : forall (a:action t1)(b:action t2), a <--?> b = true <-> a <--> b.
Proof.
intros a b.
split.
- destruct a,b; try (
    intros H; unfold "<--?>" in H; apply orb_prop in H; destruct H as [H|H];
      try (simpl in H; destruct a; inversion H); inversion H
    ).
  + destruct a0. left.
    apply s_equal_brefl; trivial.
  + right. apply eq_in_outb_refl. auto.
  + right. destruct a0. destruct i. apply orb_prop in H. destruct H as [H|H].
    ++ left. apply s_equal_brefl. exact H.
    ++ right. apply eq_in_outb_refl. exact H.
  + right. apply eq_in_outb_refl; trivial.
  + left. destruct a0. apply s_equal_brefl. exact H2.
  + right; destruct a0. apply sig_eq_actionsb_refl. exact H.
  + destruct a0. destruct o. apply orb_prop in H2. clear H H1. destruct H2 as [H2| H2].
    ++ apply orb_prop in H2. destruct H2 as [H2|H2].
      +++ right. left. apply s_equal_brefl. exact H2.
      +++ right. right; left. apply sig_eq_actionsb_refl. exact H2.
    ++ right; right; right. apply eq_in_outb_refl. auto.
  + right. destruct a0. destruct i. apply orb_prop in H2. clear H1 H. destruct H2 as [H|H].
    ++ left. apply s_equal_brefl. auto.
    ++ right; apply eq_in_outb_refl. auto.
  + destruct o; destruct a0. clear H1 H2. apply orb_prop in H. destruct H as [H|H].
    ++ apply orb_prop in H. destruct H as [H|H].
      +++ right. left. apply s_equal_brefl. auto.
      +++ right. right; left. apply sig_eq_actionsb_refl. auto.
    ++ right; right; right. apply eq_in_outb_refl. auto.
  + clear H1 H2. destruct a0,i,i0. destruct o,o0. left. apply s_equal_brefl. auto.
  + destruct a0, i, o. destruct i0,o0. clear H1 H2. repeat (apply orb_prop in H; destruct H as [H|H]).
    ++ right. left. left. apply s_equal_brefl. auto.
    ++ right. left. right. apply eq_in_outb_refl. auto.
    ++ right; right; left. apply s_equal_brefl. auto.
    ++ right; right; right; left. apply eq_in_outb_refl. auto.
    ++ right; right; right; right. apply sig_eq_actionsb_refl. auto.
  + clear H1 H2. destruct a0. left.
    apply s_equal_brefl. auto.
  + clear H1 H2. destruct a0. left.
    apply s_equal_brefl. auto.
- intros H; destruct a,b; destruct a, a0; unfold "<--?>"; unfold "<-->" in  H; destruct H as [H|H]; try contradiction.   
  + apply orb_true_intro; left.
    apply s_equal_brefl; auto.
  + apply orb_true_intro.  simpl in H.
    right; apply eq_in_outb_refl; auto.
  + destruct H as [H|H]. 
    ++ apply orb_true_intro; right. apply orb_true_intro; left. apply s_equal_brefl; auto.
    ++ repeat (apply orb_true_intro; right). apply eq_in_outb_refl; auto.
  + apply orb_true_intro; right; apply eq_in_outb_refl; auto.
  + apply orb_true_intro; left; apply s_equal_brefl; auto.
  + apply orb_true_intro; right; apply sig_eq_actionsb_refl; auto.
  + destruct H as [H | [H|H]].
    ++ apply orb_true_intro; right; apply orb_true_intro; left; apply orb_true_intro; left; apply s_equal_brefl; auto.
    ++ apply orb_true_intro; right; apply orb_true_intro; left; apply orb_true_intro; right. apply sig_eq_actionsb_refl; auto.
    ++ apply orb_true_intro. right; apply orb_true_intro. right; apply eq_in_outb_refl; auto.
  + destruct H as [H|H].
    ++ apply orb_true_intro; right; apply orb_true_intro; left; apply s_equal_brefl; auto.
    ++ apply orb_true_intro; right; apply orb_true_intro; right; apply eq_in_outb_refl; auto. 
  + destruct H as [H | [H|H]].
    ++ apply orb_true_intro; right; apply orb_true_intro; left; apply orb_true_intro; left.  apply s_equal_brefl; auto.
    ++ apply orb_true_intro; right; apply orb_true_intro; left; apply orb_true_intro; right. apply sig_eq_actionsb_refl; auto.
    ++ apply orb_true_intro; right; apply orb_true_intro; right; apply eq_in_outb_refl; auto.
  + apply orb_true_intro; left; apply s_equal_brefl; auto.
  + destruct H as [[H|H]|[H|[H|H]]].
    ++ apply orb_true_intro; right; apply orb_true_intro; left; apply orb_true_intro; left. apply s_equal_brefl; auto.
    ++ apply orb_true_intro; right; apply orb_true_intro; left; apply orb_true_intro; right. apply eq_in_outb_refl; auto.
    ++ apply orb_true_intro; right; apply orb_true_intro; right; apply orb_true_intro; left; apply orb_true_intro; left;
       apply s_equal_brefl; auto.
    ++ apply orb_true_intro; right; apply orb_true_intro; right; apply orb_true_intro; left; apply orb_true_intro; right;
       apply eq_in_outb_refl; auto.
    ++ apply orb_true_intro; right; apply orb_true_intro; right; apply orb_true_intro; right. apply sig_eq_actionsb_refl; auto.
  + apply orb_true_intro; left; apply s_equal_brefl; auto.
  + apply orb_true_intro; left; apply s_equal_brefl; auto.
Qed.
