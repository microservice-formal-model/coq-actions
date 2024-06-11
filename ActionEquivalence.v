Require Import ActionDefinitions.
Require Import ActionStructuralEquality.

Require Import Program.
Require Import String.

Theorem eq_in_out_input_swap : forall (i i':actionInput)(o:actionOutput),
  input i' =s= input i /\ i =io= o ->  i' =io= o.
Proof.
intros i i' o. 
destruct i,i',o.
intros [H H0].
simpl in *.
destruct H0 as [A1 [A2 [A3 [A4 A5]]]].
destruct H as [B1 [B2 [B3 [B4 B5]]]].
repeat (split; eauto using eq_trans).
subst; auto.
Qed.

Theorem eq_in_out_output_swap : forall (i : actionInput)(o o' : actionOutput),
  output o =s= output o' /\ i =io= o -> i =io= o'.
Proof.
intros o o' i.
dependent destruction o; dependent destruction o'; dependent destruction i.
intros [H H0].
simpl in *.
destruct H0 as [A1 [A2 [A3 [A4 A5]]]].
destruct H as [B1 [B2 [B3 [B4 B5]]]].
repeat (split; eauto using eq_trans).
subst; auto.
Qed.

Lemma eq_sig_pl_pl_sym : forall (l l' : list (nat + bool)), eq_sig_pl_pl l l' -> eq_sig_pl_pl l' l.
Proof.
induction l.
- induction l'. 
  + eauto.
  + intros. destruct a; simpl in H; contradiction. 
- induction l'.
  + intros. simpl in H. destruct a; contradiction.
  + intros. destruct a,a0;(simpl in *; exact (IHl l' H) || simpl in H; contradiction). 
Qed.

Lemma type_payloads_impl_sig : forall (ts : list types)(pes pes' : list (nat + bool)), 
  eq_types_payloads ts pes /\ eq_types_payloads ts pes' -> eq_sig_pl_pl pes pes'.
Proof.
induction ts.
- destruct pes; destruct pes'; intros [H H0];
  try (simpl in H0; contradiction); try (simpl in H1; contradiction).
  + simpl in *. trivial.
- destruct pes; destruct pes'; intros [H H0]; destruct a; try (simpl in H; simpl in H0; contradiction);
    simpl in H; destruct s; try contradiction;
    simpl in H0; destruct s0; try contradiction;
    simpl; eauto using IHts.
Qed.
   
    

Theorem eq_in_eq_in_sig_trans : forall (a : actionInput)(b c: actionOutput), a =io= b /\ a =io= c -> output b <-o-> output c.
Proof.
intros a b c [H H0].
dependent destruction a; dependent destruction b; dependent destruction c.
simpl in *.
destruct H0 as [A1 [A2 [A3 [A4 A5]]]].
destruct H as [B1 [B2 [B3 [B4 B5]]]].
repeat (split; eauto using eq_trans,type_payloads_impl_sig).
Qed.

Theorem s_equal_sig_eq_out_impl_sig_eq_out : forall (a b c : action Output),
      a =s= b /\ b <-o-> c -> a <-o-> c.
intros a b c [H H0].
dependent destruction a; dependent destruction b; dependent destruction c.
dependent destruction a; dependent destruction a0; dependent destruction a1.
simpl in *.
destruct H0 as [A1 [A2 [A3 [A4 A5]]]].
destruct H as [B1 [B2 [B3 [B4 B5]]]].
repeat (split; eauto using eq_trans).
subst; auto.
Qed.

Lemma eq_types_payloads_eq : forall (lt lt':list types)(lp:list (nat+bool)), eq_types_payloads lt lp /\ eq_types_payloads lt' lp -> lt = lt'.
Proof.
induction lt.
- destruct lt'.
  + eauto.
  + intros lp [H0 H1]. exfalso. destruct lp; eauto. simpl in H1; destruct t; contradiction.
- induction lt'.
  + induction lp. 
    * intros [H0 H1]. simpl in H0; destruct a; contradiction.
    * intros [H0 H1]. simpl in H1; contradiction.
  + induction lp.
    * intros [H0 H1]. simpl in H1; destruct a0; contradiction.
    *  intros [H0 H1]. destruct a1,a0,a; try (simpl in H0; contradiction || simpl in H1; contradiction).
      ** f_equal. simpl in H0,H1. apply (IHlt lt' lp). eauto.
      ** f_equal. simpl in H0,H1. apply (IHlt lt' lp). eauto.
Qed.


Lemma eq_types_payloads_sig_pl_pl_trans : forall (tl: list types)(pl pl':list (nat + bool)), eq_types_payloads tl pl /\ eq_sig_pl_pl pl pl' -> eq_types_payloads tl pl'.
Proof.
induction tl.
- intros pl pl' [H0 H1]. destruct pl; destruct pl'; simpl in *; auto || contradiction.
- intros pl pl' [H0 H1]. destruct pl,pl'; simpl in H0,H1; destruct a; 
   try ( contradiction || destruct s; ( contradiction || destruct s0; try contradiction; simpl; eauto using IHtl)).
Qed.

Theorem eq_io_sig_eq_impl_io_eq : forall (a : actionInput)(b c : actionOutput),
  a =io= b /\ output b <-o-> output c -> a =io= c. 
Proof.
intros a b c.
dependent destruction a; dependent destruction b; dependent destruction c.
intros [H0 H1].
simpl in *.
destruct H0 as [A1 [A2 [A3 [A4 A5]]]].
destruct H1 as [B1 [B2 [B3 [B4 B5]]]].
repeat (split; eauto using eq_trans, eq_types_payloads_sig_pl_pl_trans).
Qed.

Theorem eq_sig_sym : forall (a b:action Output), a <-o-> b -> b <-o-> a.
Proof.
intros a b H.
dependent destruction a; dependent destruction b.
simpl in *.
dependent destruction a.
dependent destruction a0.
destruct H as [A1 [A2 [A3 [A4 A5]]]].
repeat (split; eauto using eq_sig_pl_pl_sym).
Qed.

Lemma eq_sig_pl_pl_refl : forall (pes : list( nat + bool)), eq_sig_pl_pl pes pes.
Proof.
induction pes.
- simpl; auto.
- destruct a; simpl; eauto using IHpes.
Qed.

Lemma eq_impl_sig_pl_pl_eq : forall (pes pes' : list (nat + bool)), pes = pes' -> eq_sig_pl_pl pes pes'.
Proof.
intros pes pes' H.
destruct pes.
destruct pes'.
- simpl. trivial.
- discriminate H.
- subst; eauto using eq_sig_pl_pl_refl.
Qed.

Theorem s_eql_swap_output_sig : forall (a b c: action Output), a <-o-> b /\ b =s= c -> a <-o-> c.
Proof.
intros a b c [H0 H1].
dependent destruction a; dependent destruction b; dependent destruction c.
dependent destruction a; dependent destruction a0; dependent destruction a1.
simpl in *.
destruct H0 as [A1 [A2 [A3 [A4 A5]]]].
destruct H1 as [B1 [B2 [B3 [B4 B5]]]].
repeat (split; eauto using eq_trans).
subst; auto.
Qed.

Lemma eq_sig_pl_pl_trans : forall  (a b c: list (nat + bool)), eq_sig_pl_pl a b /\ eq_sig_pl_pl b c -> eq_sig_pl_pl a c.
Proof.
induction a.
- intros b c [H0 H1]. destruct b.
  + destruct c; trivial.
  + destruct c; trivial; simpl in H0; contradiction.
- destruct b.
  + destruct c; intros [H0 H1]; simpl in H0; destruct a; contradiction.
  + destruct c; intros [H0 H1]; try (simpl in H1; destruct s; contradiction).
    destruct a,s,s0; simpl in *; try (eauto using IHa); try (contradiction).
Qed.

Theorem sig_pl_pl_eq_trans : forall (a b c : action Output), a <-o-> b /\ b <-o-> c -> a <-o-> c.
Proof.
intros a b c [H0 H1].
dependent destruction a; dependent destruction b; dependent destruction c.
dependent destruction a; dependent destruction a0; dependent destruction a1.
simpl in *.
destruct H0 as [A1 [A2 [A3 [A4 A5]]]].
destruct H1 as [B1 [B2 [B3 [B4 B5]]]].
repeat (split; eauto using eq_trans, eq_sig_pl_pl_trans).
Qed.

Theorem eq_io_trans_s_equal : forall (a c : actionInput)(o : actionOutput), a =io= o /\ c =io= o -> input a =s= input c.
Proof.
intros a c o [H0 H1].
dependent destruction a; dependent destruction o; dependent destruction c.
simpl in *.
destruct H0 as [A1 [A2 [A3 [A4 A5]]]].
destruct H1 as [B1 [B2 [B3 [B4 B5]]]].
repeat (split; eauto using eq_trans,eq_types_payloads_eq).
Qed.

Lemma match_input_eq : forall (a b i': actionInput)(tid sid sid' tid' : nat)(o o':actionOutput)(e:b =io= o)(e': i' =io= o'),
  input a =s= input b /\ matches ( matchEvent tid sid b o e) =s= matches (matchEvent tid' sid' i' o' e') ->
    input a =s= input i'.
Proof.
intros a b i' tid sid sid' tid' o o' e e' [H0 H1].
destruct a; destruct b. destruct i'.
simpl in H0,H1. 
destruct H0 as [A1 [A2 [A3 [A4 A5]]]], H1 as [_ [_ [H1 _]]].
destruct H1 as [B1 [B2 [B3 [B4 B5]]]].
simpl.
repeat (split; eauto using eq_trans).
Qed.

Lemma match_input_eq_out : forall (a b i': actionInput)(tid sid sid' tid' : nat)(o o':actionOutput)(e:b =io= o)(e': i' =io= o'),
  a =io= o /\ matches ( matchEvent tid sid b o e) =s= matches (matchEvent tid' sid' i' o' e') ->
    a =io= o'.
intros a b i' tid sid sid' tid' o o' e e' [H0 H1].
destruct a. destruct o. destruct o'.
simpl in H0,H1. 
destruct H0 as [A1 [A2 [A3 [A4 A5]]]], H1 as [_ [_ [_ H1]]].
destruct H1 as [B1 [B2 [B3 [B4 B5]]]].
repeat (split; eauto using eq_trans).
subst. auto.
Qed.

Lemma match_output_eq : forall (i i': actionInput)(tid sid sid' tid' : nat)(a b o':actionOutput)(e:i =io= b)(e': i' =io= o'),
  output a =s= output b /\ matches ( matchEvent tid sid i b e) =s= matches (matchEvent tid' sid' i' o' e') ->
    output a =s= output o'.
Proof.
intros i i' tid sid sid' tid' a b o' e e' [H0 H1].
destruct a; destruct b; destruct o'.
simpl in H0,H1. 
destruct H0 as [A1 [A2 [A3 [A4 A5]]]], H1 as [_ [_ [_ [H1 H2]]]].
destruct H2 as [B1 [B2 [B3 B4]]].
simpl.
repeat (split; eauto using eq_trans).
Qed.

Lemma match_output_sig_eq : forall (i i': actionInput)(tid sid sid' tid' : nat)(a b o':actionOutput)(e:i =io= b)(e': i' =io= o'),
  output a <-o-> output b /\ matches ( matchEvent tid sid i b e) =s= matches (matchEvent tid' sid' i' o' e') ->
    output a <-o-> output o'.
Proof.
intros i i' tid sid sid' tid' a b o' e e' [H0 H1].
destruct a; destruct b; destruct o'.
simpl in H0,H1. 
destruct H0 as [A1 [A2 [A3 [A4 A5]]]], H1 as [_ [_ [_ [H1 H2]]]].
destruct H2 as [B1 [B2 [B3 B4]]].
simpl.
repeat (split; eauto using eq_trans).
subst; trivial.
Qed.

Lemma s_equal_impl_sig_eq : forall (a b : action Output), a =s= b -> a <-o-> b.
Proof.
intros a b H.
dependent destruction a; dependent destruction b.
destruct a,a0. 
simpl in *.
destruct H as [A1 [A2 [A3 [A4 A5]]]].
repeat (split; auto).
subst.
induction l0.
- simpl. trivial.
- destruct a; simpl; eauto using IHl0.
Qed.

Lemma matches_impl : forall (tid0 tid sid0 sid : nat)(i0 i: actionInput)(o0 o:actionOutput)(e0: i0 =io= o0)(e:i =io= o),
  matches (matchEvent tid0 sid0 i0 o0 e0) =s= matches (matchEvent tid sid i o e) -> input i0 =s= input i /\ output o0 =s= output o.
Proof.
intros tid tid' sid sid' i i' o o' e e'.
intros H.
split.
- destruct i,i'. simpl in *. destruct H as [_ [_ [H _]]]. auto.
- destruct o,o'. simpl in *. destruct H as [_ [_ [_ H]]]. auto.
Qed.

Ltac destruct_equiv_name H_name H a0 a1 :=
  unfold "<-->" in H;
  match type of H with
  | ?A \/ ?B \/ ?C =>  destruct H as [H_name|[H_name|H_name]]
  | ?A \/ ?B => destruct H as [H_name|H_name]
  end;
  try (simpl in H_name; destruct a0,a1; contradiction);
  try (contradiction).

Ltac destruct_abc Name_ab Name_bc H_ab H_bc a a0 a1 :=
  destruct_equiv_name Name_ab H_ab a a0;
  destruct_equiv_name Name_bc H_bc a0 a1.

Lemma match_match_impl_match_out : forall (tid tid1 sid sid1 : nat) (o o1 : actionOutput)(i i1 : actionInput)(e:i =io= o)(e1:i1 =io= o1), 
  matches (matchEvent tid sid i o e) <--> matches (matchEvent tid1 sid1 i1 o1 e1) -> matches (matchEvent tid sid i o e) <--> output o1.
Proof.
intros.
destruct H as [H|H].
- right. simpl in H. destruct H as [_ [_ [H _]]].
  destruct i ,i1. destruct H as [H0 [H1 [H2 [H3 H4]]]]. subst. 
  right; left. eauto using (eq_in_eq_in_sig_trans).
- destruct H as [[H|H]|[H|[H|H]]]; 
  try (right; right; left; eauto using eq_in_out_input_swap, eq_in_eq_in_sig_trans, s_equal_impl_sig_eq).
Qed.

Theorem helper_matches_matches : forall (tid tid1 sid sid1: nat)(i i0 i1: actionInput)(o o0 o1 : actionOutput) 
  (H0 : (input i =s= input i0 \/ i =io= o0) \/ output o =s= output o0 \/ i0 =io= o \/ output o <-o-> output o0)
  (H : (input i0 =s= input i1 \/ i0 =io= o1) \/ output o0 =s= output o1 \/ i1 =io= o0 \/ output o0 <-o-> output o1) 
  (e : i =io= o)(e0 : i0 =io= o0)(e1:i1 =io= o1), matches (matchEvent tid sid i o e) <--> matches (matchEvent tid1 sid1 i1 o1 e1).
Proof.
intros tid tid' sid sid' i i0 i1 o o0 o1 H H0.
destruct H as [[H|H]|[H|[H|H]]], H0 as [[H0|H0]|[H0|[H0|H0]]];
intros e e_m e_'.
- right;left;left. eauto using s_equal_trans.
- right;right;right;right. eauto using  eq_in_out_input_swap, eq_in_eq_in_sig_trans.
- right; right; right; right. 
    apply s_eql_swap_output_sig with (b := output o0). split; eauto.
    eauto using eq_in_out_input_swap, eq_in_eq_in_sig_trans. 
(*  i =io= o, i=i0 => i0 =io= o, i0 =io= o0 => o <-o-> o0, o0 = o1 => o <-o-> o1 *)
- right; left; left. eauto using eq_io_trans_s_equal, s_equal_trans.
- right. left;right. eauto using eq_in_out_input_swap, eq_io_sig_eq_impl_io_eq.
- right. left; left. eauto using eq_io_trans_s_equal, s_equal_trans.
- right;left;left. 
  apply s_equal_trans with (b := input i0). split; eauto using eq_io_trans_s_equal, s_equal_trans.
- right; left; right. eauto using eq_in_out_output_swap.
- right. left; left. eauto using  eq_io_trans_s_equal.
- right. left; right. eauto using eq_io_sig_eq_impl_io_eq. 
- right. right; right. left. apply eq_in_out_output_swap with (o := o0). split; eauto using eq_in_out_input_swap, s_equal_sym.
- right. right; right; right. apply eq_sig_sym. apply s_eql_swap_output_sig with (b := output o0).  
  eauto using s_equal_sym, eq_in_eq_in_sig_trans.
- right. right; left. eauto using s_equal_trans.
- right. right; right; left. eauto using eq_in_out_output_swap, s_equal_sym.
- right. right; right; right. eauto using s_equal_sig_eq_out_impl_sig_eq_out.
- right. right; right; left. eauto using s_equal_sym, eq_in_out_input_swap.
- right; right; right; right; eauto using eq_in_eq_in_sig_trans.
- right; right; right; right; eauto using eq_in_eq_in_sig_trans, s_eql_swap_output_sig.
- right; right; right; right. apply sig_pl_pl_eq_trans with (b := output o0); split; eauto using eq_in_eq_in_sig_trans.
- right; right; right; right. eauto using eq_in_eq_in_sig_trans, sig_pl_pl_eq_trans.
- right. right; right; right. apply eq_sig_sym. apply  sig_pl_pl_eq_trans with (b := output o0);
  split; eauto using eq_sig_sym, eq_in_out_input_swap, eq_in_eq_in_sig_trans.
- right. right; right; right. eauto using eq_in_eq_in_sig_trans, sig_pl_pl_eq_trans.
- right; right; right; right; eauto using s_eql_swap_output_sig.
- right; right; right; right; eauto using eq_in_eq_in_sig_trans, sig_pl_pl_eq_trans.
- right; right; right; right; eauto using sig_pl_pl_eq_trans.
Qed.

Theorem helper_matches_output : forall (tid sid: nat)(i i0: actionInput)(o o0 a1 : actionOutput) 
  (H0: (input i =s= input i0 \/ i =io= o0) \/ output o =s= output o0 \/ i0 =io= o \/ output o <-o-> output o0)
  (H1: output o0 =s= output a1 \/ output o0 <-o-> output a1 \/ i0 =io= a1) 
  (e : i =io= o)(e0 : i0 =io= o0), matches (matchEvent tid sid i o e) <--> output a1.
Proof.
intros.
eapply match_match_impl_match_out with (tid1 := tid)(sid1 := sid)(i1 := i).
apply helper_matches_matches with (i0 := i0)(o0 := o0).
- trivial.
- destruct H0 as [[H|H]|[H|[H|H]]].
  + left; left. eauto using s_equal_sym.
  + right; right; left; trivial.
  + right; right; left; eauto using eq_in_out_output_swap.
  + left; left; eauto using eq_io_trans_s_equal.
  + right; right; left. eauto using eq_io_sig_eq_impl_io_eq.
- trivial. Unshelve.  
  destruct H1 as [H1 |[H1|H1]].
  + destruct H0 as [[H0|H0]|[H0|[H0|H0]]]; try eauto using eq_in_out_input_swap, eq_in_out_output_swap.
    * apply eq_in_out_output_swap  with (o := o0); split; eauto using eq_in_out_input_swap, eq_io_trans_s_equal.
    * eauto using s_eql_swap_output_sig, eq_io_sig_eq_impl_io_eq.
  + destruct H0 as [[H0|H0]|[H0|[H0|H0]]]; eauto using eq_in_out_input_swap, eq_io_sig_eq_impl_io_eq.
    * eauto using eq_in_out_output_swap, eq_io_sig_eq_impl_io_eq.
    * apply eq_io_sig_eq_impl_io_eq with (b := o0); split; eauto using eq_in_out_input_swap, eq_io_trans_s_equal.
  + destruct H0 as [[H0|H0]|[H0|[H0|H0]]]; eauto using eq_in_out_input_swap, eq_io_trans_s_equal.
    * apply eq_in_out_input_swap with (i := i0); split; eauto using eq_in_out_output_swap, eq_io_trans_s_equal.
    * apply eq_in_out_input_swap with (i := i0); split; eauto using eq_io_sig_eq_impl_io_eq, eq_io_trans_s_equal.
Qed.
    

Theorem equiv_trans {t1 t2 t3:ioh} : forall (a:action t1)(b:action t2)(c:action t3), a <--> b /\ b <--> c -> a <--> c.
Proof.
intros a b c [a_equiv_b b_equiv_c].
destruct b.
(* eliminat all cases with wrong assumption *)
- destruct a,c; try (destruct b_equiv_c; simpl in H; destruct a0; contradiction); try (contradiction);
    try( destruct a_equiv_b; simpl in H; destruct a; contradiction); try (contradiction);
    (* Now collectively destruct all Hypotheses *) 
    destruct_abc H0 H a_equiv_b b_equiv_c a a0 a1;
    try (destruct a1; destruct H as [H | H]);
    try (destruct a; destruct H0 as [H0|H0]).
    (* input <-> input <-> input *)
  + left; eauto using s_equal_trans.
  + right; eauto using eq_in_out_input_swap.
  + right; left; eauto using s_equal_trans.
  + (* input <-> match is coming from input output equality*)
    right; right; eauto using eq_in_out_input_swap .
  + (* output <-> input <-> input *)
     right; eauto using eq_in_out_input_swap , s_equal_sym.
  + (* output <-> input <-> output *) 
     right; eauto using eq_in_eq_in_sig_trans.
  + (* output <-> input <-> matches *) 
     right; right; right; eauto using s_equal_sym, eq_in_out_input_swap . 
  + right; right; left; eauto using eq_in_eq_in_sig_trans.
    (* match <-> input <-> input *)
  + right; left; eauto using s_equal_trans,s_equal_sym.
  + right; right; eauto using eq_in_out_input_swap , s_equal_sym. 
    (* match <-> input <-> output*)
  + right; right; right; eauto using eq_in_out_input_swap , s_equal_sym.
  + (* <i,o> <-> input is o <-> input *)
      right; right; left. eauto using eq_in_eq_in_sig_trans.
    (* match <-> input <-> match *)
  +  right;left;left; eauto using s_equal_trans, s_equal_sym.
  + right; right; right; left; eauto using eq_in_out_input_swap , s_equal_sym.
  + right; left; right; eauto using eq_in_out_input_swap , s_equal_sym.
  + right; right; right; right; eauto using eq_in_eq_in_sig_trans. 
- destruct a_equiv_b as [H | H]; destruct a; 
  try (simpl in H; dependent destruction a; contradiction).
  destruct b_equiv_c as [H1 | H1]; destruct c;
  try (simpl in H1; dependent destruction a0; contradiction).
  + left; eauto using s_equal_trans.
  + right; eauto using eq_in_out_output_swap, s_equal_sym.
  + right; eauto using s_equal_sig_eq_out_impl_sig_eq_out.
  + dependent destruction a1. destruct H1 as [H1 | [H1 | H1]].
    * right; left; eauto using s_equal_trans.
    * right; right; left; eauto using s_equal_sig_eq_out_impl_sig_eq_out.
    * right; right; right; eauto using eq_in_out_output_swap, s_equal_sym.
  + destruct c; try( destruct b_equiv_c as [| H0]; try( simpl in H0; try (dependent destruction a0); contradiction)).
    * left; eauto using eq_io_trans_s_equal.
    * right; eauto using eq_in_out_output_swap.
    * right; eauto using eq_io_sig_eq_impl_io_eq.
    * dependent destruction a1; destruct H0 as [H0 | [H0 | H0]].
      ** right; right; eauto using eq_in_out_output_swap.
      ** right; right; eauto using eq_io_sig_eq_impl_io_eq.
      ** right; left; eauto using eq_io_trans_s_equal.
  + destruct c; try( destruct b_equiv_c as [| H0]; try( simpl in H0; try (dependent destruction a0); contradiction)).
    * right; eauto using eq_io_sig_eq_impl_io_eq, eq_sig_sym.
    * right; eauto using  s_eql_swap_output_sig.
    * right; eauto using sig_pl_pl_eq_trans.
    * dependent destruction a1.
      destruct H0 as [H0 |[H0|H0]].
      ** right; right; left; eauto using s_eql_swap_output_sig.
      ** right; right; left; eauto using sig_pl_pl_eq_trans.
      ** right; right; right; eauto using eq_io_sig_eq_impl_io_eq, eq_sig_sym.
  + destruct c; try( destruct b_equiv_c as [| H0]; try( simpl in H0; try (dependent destruction a0); contradiction)).
    * destruct a; destruct H as [H |[H|H]].
      ** right; right; eauto using eq_in_out_output_swap, s_equal_sym.
      ** right; right; eauto using eq_io_sig_eq_impl_io_eq , eq_sig_sym.
      ** right; left; eauto using eq_io_trans_s_equal.
    * destruct a; destruct H as [H | [H|H]].
      ** right; left; eauto using s_equal_trans.
      ** right; right; left;  eauto using s_eql_swap_output_sig.
      ** right; right; right; eauto using eq_in_out_output_swap.
    * destruct a; destruct H as [H | [H|H]].
      ** right; right; left. eauto using s_equal_sig_eq_out_impl_sig_eq_out.
      ** right; right; left. eauto using sig_pl_pl_eq_trans.
      ** right; right; right; eauto using eq_io_sig_eq_impl_io_eq.
    * destruct a; destruct a1. destruct H as [H | [H|H]], H0 as [H0 | [H0|H0]].
      ** right. right; left; eauto using s_equal_trans.
      ** right; right; right; right.  eauto using s_equal_sig_eq_out_impl_sig_eq_out.
      ** right. right; right; left; eauto using eq_in_out_output_swap, s_equal_sym.
      ** right; right; right; right. eauto using s_eql_swap_output_sig.
      ** right; right; right; right. eauto using sig_pl_pl_eq_trans.
      ** right. right; right; left. eauto using eq_io_sig_eq_impl_io_eq,eq_sig_sym.
      ** right; left; right; eauto using eq_in_out_output_swap.
      ** right; left; right; eauto using eq_io_sig_eq_impl_io_eq.
      ** right. left; left; eauto using eq_io_trans_s_equal.
- destruct a, c; destruct_abc H0 H a_equiv_b b_equiv_c a a0 a1.
  + destruct a0. destruct H0 as [H0|H0]. destruct H as [H|H].
    * left; eauto using s_equal_sym, s_equal_trans.
    * left. eauto using eq_io_trans_s_equal, eq_in_out_input_swap .
    * destruct H as [H|H]. 
      ** left; eauto using eq_io_trans_s_equal, eq_in_out_input_swap .
      ** left; eauto using eq_io_trans_s_equal. 
  + destruct a0. destruct H0 as [H0|H0]. destruct H as [H|H].
    * right; eauto using eq_in_out_output_swap, eq_in_out_input_swap .
    * destruct H as [H|H]; right; eauto using eq_io_sig_eq_impl_io_eq, eq_in_out_input_swap .
    * destruct H as [H|H].
      ** right; eauto using eq_in_out_output_swap.
      ** destruct H as [H|H].
        *** right; eauto using eq_io_sig_eq_impl_io_eq.
        *** right. eauto using eq_io_trans_s_equal, eq_in_out_input_swap .
  + destruct a0, H0 as [H0|H0].
    * right. destruct a1. left. eauto using match_input_eq.
    * right. destruct a1. right. eauto using match_input_eq_out.
  + destruct a0,a1, H0 as [H0|H0], H as [[H | H] | [H | [H | H]]].
    * right. left. eauto using s_equal_trans.
    * right. right. eauto using eq_in_out_input_swap .
    * right. right. eauto using eq_in_out_input_swap , eq_in_out_output_swap .
    * right. right. apply eq_in_out_input_swap  with (i := i0). split; eauto. 
         apply eq_io_trans_s_equal with (o := o). eauto using eq_in_out_input_swap.
    * right. right. eauto using eq_in_out_input_swap , eq_io_sig_eq_impl_io_eq.
    * right.  left. eauto using  eq_io_trans_s_equal, s_equal_trans.
    * right. right. eauto using eq_io_trans_s_equal, eq_in_out_input_swap .
    * right. right. eauto using eq_in_out_output_swap.
    * right. left. eauto using eq_io_trans_s_equal.
    * right. right. eauto using eq_io_sig_eq_impl_io_eq. 
  + destruct a0. destruct H0 as [H0|[H0|H0]], H as [H|H].
    * right. apply eq_in_out_output_swap with (o := o); eauto using s_equal_sym, eq_in_out_input_swap .
    * right. eauto using eq_in_out_output_swap,s_equal_sym.
    * right. apply eq_io_sig_eq_impl_io_eq with (b := o). eauto using eq_sig_sym,eq_in_out_input_swap .
    * right. eauto using eq_io_sig_eq_impl_io_eq,eq_sig_sym.
    * right. eauto using  eq_in_out_input_swap .
    * right. eauto using eq_io_trans_s_equal,eq_in_out_input_swap .
  + destruct a0. destruct H0 as [H0|[H0|H0]],H as [H|[H|H]].
    * left. eauto using s_equal_trans.
    * right. eauto using s_equal_impl_sig_eq, sig_pl_pl_eq_trans.
    * right. eauto using eq_in_eq_in_sig_trans, s_equal_sig_eq_out_impl_sig_eq_out.
    * right. eauto using s_eql_swap_output_sig.
    * right. eauto using sig_pl_pl_eq_trans.
    * right. eauto using eq_in_eq_in_sig_trans,sig_pl_pl_eq_trans.
    * right. eauto using eq_in_eq_in_sig_trans, eq_sig_sym, s_eql_swap_output_sig.
    * right. eauto using eq_in_eq_in_sig_trans, sig_pl_pl_eq_trans.
    * right. eauto using eq_in_eq_in_sig_trans.
  + destruct a0. destruct H0 as [H0 |[H0|H0]].
    * right. destruct a1. left. eauto using match_output_eq.
    * right. destruct a1. right; left. eauto using match_output_sig_eq.
    * right. destruct a1. right. left. eauto using eq_in_eq_in_sig_trans, match_output_sig_eq.
  + destruct a0,a1. destruct H0 as [H0 |[H0|H0]], H as [[H|H]|[H|[H|H]]].
    * right. right. right. apply (eq_in_out_output_swap i0 o a). split; eauto using s_equal_sym, eq_in_out_input_swap.
    * right. right. left. eauto using eq_in_eq_in_sig_trans, s_equal_sig_eq_out_impl_sig_eq_out.
    * right. eauto using s_equal_trans.
    * right. right. left. eauto using  eq_in_eq_in_sig_trans, s_equal_sig_eq_out_impl_sig_eq_out.
    * right. right. left. eauto using  s_equal_sig_eq_out_impl_sig_eq_out.
    * right; right; left; apply (sig_pl_pl_eq_trans (output a) (output o) (output o0)); split; auto;
      apply (eq_in_eq_in_sig_trans i0 o o0); split; eauto using eq_in_eq_in_sig_trans, eq_in_out_input_swap,s_equal_sym.
    * right; right; left; eauto using eq_in_eq_in_sig_trans, sig_pl_pl_eq_trans.
    * right; right; left; eauto using s_eql_swap_output_sig.
    * right; right; right. eauto using  eq_io_sig_eq_impl_io_eq, eq_sig_sym .
    * right; right; left. eauto using sig_pl_pl_eq_trans.
    * right; right; right. eauto using  eq_in_out_input_swap, s_equal_sym.
    * right; right; right. eauto using eq_in_eq_in_sig_trans, eq_io_sig_eq_impl_io_eq .
    * right; right;left. eauto using s_eql_swap_output_sig, eq_in_eq_in_sig_trans.
    * right; right; right. eauto using eq_io_trans_s_equal, eq_in_out_input_swap.
    * right. right; left. eauto using eq_in_eq_in_sig_trans, sig_pl_pl_eq_trans.
  + destruct a,a0. destruct H as [H|H]. 
    * right. left. eauto using s_equal_sym, match_input_eq.
    * right. right. eauto using s_equal_sym, match_input_eq_out.
  + destruct a,a0. destruct H0 as [[H0|H0]|[H0|[H0|H0]]], H as [H|H].
    * right; left. eauto using s_equal_sym, s_equal_trans.
    * right. left. apply s_equal_trans with (b := input i0). eauto using eq_io_trans_s_equal, s_equal_sym.
    * right; left. apply s_equal_trans with (b := input i0). eauto using eq_io_trans_s_equal, s_equal_trans.
    * right; right. eauto using eq_io_trans_s_equal, eq_in_out_input_swap.
    * right; right. apply eq_in_out_output_swap with (o := o0). eauto using eq_in_out_input_swap, s_equal_sym.
    * right; right. eauto using s_equal_sym, eq_in_out_output_swap.
    * right; right. eauto using  eq_in_out_input_swap.
    * right; right.  eauto using eq_io_trans_s_equal, eq_in_out_input_swap.
    * right; right. apply eq_io_sig_eq_impl_io_eq with (b := o0). eauto using eq_in_out_input_swap, eq_sig_sym.
    * right; right. eauto using eq_sig_sym,  eq_io_sig_eq_impl_io_eq.
  + destruct a0. destruct H as [H |[H|H]].
    * right. destruct a. left. eapply matches_impl in H0. destruct H0 as [_ H0]. eauto using s_equal_trans.
    * right. destruct a. right; left. eapply matches_impl in H0. destruct H0 as [_ H0]. eauto using s_equal_sig_eq_out_impl_sig_eq_out.
    * destruct a. right. eapply matches_impl in H0. destruct H0 as [H0 _]. right; right. eauto using eq_in_out_input_swap.
  + destruct a,a0. eauto using helper_matches_output.
  + left. eauto using s_equal_trans.
  + destruct a0,a1. destruct H as [[H|H]|[H|[H|H]]]; right; destruct a; eapply matches_impl in H0.
    * destruct H0 as [H0 _]. left; left. eauto using s_equal_trans.
    * left; right. destruct H0 as [H0 _]. eauto using eq_in_out_input_swap.
    * right; left. destruct H0 as [_ H0]. eauto using s_equal_trans.
    * right; right; left. destruct H0 as [_ H0]. eauto using s_equal_sym, eq_in_out_output_swap.
    * right; right; right. destruct H0 as [_ H0]. eauto using  s_equal_impl_sig_eq,sig_pl_pl_eq_trans.
  + destruct a,a0. destruct H0 as [[H0|H0]|[H0|[H0|H0]]]; right; destruct a1; eapply matches_impl in H.
    * destruct H as [H _]. left; left. eauto using s_equal_trans. 
    * destruct H as [_ H]. left; right. eauto using eq_in_out_output_swap.
    * destruct H as [_ H]. right; left. eauto using s_equal_trans.
    * destruct H as [H _]. right; right; left. eauto using eq_in_out_input_swap,s_equal_sym.
    * destruct H as [_ H]. right; right; right. eauto using s_equal_impl_sig_eq,sig_pl_pl_eq_trans.
  + destruct a,a0,a1. eauto using helper_matches_matches.
- destruct a, c; destruct_abc H0 H a_equiv_b b_equiv_c a a0 a1; left; eauto using s_equal_trans.
- destruct a, c; destruct_abc H0 H a_equiv_b b_equiv_c a a0 a1; left; eauto using s_equal_trans.
Qed. 

Theorem equiv_act_sym {t1 t2 :ioh} : forall (a:action t1)(b:action t2), a <--> b -> b <--> a.    
Proof.
intros a b H.
destruct a,b; destruct H as [H|H]; 
  (* eliminate cases where a direct contradiction can be applied *) 
  try contradiction;
  (* for a = b with a and b being the same type it can be solved by using s_equal symmetry *)
  try (simpl in H; destruct a; contradiction).
  (* for cases where the relationship is =io= *)
- left; eauto using s_equal_sym.
- right; trivial.
- right; trivial. 
- right; trivial.
- left; auto using s_equal_sym.
- right. auto using eq_sig_sym.
- destruct a0. right. destruct H as [H|[H|H]]; eauto using s_equal_sym, eq_sig_sym.
- destruct a. right; trivial.
- destruct a. right. destruct H as [H|[H|H]]; eauto using s_equal_sym, eq_sig_sym.
- left; eauto using s_equal_sym.
- destruct a,a0. destruct H as [[H|H]|[H|[H|H]]].
  + right. left; left. eauto using s_equal_sym.
  + right; right; right; left; trivial.
  + right;right;left. auto using s_equal_sym.
  + right; left; right; trivial.
  + right; right; right; right; auto using eq_sig_sym.
- left; auto using s_equal_sym.
- left; auto using s_equal_sym.
Qed.

Theorem equiv_act_refl {t:ioh} : forall (a : action t), a <--> a.
Proof.
destruct a; left; auto using s_equal_refl.
Qed.