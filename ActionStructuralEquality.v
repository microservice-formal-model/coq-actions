Require Import Program.
Require Import RelationClasses.
Require Import ActionDefinitions.

Lemma s_equal_refl {t:ioh} : forall (a : action t), a =s= a.
Proof.
destruct a; dependent destruction a; simpl; 
  try (dependent destruction i); try (dependent destruction o); 
  repeat (split; eauto using eq_refl).
Qed.

Lemma s_equal_sym {t1 t2: ioh} : forall (a : action t1)(b : action t2), a =s= b -> b =s= a.
Proof.
intros a b eq_a_b.
destruct a; destruct b; dependent destruction a; dependent destruction a0; simpl in *; 
  try (contradiction). 
- destruct eq_a_b as [A0 [A1 [A2 [A3 A4]]]].
  repeat (split; eauto using eq_sym).
- destruct eq_a_b as [B0 [B1 [B2 [B3 B4]]]].
  repeat (split; eauto using eq_sym).
- dependent destruction i0; dependent destruction i; 
  dependent destruction o; dependent destruction o0.
  destruct eq_a_b as [A0 [A1 [A2 A3]]].
  destruct A2 as [B0 [B1 [B2 B3]]], A3 as [C0 [C1 [C2 C3]]].
  destruct B3 as [B30 B31].
  destruct C3 as [C30 C31].
  repeat (split; eauto using eq_sym).
- destruct eq_a_b as [A0 [A1 [A2 A3]]].
  repeat (split; eauto using eq_sym).
- destruct eq_a_b as [A0 [A1 A2]].
  repeat (split; eauto using eq_sym).
Qed.

Lemma s_equal_trans {t1 t2 t3 : ioh} : forall (a : action t1)(b: action t2)(c: action t3), a =s= b /\ b =s= c -> a =s= c.
Proof.
intros a b c [eq_a_b eq_b_c].
(* eliminate all cases that have a wrong assumption *)
destruct a, b; dependent destruction a; dependent destruction a0; 
  try (simpl in eq_a_b; contradiction);
  destruct c; dependent destruction a; 
  try (simpl in eq_b_c; contradiction).
(* this covers cases for output and input event *)
all: try (
  simpl in *;
  destruct eq_a_b as [A0 [A1 [A2 [A3 A4]]]], eq_b_c as [B0 [B1 [B2 [B3 B4]]]];
  repeat (split; eauto using eq_trans)
).
(* match event *)
- simpl in *. 
  dependent destruction i; dependent destruction i0;
  dependent destruction o; dependent destruction o0;
  dependent destruction o1; dependent destruction i1.
  destruct eq_a_b as [A0 [A1 [A2 [A3 [A4 [A5 [A6 A7]]]]]]], A2 as [A20 [A21 [A22 [A23 A24]]]].
  destruct eq_b_c as [B0 [B1 [B2 [B3 [B4 [B5 [B6 B7]]]]]]], B2 as [B20 [B21 [B22 [B23 B24]]]].
  repeat (split; eauto using eq_trans).
(* dbAccess *)
- simpl in *.
  destruct eq_a_b as [A0 [A1 [A2 A3]]].
  destruct eq_b_c as [B0 [B1 [B2 B3]]].
  repeat (split; eauto using eq_trans).
(* guard *)
- simpl in *.
  destruct eq_a_b as [A0 [A1 A2]].
  destruct eq_b_c as [B0 [B1 B2]].
  repeat(split; eauto using eq_trans).
Qed.
