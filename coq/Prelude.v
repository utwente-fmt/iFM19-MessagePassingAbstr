Require Import HahnBase.
Require Import List.
Require Import Utf8.

Module Type Domains.
  Parameter Var: Type.
  Parameter Val: Type.
  Parameter val_plus: Val -> Val -> Val.
  Parameter val_unit : Val.

  Parameter var_eq_dec : forall x y: Var, { x = y } + { x <> y }.
  Parameter val_eq_dec : forall x y: Val, { x = y } + { x <> y }.
  Parameter val_inf : forall xs: list Val, exists v: Val, ~ In v xs.

  Lemma val_pair_eq_dec :
    forall x y : Val * Val, {x = y} + {x <> y}.
  Proof.
    decide equality; apply val_eq_dec.
  Qed.
End Domains.

Definition update {A B} (eq_dec: forall x y: A, { x = y } + { x <> y })(f: A -> B)(x: A)(v: B): A -> B :=
  fun y: A => if eq_dec x y then v else f y.

Definition disjoint {A} (X Y : A -> Prop) :=
  forall x, X x -> Y x -> False.

Definition disjoint_list {A} (xl yl : list A) :=
  forall x (IN1 : In x xl) (IN2 : In x yl), False.

Definition pred_of_list {A} (l : list A) (x : A) := In x l.

Coercion pred_of_list : list >-> Funclass.

Lemma disjoint_conv :
  forall A (l1 l2 : list A),
  disjoint l1 l2 -> disjoint_list l1 l2.
Proof.
  done.
Qed.

Lemma option_not_none {T} :
  forall x : option T,
  ~ x = None <-> exists v, x = Some v.
Proof.
  intros x. split; intro H1.
  - intuition. destruct x; vauto.
  - intro. desf.
Qed.

Lemma list_forall_notin {T} :
  forall xs: list T, (forall x, ~ In x xs) -> xs = nil.
Proof.
  induction xs; intros H1; auto.
  assert (H2: forall x: T, ~ In x xs). {
    intros x H2. apply H1 with x.
    simpl. by right. }
  apply IHxs in H2. vauto.
  simpl in H1. specialize H1 with a.
  apply not_or_and in H1. desf.
Qed.
