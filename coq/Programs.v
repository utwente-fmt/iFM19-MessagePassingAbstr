Require Import HahnBase.
Require Import Heaps.
Require Import List.
Require Import Prelude.
Require Import Processes.
Require Import Nat.
Require Import Setoid.
Require Import Utf8.

Import ListNotations.

Set Implicit Arguments.

(** * Programs *)

Module Type Programs
  (dom: Domains)
  (procs: Processes dom)
  (heaps: Heaps dom).

Export dom procs heaps.

(** ** Syntax *)

(** *** Expressions *)

Inductive Expr :=
  | Econst(n: Val)
  | Evar(x: Var)
  | Eplus(E1 E2: Expr).

Add Search Blacklist "Expr_rect".
Add Search Blacklist "Expr_ind".
Add Search Blacklist "Expr_rec".

Fixpoint expr_fv (E: Expr): list Var :=
   match E with
    | Econst n => []
    | Evar x => [x]
    | Eplus E1 E2 => expr_fv E1 ++ expr_fv E2
  end.

Definition expr_closed (E: Expr): Prop := expr_fv E = nil.

Lemma expr_closed_plus :
  forall E1 E2,
  expr_closed (Eplus E1 E2) <-> expr_closed E1 /\ expr_closed E2.
Proof.
  intros E1 E2. unfold expr_closed. split; intro H1; simpls.
  - apply app_eq_nil in H1. desf.
  - destruct H1 as (H1 & H2). rewrite H1, H2. simpls.
Qed.

Fixpoint expr_subst (x: Var)(E E': Expr): Expr :=
  match E' with
    | Econst n => Econst n
    | Evar y => if var_eq_dec x y then E else Evar y
    | Eplus E1 E2 => Eplus (expr_subst x E E1) (expr_subst x E E2)
  end.

Lemma expr_subst_pres :
  forall E1 E2 x, ~ In x (expr_fv E1) -> expr_subst x E2 E1 = E1.
Proof.
  induction E1; intros E2 x' H; simpls; intuition desf.
  rewrite IHE1_1, IHE1_2; auto.
  - intro H1. apply H.
    apply in_or_app. by right.
  - intro H1. apply H.
    apply in_or_app. by left.
Qed.

Lemma expr_fv_subst_notin :
  forall E E' x,
  ~ In x (expr_fv E') -> ~ In x (expr_fv (expr_subst x E' E)).
Proof.
  induction E as [n|v|E1 IH1 E2 IH2]; intros E' x H1 H2; simpls.
  - desf. simpl in H2. desf.
  - apply in_app_or in H2. destruct H2 as [H2 | H2].
    + apply IH1 in H1. desf.
    + apply IH2 in H1. desf.
Qed.

Lemma expr_fv_subst_in :
  forall E E' x y,
  ~ x = y ->
  ~ In x (expr_fv E') ->
  In x (expr_fv (expr_subst y E' E)) <-> In x (expr_fv E).
Proof.
  induction E as [n|v|E1 IH1 E2 IH2]; intros E' x y H1 H2; simpls.
  - desf. split; intro H3; vauto.
    destruct H3 as [H3 | H3]; vauto.
  - split; intro H3.
    + apply in_app_or in H3. destruct H3 as [H3 | H3].
      * apply IH1 with (y := y) in H2; vauto.
        apply in_or_app. left. by rewrite <- H2.
      * apply IH2 with (y := y) in H2; vauto.
        apply in_or_app. right. by rewrite <- H2.
    + apply in_app_or in H3. destruct H3 as [H3 | H3].
      * apply IH1 with (y := y) in H2; vauto.
        apply in_or_app. left. by rewrite H2.
      * apply IH2 with (y := y) in H2; vauto.
        apply in_or_app. right. by rewrite H2.
Qed.

Inductive Cond :=
  | Bconst(b: bool)
  | Bnot(B: Cond)
  | Band(B1 B2: Cond)
  | Beq(E1 E2: Expr).

Add Search Blacklist "Cond_rect".
Add Search Blacklist "Cond_ind".
Add Search Blacklist "Cond_rec".

Fixpoint cond_fv (B: Cond): list Var :=
   match B with
    | Bconst b => []
    | Bnot B' => cond_fv B'
    | Band B1 B2 => cond_fv B1 ++ cond_fv B2
    | Beq E1 E2 => expr_fv E1 ++ expr_fv E2
  end.

Definition cond_closed (B: Cond): Prop := cond_fv B = nil.

Lemma cond_closed_not :
  forall B, cond_closed (Bnot B) <-> cond_closed B.
Proof.
  intro B. split; intro H; simpls.
Qed.

Lemma cond_closed_and :
  forall B1 B2,
  cond_closed (Band B1 B2) <-> cond_closed B1 /\ cond_closed B2.
Proof.
  intros B1 B2. split; intro H1.
  - red in H1. simpl in H1.
    apply app_eq_nil in H1. desf.
  - destruct H1 as (H1 & H2).
    red. simpl. by rewrite H1, H2.
Qed.

Lemma cond_closed_eq :
  forall E1 E2,
  cond_closed (Beq E1 E2) <-> expr_closed E1 /\ expr_closed E2.
Proof.
  intros E1 E2. split; intro H1.
  - red in H1. simpl in H1.
    apply app_eq_nil in H1. desf.
  - destruct H1 as (H1 & H2).
    red. simpl. red in H1, H2.
    by rewrite H1, H2.
Qed.

Fixpoint cond_subst (x: Var)(E: Expr)(B: Cond): Cond :=
  match B with
    | Bconst b => Bconst b
    | Bnot B' => Bnot (cond_subst x E B')
    | Band B1 B2 => Band (cond_subst x E B1) (cond_subst x E B2)
    | Beq E1 E2 => Beq (expr_subst x E E1) (expr_subst x E E2)
  end.

Lemma cond_subst_pres :
  forall B E x, ~ In x (cond_fv B) -> cond_subst x E B = B.
Proof.
  induction B; intros E x H; simpls.
  - by rewrite IHB.
  - rewrite IHB1, IHB2; intuition.
  - repeat rewrite expr_subst_pres; intuition.
Qed.

Lemma cond_fv_subst_notin :
  forall B E x,
  ~ In x (expr_fv E) -> ~ In x (cond_fv (cond_subst x E B)).
Proof.
  induction B as [b|B' IH|B1 IH1 B2 IH2|E1 E2];
  intros E x H1 H2; vauto.
  - apply IH in H1. simpls.
  - simpl in H2. apply in_app_or in H2.
    destruct H2 as [H2 | H2].
    + by apply IH1 in H1.
    + by apply IH2 in H1.
  - simpl in H2. apply in_app_or in H2.
    destruct H2 as [H2 | H2].
    + apply expr_fv_subst_notin in H2; auto.
    + apply expr_fv_subst_notin in H2; auto.
Qed.

Lemma cond_fv_subst_in :
  forall B E x y,
  ~ x = y ->
  ~ In x (expr_fv E) ->
  In x (cond_fv (cond_subst y E B)) <-> In x (cond_fv B).
Proof.
  induction B as [b|B' IH|B1 IH1 B2 IH2|E1 E2];
  intros E x y H1 H2; vauto.
  - split; intro H3.
    + simpls. rewrite IH in H3; auto.
    + simpl. rewrite IH; vauto.
  - simpls. split; intro H3; simpls.
    + apply in_app_or in H3. destruct H3 as [H3 | H3].
      * apply in_or_app. left. apply IH1 in H3; auto.
      * apply in_or_app. right. apply IH2 in H3; auto.
    + apply in_app_or in H3. destruct H3 as [H3 | H3].
      * apply in_or_app. left. apply <- IH1; auto.
      * apply in_or_app. right. apply <- IH2; auto.
  - simpls. split; intro H3; simpls.
    + apply in_or_app.
      rewrite <- expr_fv_subst_in with (E := E1)(E' := E)(y := y); vauto.
      rewrite <- expr_fv_subst_in with (E := E2)(E' := E)(y := y); vauto.
      apply in_app_or in H3. desf.
    + apply in_or_app.
      rewrite expr_fv_subst_in with (E := E1)(E' := E)(y := y); vauto.
      rewrite expr_fv_subst_in with (E := E2)(E' := E)(y := y); vauto.
      apply in_app_or in H3. desf.
Qed.

(** *** Commands *)

(** For now atomics are left out; these are straightforward to add. *)

Inductive Cmd :=
  | Cskip
  | Cseq(C1 C2: Cmd)
  | Cass(x: Var)(E: Expr)
  | Cread(x: Var)(E: Expr)
  | Cwrite(E1 E2: Expr)
  | Cite(B: Cond)(C1 C2: Cmd)
  | Cwhile(B: Cond)(C: Cmd)
  | Cpar(C1 C2: Cmd)
  | Calloc(x: Var)(E: Expr)
  | Cdispose(E: Expr)
  | Csend(E T: Expr)
  | Crecv1(x y: Var)
  | Crecv2(x: Var)(T: Expr)
  | Cquery(B: Cond).

Add Search Blacklist "Cmd_rect".
Add Search Blacklist "Cmd_ind".
Add Search Blacklist "Cmd_rec".

Lemma cmd_neg_seq :
  forall C1 C2, ~ C1 = Cseq C2 C1.
Proof.
  induction C1; intros C2 H1; vauto. clarify.
  by apply IHC1_2 in H0.
Qed.

Lemma cmd_neg_ite_t :
  forall C1 C2 B, ~ C1 = Cite B C1 C2.
Proof.
  induction C1; ins. intro. vauto.
  by apply IHC1_1 in H1.
Qed.

Lemma cmd_neg_ite_f :
  forall C2 C1 B, ~ C2 = Cite B C1 C2.
Proof.
  induction C2; ins. intro. vauto.
  by apply IHC2_2 in H.
Qed.

Fixpoint cmd_fv (C: Cmd): list Var :=
  match C with
    | Cskip => []
    | Cass x E
    | Cread x E
    | Calloc x E => x :: expr_fv E
    | Cwrite E1 E2 => expr_fv E1 ++ expr_fv E2
    | Cite B C1 C2 => cond_fv B ++ cmd_fv C1 ++ cmd_fv C2
    | Cwhile B C' => cond_fv B ++ cmd_fv C'
    | Cseq C1 C2
    | Cpar C1 C2 => cmd_fv C1 ++ cmd_fv C2
    | Cdispose E => expr_fv E
    | Csend E T => expr_fv E ++ expr_fv T
    | Crecv1 x y => [x; y]
    | Crecv2 x T => x :: expr_fv T
    | Cquery B => cond_fv B
  end.

Fixpoint cmd_mod (C: Cmd): list Var :=
  match C with
    | Cskip => []
    | Cass x _
    | Cread x _
    | Calloc x _ => [x]
    | Cwrite _ _ => []
    | Cite _ C1 C2 => cmd_mod C1 ++ cmd_mod C2
    | Cwhile _ C' => cmd_mod C'
    | Cseq C1 C2
    | Cpar C1 C2 => cmd_mod C1 ++ cmd_mod C2
    | Cdispose _ => []
    | Csend _ _ => []
    | Crecv1 x y => [x; y]
    | Crecv2 x _ => [x]
    | Cquery _ => []
  end.

Lemma cmd_fv_mod :
  forall C x, In x (cmd_mod C) -> In x (cmd_fv C).
Proof.
  induction C; intros z H; simpls; vauto.
  - apply in_app_iff in H. destruct H as [H | H].
    + apply in_app_iff. left. by apply IHC1.
    + apply in_app_iff. right. by apply IHC2.
  - intuition.
  - intuition.
  - apply in_app_iff. right.
    apply in_app_iff in H. destruct H as [H | H].
    + apply in_app_iff. left. by apply IHC1.
    + apply in_app_iff. right. by apply IHC2.
  - apply in_app_iff. right. by apply IHC.
  - apply in_app_iff in H. destruct H as [H | H].
    + apply in_app_iff. left. by apply IHC1.
    + apply in_app_iff. right. by apply IHC2.
  - intuition.
  - intuition.
Qed.

(** ** Denotational semantics *)

Definition Store := Var -> Val.

Definition updatestore (s: Store) x v := update var_eq_dec s x v.

Definition store_agree (xs: list Var)(s1 s2: Store) : Prop :=
  forall x: Var, In x xs -> s1 x = s2 x.

Lemma store_agree_split :
  forall xs1 xs2 s1 s2,
  store_agree (xs1 ++ xs2) s1 s2 ->
  store_agree xs1 s1 s2 /\ store_agree xs2 s1 s2.
Proof.
  intros xs1 xs2 s1 s2 H1.
  split; intros x H2.
  - apply H1. apply in_or_app. by left.
  - apply H1. apply in_or_app. by right.
Qed.

Fixpoint expr_eval (E: Expr)(s: Store): Val :=
  match E with
    | Econst n => n
    | Evar x => s x
    | Eplus E1 E2 => val_plus (expr_eval E1 s) (expr_eval E2 s)
  end.

Lemma expr_eval_subst :
  forall E1 E2 x s,
  expr_eval (expr_subst x E1 E2) s =
  expr_eval E2 (updatestore s x (expr_eval E1 s)).
Proof.
  intros E1 E2 x s. unfold updatestore, update.
  induction E2 as [v | y | E1' IH1 E2' IH2]; simpls.
  - desf.
  - by rewrite IH1, IH2.
Qed.

Lemma expr_agree :
  forall E s1 s2,
  store_agree (expr_fv E) s1 s2 -> expr_eval E s1 = expr_eval E s2.
Proof.
  induction E; intros s1 s2 H; simpls.
  - apply H. vauto.
  - apply store_agree_split in H. des.
    by rewrite IHE1 with s1 s2, IHE2 with s1 s2.
Qed.

Lemma expr_eval_upd :
  forall E s x v,
  ~ In x (expr_fv E) -> expr_eval E (updatestore s x v) = expr_eval E s.
Proof.
  intros E s x v H1.
  rewrite expr_agree with E s (updatestore s x v); vauto.
  intros y H2. unfold updatestore, update. desf.
Qed.

Fixpoint cond_eval (B: Cond)(s: Store): bool :=
  match B with
    | Bconst b => b
    | Bnot B' => negb (cond_eval B' s)
    | Band B1 B2 => (cond_eval B1 s) && (cond_eval B2 s)
    | Beq E1 E2 => if val_eq_dec (expr_eval E1 s) (expr_eval E2 s) then true else false
  end.

Lemma cond_eval_subst :
  forall B E x s,
  cond_eval (cond_subst x E B) s =
  cond_eval B (updatestore s x (expr_eval E s)).
Proof.
  induction B as [b | B' IH | B1 IH1 B2 IH2 | E' IH];
  intros E x s; simpl; intuition.
  - by rewrite IH.
  - by rewrite IH1, IH2.
  - by repeat rewrite expr_eval_subst.
Qed.

Lemma cond_agree :
  forall B s1 s2,
  store_agree (cond_fv B) s1 s2 -> cond_eval B s1 = cond_eval B s2.
Proof.
  induction B as [b | B' IH | B1 IH1 B2 IH2 | E1 E2];
  intros s1 s2 H; simpls.
  - by rewrite IH with s1 s2.
  - apply store_agree_split in H. destruct H as (H1 & H2).
    by rewrite IH1 with s1 s2, IH2 with s1 s2.
  - apply store_agree_split in H. destruct H as (H1 & H2).
    by rewrite expr_agree with E1 s1 s2, expr_agree with E2 s1 s2.
Qed.

Lemma cond_eval_upd :
  forall B s x v,
  ~ In x (cond_fv B) -> cond_eval B (updatestore s x v) = cond_eval B s.
Proof.
  intros B s x v H1.
  rewrite cond_agree with B s (updatestore s x v); vauto.
  intros y H2. unfold updatestore, update. desf.
Qed.

(** ** Expression conversion *)

(** Operations and properties to convert [Expr] to [ProcExpr], and [Cond] to [ProcCond]. *)

Fixpoint expr_conv (E: Expr)(s: Store): ProcExpr :=
  match E with
    | Econst v => PEconst v
    | Evar x => PEconst (s x)
    | Eplus E1 E2 => PEplus (expr_conv E1 s) (expr_conv E2 s)
  end.

Lemma expr_conv_closed :
  forall E s1 s2, expr_closed E -> expr_conv E s1 = expr_conv E s2.
Proof.
  induction E as [v|x|E1 IH1 E2 IH2]; intros s1 s2 H1; simpls; vauto.
  red in H1. simpl in H1. apply app_eq_nil in H1.
  destruct H1 as (H1 & H2).
  rewrite IH1 with s1 s2, IH2 with s1 s2; auto.
Qed.

Lemma expr_conv_eval :
  forall E s, expr_eval E s = pexpr_eval (expr_conv E s).
Proof.
  induction E as [v | x | E1 IH1 E2 IH2]; intros s; simpls.
  by rewrite IH1, IH2.
Qed.

Lemma expr_conv_subst :
  forall x s E1 E2,
  pexpr_eval (expr_conv (expr_subst x E1 E2) s) =
  pexpr_eval (expr_conv E2 (updatestore s x (expr_eval E1 s))).
Proof.
  intros x s E1 E2.
  repeat rewrite <- expr_conv_eval.
  apply expr_eval_subst.
Qed.

Lemma expr_conv_subst_upd :
  forall E x y v s,
  ~ In y (expr_fv E) ->
  expr_conv (expr_subst x (Evar y) E) (updatestore s y v) =
  expr_conv (expr_subst x (Econst v) E) s.
Proof.
  induction E as [v|z|E1 IH1 E2 IH2]; intros x y v' s H1; simpls.
  - desf.
    + unfold expr_conv. unfold updatestore, update. desf.
    + unfold expr_conv. unfold updatestore, update. desf.
      apply not_or_and in H1. desf.
  - rewrite IH1, IH2; auto.
    + intro H2. apply H1. apply in_or_app. by right.
    + intro H2. apply H1. apply in_or_app. by left.
Qed.

Lemma expr_conv_subst_upd_swap :
  forall E E' x1 x2 y v s,
  ~ In y (expr_fv E) ->
  ~ x1 = x2 ->
  ~ x1 = y ->
  ~ In x2 (expr_fv E') ->
  expr_conv (expr_subst x1 E' (expr_subst x2 (Evar y) E)) (updatestore s y v) =
  expr_conv (expr_subst x2 (Evar y) (expr_subst x1 E' E)) (updatestore s y v).
Proof.
  induction E as [v|z|E1 IH1 E2 IH2];
  intros E' x1 x2 y v' s H1 H2 H3 H4; simpls; desf; simpls; desf.
  - rewrite expr_subst_pres; auto.
  - rewrite IH1, IH2; vauto.
    + intro H5. apply H1. apply in_or_app. by right.
    + intro H5. apply H1. apply in_or_app. by left.
Qed.

Lemma expr_conv_agree :
  forall E s1 s2,
    (forall x, In x (expr_fv E) -> s1 x = s2 x) ->
  expr_conv E s1 = expr_conv E s2.
Proof.
  induction E as [v|z|E1 IH1 E2 IH2]; intros s1 s2 H1; vauto.
  - simpl. rewrite H1; vauto.
  - simpl. rewrite IH1 with s1 s2, IH2 with s1 s2; vauto.
    + intros x H2. apply H1. simpl. apply in_app_iff. by right.
    + intros x H2. apply H1. simpl. apply in_app_iff. by left.
Qed.

Fixpoint cond_conv (B: Cond)(s : Store): ProcCond :=
  match B with
    | Bconst b => PBconst b
    | Bnot B' => PBnot (cond_conv B' s)
    | Band B1 B2 => PBand (cond_conv B1 s) (cond_conv B2 s)
    | Beq E1 E2 => PBeq (expr_conv E1 s) (expr_conv E2 s)
  end.

Lemma cond_conv_closed :
  forall B s1 s2, cond_closed B -> cond_conv B s1 = cond_conv B s2.
Proof.
  induction B as [b | B' IH | B1 IH1 B2 IH2| E1 E2];
  intros s1 s2 H1; simpls; vauto.
  - rewrite IH with s1 s2; auto.
  - apply cond_closed_and in H1. destruct H1 as (H1 & H2).
    rewrite IH1 with s1 s2, IH2 with s1 s2; auto.
  - apply cond_closed_eq in H1. destruct H1 as (H1 & H2).
    rewrite expr_conv_closed with E1 s1 s2; auto.
    rewrite expr_conv_closed with E2 s1 s2; auto.
Qed.

Lemma cond_conv_eval :
  forall B s, cond_eval B s = pcond_eval (cond_conv B s).
Proof.
  induction B as [b | B' IH | B1 IH1 B2 IH2| E1 E2]; intro s; simpls.
  - by rewrite IH.
  - by rewrite IH1, IH2.
  - by repeat rewrite expr_conv_eval.
Qed.

Lemma cond_conv_subst :
  forall x s E B,
  pcond_eval (cond_conv (cond_subst x E B) s) =
  pcond_eval (cond_conv B (updatestore s x (expr_eval E s))).
Proof.
  intros x s E B.
  repeat rewrite <- cond_conv_eval.
  apply cond_eval_subst.
Qed.

Lemma cond_conv_subst_upd :
  forall B x y v s,
  ~ In y (cond_fv B) ->
  cond_conv (cond_subst x (Evar y) B) (updatestore s y v) =
  cond_conv (cond_subst x (Econst v) B) s.
Proof.
  induction B as [b|B' IH|B1 IH1 B2 IH2|E1 E2];
  intros x y v s H1; simpls.
  - rewrite IH; auto.
  - rewrite IH1, IH2; auto.
    + intro H2. apply H1. apply in_or_app. by right.
    + intro H2. apply H1. apply in_or_app. by left.
  - repeat rewrite expr_conv_subst_upd; auto.
    + intro H2. apply H1. apply in_or_app. by right.
    + intro H2. apply H1. apply in_or_app. by left.
Qed.

Lemma cond_conv_subst_upd_swap :
  forall B E x1 x2 y v s,
  ~ In y (cond_fv B) ->
  ~ x1 = x2 ->
  ~ x1 = y ->
  ~ In x2 (expr_fv E) ->
  cond_conv (cond_subst x1 E (cond_subst x2 (Evar y) B)) (updatestore s y v) =
  cond_conv (cond_subst x2 (Evar y) (cond_subst x1 E B)) (updatestore s y v).
Proof.
  induction B as [b|B' IH|B1 IH1 B2 IH2|E1 E2];
  intros E x1 x2 y v' s H1 H2 H3 H4; simpls; desf; simpls; desf.
  - rewrite IH; vauto.
  - rewrite IH1, IH2; vauto.
    + intro H5. apply H1. apply in_or_app. by right.
    + intro H5. apply H1. apply in_or_app. by left.
  - repeat rewrite expr_conv_subst_upd_swap; vauto.
    + intro H5. apply H1. apply in_or_app. by right.
    + intro H5. apply H1. apply in_or_app. by left.
Qed.

Lemma cond_conv_agree :
  forall B s1 s2,
    (forall x, In x (cond_fv B) -> s1 x = s2 x) ->
  cond_conv B s1 = cond_conv B s2.
Proof.
  induction B as [b|B' IH|B1 IH1 B2 IH2|E1 E2];
  intros s1 s2 H1; vauto.
  - simpl. rewrite IH with s1 s2; vauto.
  - simpl. rewrite IH1 with s1 s2, IH2 with s1 s2; auto.
    + intros x H2. apply H1. simpl. apply in_app_iff. by right.
    + intros x H2. apply H1. simpl. apply in_app_iff. by left.
  - simpl. repeat rewrite expr_conv_agree with (s1 := s1)(s2 := s2); vauto.
    + intros x H2. apply H1. simpl. apply in_app_iff. by right.
    + intros x H2. apply H1. simpl. apply in_app_iff. by left.
Qed.

(** ** Shared-memory accesses *)

(** The operation [cmd_acc C] yields all heap locations that [C] can
    _access_ in a single computation step. The operation [cmd_writes C]
    yields all heap locations that [C] can _write to_ in a singles step.
    In both operations, heap allocation is not considered, as the heap cell
    is not yet allocated. *)

Fixpoint cmd_acc (C: Cmd)(s: Store): list Val :=
  match C with
    | Cskip => []
    | Cseq C' _ => cmd_acc C' s
    | Cass _ _ => []
    | Cread _ E => [expr_eval E s]
    | Cwrite E _ => [expr_eval E s]
    | Cite _ _ _ => []
    | Cwhile _ _ => []
    | Cpar C1 C2 => cmd_acc C1 s ++ cmd_acc C2 s
    | Calloc _ _ => []
    | Cdispose E => [expr_eval E s]
    | Csend _ _ => []
    | Crecv1 _ _ => []
    | Crecv2 _ _ => []
    | Cquery _ => []
  end.

Fixpoint cmd_writes (C: Cmd)(s: Store): list Val :=
  match C with
    | Cskip => []
    | Cseq C' _ => cmd_writes C' s
    | Cass _ _ => []
    | Cread _ _ => []
    | Cwrite E _ => [expr_eval E s]
    | Cite _ _ _ => []
    | Cwhile _ _ => []
    | Cpar C1 C2 => cmd_writes C1 s ++ cmd_writes C2 s
    | Calloc _ _ => []
    | Cdispose E => [expr_eval E s]
    | Csend _ _ => []
    | Crecv1 _ _ => []
    | Crecv2 _ _ => []
    | Cquery _ => []
  end.

Lemma cmd_writes_acc :
  forall C s l, In l (cmd_writes C s) -> In l (cmd_acc C s).
Proof.
  induction C; intros s l H; simpls; vauto.
  - by apply IHC1.
  - apply in_app_iff in H. apply in_app_iff.
    destruct H as [H|H].
    + left. by apply IHC1.
    + right. by apply IHC2.
Qed.

(** ** Small-step operational semantics *)

Inductive Label :=
  (* assertions *)
  | Lquery(b: bool)
  (* explicit send *)
  | Lsend(v: Val)(tag: Val)
  (* explicit receive *)
  | Lrecv(v: Val)(tag: Val)
  (* explicit communication *)
  | Lcomm(v: Val)(tag: Val)
  (* internal computation *)
  | Lcomp.

Add Search Blacklist "Label_rect".
Add Search Blacklist "Label_ind".
Add Search Blacklist "Label_rec".

Inductive step : Cmd -> Heap -> Store -> Label -> Cmd -> Heap -> Store -> Prop :=
  (* sequential composition *)
  | step_seq_l C1 h s l C1' h' s' C2 :
    step C1 h s l C1' h' s' -> step (Cseq C1 C2) h s l (Cseq C1' C2) h' s'
  | step_seq_r C h s :
    step (Cseq Cskip C) h s Lcomp C h s
  (* assignment *)
  | step_ass x E h s :
    let v := expr_eval E s in
    step (Cass x E) h s Lcomp Cskip h (updatestore s x v)
  (* heap reading *)
  | step_read x E v h s :
    h (expr_eval E s) = Some v ->
    step (Cread x E) h s Lcomp Cskip h (updatestore s x v)
  (* heap writing *)
  | step_write E1 E2 h s :
    let l := expr_eval E1 s in
    let v := expr_eval E2 s in
    h l <> None ->
    step (Cwrite E1 E2) h s Lcomp Cskip (updateheap h l (Some v)) s
  (* if-then-else *)
  | step_ite_l B C1 C2 h s :
    cond_eval B s -> step (Cite B C1 C2) h s Lcomp C1 h s
  | step_ite_r B C1 C2 h s :
    ~ cond_eval B s -> step (Cite B C1 C2) h s Lcomp C2 h s
  (* while loops *)
  | step_while B C h s :
    step (Cwhile B C) h s Lcomp (Cite B (Cseq C (Cwhile B C)) Cskip) h s
  (* heap allocation *)
  | step_alloc x E l h s :
    let v := expr_eval E s in
    h l = None ->
    step (Calloc x E) h s Lcomp Cskip (updateheap h l (Some v)) (updatestore s x l)
  (* heap disposal *)
  | step_dispose E h s :
    let l := expr_eval E s in
    step (Cdispose E) h s Lcomp Cskip (updateheap h l None) s
  (* parallel *)
  | step_par_l C1 C2 h s l C1' h' s' :
    step C1 h s l C1' h' s' ->
    step (Cpar C1 C2) h s l (Cpar C1' C2) h' s'
  | step_par_r C1 C2 h s l C2' h' s' :
    step C2 h s l C2' h' s' ->
    step (Cpar C1 C2) h s l (Cpar C1 C2') h' s'
  | step_par_done h s :
    step (Cpar Cskip Cskip) h s Lcomp Cskip h s
  (* sending *)
  | step_send E T h s :
    let v := expr_eval E s in
    let tag := expr_eval T s in
    step (Csend E T) h s (Lsend v tag) Cskip h s
  (* receiving *)
  | step_recv1 x y v1 v2 h s :
    step (Crecv1 x y) h s (Lrecv v1 v2) Cskip h (updatestore (updatestore s x v1) y v2)
  | step_recv2 x T v h s :
    let tag := expr_eval T s in
    step (Crecv2 x T) h s (Lrecv v tag) Cskip h (updatestore s x v)
  (* communication *)
  | step_comm_l C1 C2 h s C1' C2' s' v tag :
    step C1 h s (Lsend v tag) C1' h s ->
    step C2 h s (Lrecv v tag) C2' h s' ->
    step (Cpar C1 C2) h s (Lcomm v tag) (Cpar C1' C2') h s'
  | step_comm_r C1 C2 h s C1' C2' s' v tag :
    step C1 h s (Lrecv v tag) C1' h s' ->
    step C2 h s (Lsend v tag) C2' h s ->
    step (Cpar C1 C2) h s (Lcomm v tag) (Cpar C1' C2') h s'
  (* querying *)
  | step_query B h s :
    step (Cquery B) h s (Lquery (cond_eval B s)) (Cskip) h s.

Add Search Blacklist "step_ind".

Lemma prog_sos_neg_C :
  forall C h s l h' s', ~ step C h s l C h' s'.
Proof.
  induction C; intros h s l h' s' STEP; vauto; inv STEP; clear STEP.
  - by apply IHC1 in H7.
  - by apply cmd_neg_seq in H5.
  - by apply cmd_neg_ite_t in H5.
  - by apply cmd_neg_ite_f in H5.
  - by apply IHC1 in H7.
  - by apply IHC2 in H7.
  - by apply IHC1 in H8.
  - by apply IHC1 in H8.
Qed.

Lemma step_heap_finite :
  forall C h s l C' h' s',
  step C h s l C' h' s' -> heap_finite h -> heap_finite h'.
Proof.
  induction C; intros h s l C' h' s' STEP FIN; inv STEP; vauto.
  - by apply IHC1 in H7.
  - by apply heap_finite_upd.
  - by apply IHC1 in H7.
  - by apply IHC2 in H7.
  - by apply heap_finite_upd.
  - by apply heap_finite_upd.
Qed.

Lemma step_send_state :
  forall C h s v tag C' h' s',
  step C h s (Lsend v tag) C' h' s' -> h = h' /\ s = s'.
Proof.
  induction C; intros h s v tag C' h' s' STEP; inv STEP; clear STEP.
  - by apply IHC1 in H7.
  - by apply IHC1 in H7.
  - by apply IHC2 in H7.
Qed.

Lemma step_fv_mod :
  forall C h s l C' h' s',
  step C h s l C' h' s' ->
    (forall x, In x (cmd_fv C') -> In x (cmd_fv C)) /\
    (forall x, In x (cmd_mod C') -> In x (cmd_mod C)) /\
    (forall x, ~ In x (cmd_mod C) -> s x = s' x).
Proof.
  induction C; intros h s l C' h' s' STEP.
  (* skip *)
  - repeat split; intros x H1; inv STEP.
  (* sequential composition *)
  - repeat split; intros x H; simpls.
    + inv STEP. clear STEP. simpl in H.
      apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply IHC1 in H8.
        destruct H8 as (H8 & _). by apply H8.
      * apply in_app_iff. by right.
    + inv STEP; clear STEP.
      * simpl in H. apply in_app_iff in H.
        destruct H as [H | H].
        ** apply IHC1 in H8. destruct H8 as (_ & H8 & _).
           apply in_app_iff. left. by apply H8.
        ** apply in_app_iff. by right.
    + inv STEP. clear STEP. apply IHC1 in H8.
      destruct H8 as (_ & _ & H8). apply H8.
      intro H1. apply H. apply in_app_iff. by left.
  (* assign *)
  - inv STEP. repeat split; simpls. intros y H1.
    apply not_or_and in H1. destruct H1 as (H1 & _).
    unfold updatestore, update. desf.
  (* heap reading *)
  - inv STEP. repeat split; simpls. intros y H1.
    apply not_or_and in H1. destruct H1 as (H1 & _).
    unfold updatestore, update. desf.
  (* heap writing *)
  - inv STEP.
  (* if-then-else *)
  - inv STEP; repeat split; simpls.
    + intros x H1. apply in_app_iff. right.
      apply in_app_iff. by left.
    + intros x H1. apply in_app_iff. by left.
    + intros x H1. apply in_app_iff. right.
      apply in_app_iff. by right.
    + intros x H1. apply in_app_iff. by right.
  (* while loops *)
  - inv STEP; repeat split; simpls.
    + intros x H1. apply in_app_iff in H1.
      destruct H1 as [H1 | H1].
      * apply in_app_iff. by left.
      * apply in_app_iff in H1. desf.
        apply in_app_iff in H1. destruct H1 as [H1 | H1]; auto.
        apply in_app_iff. by right.
    + intros x H1. apply in_app_iff in H1. desf.
      apply in_app_iff in H1. desf.
  (* parallel composition *)
  - inv STEP; clear STEP; repeat split; simpls.
    + intros x H1. apply in_app_iff. apply in_app_iff in H1. intuition.
      left. apply IHC1 in H7. destruct H7 as (H7 & _). by apply H7.
    + intros x H1. apply in_app_iff. apply in_app_iff in H1. intuition.
      left. apply IHC1 in H7. destruct H7 as (_ & H7 & _). by apply H7.
    + intros x H1. apply IHC1 in H7. destruct H7 as (_ & _ & H7).
      apply H7. intro H2. apply H1. apply in_app_iff. by left.
    + intros x H1. apply in_app_iff. apply in_app_iff in H1. intuition.
      right. apply IHC2 in H7. destruct H7 as (H7 & _). by apply H7.
    + intros x H1. apply in_app_iff. apply in_app_iff in H1. intuition.
      right. apply IHC2 in H7. destruct H7 as (_ & H7 & _). by apply H7.
    + intros x H1. apply IHC2 in H7. destruct H7 as (_ & _ & H7).
      apply H7. intro H2. apply H1. apply in_app_iff. by right.
    + intros x H2. apply in_app_iff in H2. destruct H2 as [H2 | H2].
      * apply in_app_iff. left. apply IHC1 in H1. destruct H1 as (H1 & _).
        by apply H1.
      * apply in_app_iff. right. apply IHC2 in H8. destruct H8 as (H8 & _).
        by apply H8.
    + intros x H2. apply in_app_iff in H2. destruct H2 as [H2 | H2].
      * apply in_app_iff. left. apply IHC1 in H1. destruct H1 as (_ & H1 & _).
        by apply H1.
      * apply in_app_iff. right. apply IHC2 in H8. destruct H8 as (_ & H8 & _).
        by apply H8.
    + intros x H2. rewrite in_app_iff in H2. apply not_or_and in H2.
      destruct H2 as (H2 & H3). apply IHC2 in H8. destruct H8 as (_ & _ & H8).
      by apply H8.
    + intros x H2. apply in_app_iff in H2. destruct H2 as [H2 | H2].
      * apply in_app_iff. left. apply IHC1 in H1. destruct H1 as (H1 & _).
        by apply H1.
      * apply in_app_iff. right. apply IHC2 in H8. destruct H8 as (H8 & _).
        by apply H8.
    + intros x H2. apply in_app_iff in H2. destruct H2 as [H2 | H2].
      * apply in_app_iff. left. apply IHC1 in H1. destruct H1 as (_ & H1 & _).
        by apply H1.
      * apply in_app_iff. right. apply IHC2 in H8. destruct H8 as (_ & H8 & _).
        by apply H8.
    + intros x H2. rewrite in_app_iff in H2. apply not_or_and in H2.
      destruct H2 as (H2 & H3). apply IHC1 in H1. destruct H1 as (_ & _ & H1).
      by apply H1.
  (* heap allocation *)
  - inv STEP. rename l0 into l'. repeat split; simpls.
    intros y H1. apply not_or_and in H1. destruct H1 as (H1 & _).
    unfold updatestore, update. desf.
  (* heap disposal *)
  - inv STEP.
  (* sending *)
  - inv STEP.
  (* receiving *)
  - inv STEP. repeat split; simpls. intros z H1.
    unfold updatestore, update. desf.
    + apply not_or_and in H1. destruct H1 as (_ & H1).
      apply not_or_and in H1. desf.
    + apply not_or_and in H1. desf.
  - inv STEP. repeat split; simpls. intros y H1.
    apply not_or_and in H1. destruct H1 as (H1 & _).
    unfold updatestore, update. desf.
  (* querying *)
  - inv STEP.
Qed.

Lemma step_agree :
  forall C h s1 s2 l C' h' s1' (phi: Var -> Prop),
    (forall x, In x (cmd_fv C) -> phi x) ->
    (forall x, phi x -> s1 x = s2 x) ->
    step C h s1 l C' h' s1' ->
  exists s2',
    (forall x, phi x -> s1' x = s2' x) /\
    step C h s2 l C' h' s2'.
Proof.
  induction C; intros h s1 s2 l C' h' s1' phi H1 H2 STEP.
  (* skip *)
  - inv STEP.
  (* sequential composition *)
  - inv STEP.
    + apply IHC1 with (s2 := s2)(phi := phi) in H9; vauto.
      * destruct H9 as (s2' & H3 & STEP').
        exists s2'. intuition vauto.
      * intros x H. apply H1. simpl. apply in_app_iff. by left.
    + exists s2. intuition vauto.
  (* assignment *)
  - inv STEP.
    exists (updatestore s2 x (expr_eval E s2)). split; vauto.
    + intros y H. unfold updatestore, update.
      destruct (var_eq_dec x y); vauto.
      * rewrite <- expr_agree with (s1 := s1); vauto.
        unfold store_agree. intros x H'.
        apply H2, H1. by right.
      * by apply H2.
  (* heap reading *)
  - inv STEP.
    rewrite expr_agree with (s2 := s2) in H9; vauto.
    + exists (updatestore s2 x v). split; vauto.
      intros y H3. unfold updatestore, update.
      destruct (var_eq_dec x y); auto.
    + red. intros y H3. apply H2. apply H1. simpl. by right.
  (* heap writing *)
  - inv STEP. subst l1 l0 v0 v.
    exists s2. split; vauto.
    repeat rewrite expr_agree with (s1 := s1')(s2 := s2); intuition.
    + constructor. intro H3. apply H9.
      rewrite expr_agree with (s2 := s2); auto. red. intros y H4.
      apply H2. apply H1. simpl. apply in_app_iff. by left.
    + red. intros y H4. apply H2. apply H1. simpl.
      apply in_app_iff. by right.
    + red. intros y H4. apply H2. apply H1. simpl.
      apply in_app_iff. by left.
  (* if-then-else *)
  - inv STEP; vauto.
    + exists s2. split; vauto. constructor.
      rewrite <- cond_agree with (s1 := s1'); auto.
      red. ins. apply H2, H1. apply in_app_iff. by left.
    + exists s2. split; vauto. constructor.
      rewrite <- cond_agree with (s1 := s1'); auto.
      red. ins. apply H2, H1. apply in_app_iff. by left.
  (* while loops *)
  - inv STEP. exists s2. intuition. constructor.
  (* parallel composition *)
  - inv STEP; clear STEP.
    + apply IHC1 with (s2 := s2)(phi := phi) in H9; vauto.
      * destruct H9 as (s2' & H3 & H4).
        exists s2'. split; vauto.
      * intros x H. apply H1. simpl. apply in_app_iff. by left.
    + apply IHC2 with (s2 := s2)(phi := phi) in H9; vauto.
      * destruct H9 as (s2' & H3 & H4).
        exists s2'. split; vauto.
      * intros x H. apply H1. simpl. apply in_app_iff. by right.
    + exists s2. intuition. constructor.
    + apply IHC2 with (s2 := s2)(phi := phi) in H10; vauto.
      * destruct H10 as (s2' & H4 & H5).
        exists s2'. intuition. constructor; vauto.
        apply IHC1 with (s2 := s2)(phi := phi) in H3; desf; intuition.
        ** generalize H0. intro H0'.
           apply step_send_state in H0. desf.
        ** apply H1. simpl. apply in_app_iff. by left.
      * intros y H4. apply H1. simpl.
        apply in_app_iff. by right.
    + apply IHC1 with (s2 := s2)(phi := phi) in H3; vauto.
      * destruct H3 as (s2' & H4 & H5).
        exists s2'. intuition.
        apply step_comm_r; vauto.
        apply IHC2 with (s2 := s2)(phi := phi) in H10; desf; intuition.
        ** generalize H0. intro H0'.
           apply step_send_state in H0. desf.
        ** apply H1. simpl. apply in_app_iff. by right.
      * intros y H4. apply H1. simpl.
        apply in_app_iff. by left.
  (* heap allocation *)
  - inv STEP. rename l0 into l'. subst v.
    rewrite expr_agree with (s2 := s2).
    + exists (updatestore s2 x l').
      split; vauto. intros y H3.
      unfold updatestore, update.
      destruct (var_eq_dec x y); auto.
    + red. intros y H3. apply H2, H1. simpl. by right.
  (* heap disposal *)
  - inv STEP. subst l0 l1. exists s2. split; vauto.
    rewrite expr_agree with (s2 := s2); vauto.
    red. intros x H3. by apply H2, H1.
  (* sending *)
  - inv STEP. subst v0 v tag tag0. exists s2. intuition.
    rewrite expr_agree with (s2 := s2); vauto.
    + rewrite expr_agree with (E := T)(s2 := s2); vauto. red.
      intros x H3. apply H2, H1. simpl.
      apply in_app_iff. by right.
    + red. intros x H3. apply H2, H1. simpl.
      apply in_app_iff. by left.
  (* receiving *)
  - inv STEP. exists (updatestore (updatestore s2 x v1) y v2).
    intuition vauto. unfold updatestore, update. desf. by apply H2.
  - inv STEP. subst tag. exists (updatestore s2 x v). intuition.
    + unfold updatestore, update. desf. apply H2. done.
    + rewrite expr_agree with T s1 s2; vauto. red.
      intros y H3. apply H2, H1. simpl. by right.
  (* querying *)
  - inv STEP. exists s2. intuition.
    rewrite cond_agree with (s2 := s2); vauto.
    red. intros x H3. apply H2, H1. vauto.
Qed.

(** ** Fault semantics *)

(** The predicate [fault C h s] determines whether [C] can perform a
    data race or memory violation in the next computation step. *)

Inductive fault : Cmd -> Heap -> Store -> Prop :=
  (* heap reading *)
  | fault_read x E h s :
    h (expr_eval E s) = None -> fault (Cread x E) h s
  (* heap writing  *)
  | fault_write E1 E2 h s :
    h (expr_eval E1 s) = None -> fault (Cwrite E1 E2) h s
  (* heap allocation *)
  | fault_alloc x E h s :
    (forall l: Val, h l <> None) -> fault (Calloc x E) h s
  (* heap disposal *)
  | fault_dispose E h s :
    h (expr_eval E s) = None -> fault (Cdispose E) h s
  (* parallel *)
  | fault_par_l C1 C2 h s :
    fault C1 h s -> fault (Cpar C1 C2) h s
  | fault_par_r C1 C2 h s :
    fault C2 h s -> fault (Cpar C1 C2) h s
  (* sequential composition *)
  | fault_seq C1 C2 h s :
    fault C1 h s -> fault (Cseq C1 C2) h s
  (* data races *)
  | fault_race_l C1 C2 h s :
    ~ disjoint (cmd_writes C1 s) (cmd_acc C2 s) -> fault (Cpar C1 C2) h s
  | fault_race_r C1 C2 h s :
    ~ disjoint (cmd_acc C1 s) (cmd_writes C2 s) -> fault (Cpar C1 C2) h s.

Add Search Blacklist "fault_ind".

Theorem step_progress :
  forall C h s,
  ~ fault C h s -> C = Cskip \/ exists l C' h' s', step C h s l C' h' s'.
Proof.
  induction C; intros h s ABORT.
  (* empty programs *)
  - by left.
  (* sequential composition *)
  - assert (H1: C1 = Cskip \/ ~ C1 = Cskip) by apply classic.
    right. destruct H1 as [H1 | H1].
    + clarify. exists Lcomp, C2, h, s. vauto.
    + assert (H2: ~ fault C1 h s) by (intro H2; apply ABORT; vauto).
      apply IHC1 in H2. destruct H2 as [H2 | H2]; vauto.
      destruct H2 as (l & C1' & h' & s' & STEP).
      exists l, (Cseq C1' C2), h', s'. vauto.
  (* assignment *)
  - right. exists Lcomp, Cskip, h, (updatestore s x (expr_eval E s)).
    constructor.
  (* heap reading *)
  - assert (H1: exists v, h (expr_eval E s) = Some v)
      by (rewrite <- option_not_none; intro H1; apply ABORT; vauto).
    right. destruct H1 as (v & H1).
    exists Lcomp, Cskip, h, (updatestore s x v). vauto.
  (* heap writing *)
  - assert (H1: exists v, h (expr_eval E1 s) = Some v)
      by (rewrite <- option_not_none; intro H1; apply ABORT; vauto).
    right. destruct H1 as (v & H1).
    exists Lcomp, Cskip, (updateheap h (expr_eval E1 s) (Some (expr_eval E2 s))), s.
    constructor. apply option_not_none. by exists v.
  (* if-then-else *)
  - assert (H1: cond_eval B s = true \/ cond_eval B s = false)
      by (rewrite <- Bool.not_true_iff_false; apply classic).
    right. destruct H1 as [H1 | H1].
    + exists Lcomp, C1, h, s. by apply step_ite_l.
    + exists Lcomp, C2, h, s. apply step_ite_r. vauto.
  (* while loops *)
  - right. exists Lcomp, (Cite B (Cseq C (Cwhile B C)) Cskip), h, s. vauto.
  (* parallel composition *)
  - assert (H1: C1 = Cskip \/ ~ C1 = Cskip) by apply classic.
    assert (H2: C2 = Cskip \/ ~ C2 = Cskip) by apply classic.
    destruct H1 as [H1|H1], H2 as [H2|H2]; clarify.
    + right. exists Lcomp, Cskip, h, s. vauto.
    + assert (H3: C2 = Cskip \/ exists l C2' h' s', step C2 h s l C2' h' s')
        by (apply IHC2; intro; apply ABORT; vauto).
      destruct H3 as [H3|(l&C2'&h'&s'&H3)]; vauto.
      right. exists l, (Cpar Cskip C2'), h', s'. vauto.
    + assert (H3: C1 = Cskip \/ exists l C1' h' s', step C1 h s l C1' h' s')
        by (apply IHC1; intro; apply ABORT; vauto).
      destruct H3 as [H3|(l&C1'&h'&s'&H3)]; vauto.
      right. exists l, (Cpar C1' Cskip), h', s'. vauto.
    + assert (H3: C1 = Cskip \/ exists l C1' h' s', step C1 h s l C1' h' s')
        by (apply IHC1; intro; apply ABORT; vauto).
      destruct H3 as [H3|(l&C1'&h'&s'&H3)]; vauto.
      right. exists l, (Cpar C1' C2), h', s'. vauto.
  (* heap allocation *)
  - assert (H1: ~ forall v, h v <> None) by (intro; apply ABORT; vauto).
    right. apply not_all_not_ex in H1. destruct H1 as (v & H1).
    exists Lcomp, Cskip, (updateheap h v (Some (expr_eval E s))), (updatestore s x v).
    vauto.
  (* heap disposal *)
  - right. exists Lcomp, Cskip, (updateheap h (expr_eval E s) None), s. vauto.
  (* sending *)
  - right. exists (Lsend (expr_eval E s) (expr_eval T s)), Cskip, h, s. vauto.
  (* receiving *)
  - right. exists (Lrecv val_unit val_unit).
    exists Cskip, h, (updatestore (updatestore s x val_unit) y val_unit). vauto.
  - right. exists (Lrecv val_unit (expr_eval T s)).
    exists Cskip, h, (updatestore s x val_unit). vauto.
  (* querying *)
  - right. exists (Lquery (cond_eval B s)), Cskip, h, s. vauto.
Qed.

End Programs.
