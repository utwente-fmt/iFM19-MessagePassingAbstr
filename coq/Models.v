Require Import HahnBase.
Require Import Heaps.
Require Import List.
Require Import Prelude.
Require Import Permissions.
Require Import Processes.
Require Import Programs.
Require Import QArith.
Require Import Qcanon.
Require Import Utf8.

Import ListNotations.

Set Implicit Arguments.

(** * Models *)

Module Type Models
  (doms: Domains)
  (procs: Processes doms)
  (heaps: Heaps doms)
  (progs: Programs doms procs heaps).

Export doms procs heaps progs.

(** ** Abstract Processes *)

(** Abstract processes have the same structure as [Proc], but are allowed to
    contain program expressions. Abstract processes can be converted to concrete
    processes using [aproc_conv]. *)

(** *** Statics *)

Inductive AbstrProc :=
  | APdelta
  | APepsilon
  | APsend(E T: Expr)
  | APrecv(E T: Expr)
  | APassn(B: Cond)
  | APseq(P1 P2: AbstrProc)
  | APalt(P1 P2: AbstrProc)
  | APpar(P1 P2: AbstrProc)
  | APsum(f: Val -> AbstrProc)
  | APcond(B: Cond)(P: AbstrProc)
  | APiter(P: AbstrProc).

Add Search Blacklist "AbstrProc_rect".
Add Search Blacklist "AbstrProc_ind".
Add Search Blacklist "AbstrProc_rec".

Lemma aproc_sum_ext : forall f g, f = g -> APsum f = APsum g.
Proof. intuition vauto. Qed.

Fixpoint aproc_fv (AP: AbstrProc)(x: Var): Prop :=
  match AP with
    | APdelta => False
    | APepsilon => False
    | APsend E T => In x (expr_fv E ++ expr_fv T)
    | APrecv E T => In x (expr_fv E ++ expr_fv T)
    | APassn B => In x (cond_fv B)
    | APseq AP1 AP2 => aproc_fv AP1 x \/ aproc_fv AP2 x
    | APalt AP1 AP2 => aproc_fv AP1 x \/ aproc_fv AP2 x
    | APpar AP1 AP2 => aproc_fv AP1 x \/ aproc_fv AP2 x
    | APsum f => exists v: Val, aproc_fv (f v) x
    | APcond B AP' => In x (cond_fv B) \/ aproc_fv AP' x
    | APiter AP' => aproc_fv AP' x
  end.

Definition aproc_closed (AP: AbstrProc): Prop :=
  forall x: Var, ~ aproc_fv AP x.

Lemma aproc_closed_seq :
  forall AP1 AP2,
  aproc_closed (APseq AP1 AP2) <-> aproc_closed AP1 /\ aproc_closed AP2.
Proof.
  intros AP1 AP2. split; intro H1.
  - red in H1. simpl in H1. split.
    + red. intros x H2. apply H1 with x. by left.
    + red. intros x H2. apply H1 with x. by right.
  - destruct H1 as (H1 & H2). red. intros x H3.
    simpl in H3. destruct H3 as [H3 | H3].
    + by apply H1 with x.
    + by apply H2 with x.
Qed.

Lemma aproc_closed_alt :
  forall AP1 AP2,
  aproc_closed (APalt AP1 AP2) <-> aproc_closed AP1 /\ aproc_closed AP2.
Proof.
  intros AP1 AP2. split; intro H1.
  - red in H1. simpl in H1. split.
    + red. intros x H2. apply H1 with x. by left.
    + red. intros x H2. apply H1 with x. by right.
  - destruct H1 as (H1 & H2). red. intros x H3.
    simpl in H3. destruct H3 as [H3 | H3].
    + by apply H1 with x.
    + by apply H2 with x.
Qed.

Lemma aproc_closed_par :
  forall AP1 AP2,
  aproc_closed (APpar AP1 AP2) <-> aproc_closed AP1 /\ aproc_closed AP2.
Proof.
  intros AP1 AP2. split; intro H1.
  - red in H1. simpl in H1. split.
    + red. intros x H2. apply H1 with x. by left.
    + red. intros x H2. apply H1 with x. by right.
  - destruct H1 as (H1 & H2). red. intros x H3.
    simpl in H3. destruct H3 as [H3 | H3].
    + by apply H1 with x.
    + by apply H2 with x.
Qed.

Fixpoint aproc_conv (AP: AbstrProc)(s: Store): Proc :=
  match AP with
    | APdelta => Pdelta
    | APepsilon => Pepsilon
    | APsend E T => Psend (expr_conv E s) (expr_conv T s)
    | APrecv E T => Precv (expr_conv E s) (expr_conv T s)
    | APassn B => Passn (cond_conv B s)
    | APseq AP1 AP2 => Pseq (aproc_conv AP1 s) (aproc_conv AP2 s)
    | APalt AP1 AP2 => Palt (aproc_conv AP1 s) (aproc_conv AP2 s)
    | APpar AP1 AP2 => Ppar (aproc_conv AP1 s) (aproc_conv AP2 s)
    | APsum f => Psum (fun v => aproc_conv (f v) s)
    | APcond B AP' => Pcond (cond_conv B s) (aproc_conv AP' s)
    | APiter AP' => Piter (aproc_conv AP' s)
  end.

Lemma aproc_conv_closed :
  forall AP s1 s2,
  aproc_closed AP -> aproc_conv AP s1 = aproc_conv AP s2.
Proof.
  induction AP; intros s1 s2 H1; simpls; vauto.
  (* sending *)
  - rewrite expr_conv_closed with E s1 s2, expr_conv_closed with T s1 s2; auto.
    + unfold aproc_closed in H1. simpl in H1.
      red. apply list_forall_notin in H1.
      apply app_eq_nil in H1. desf.
    + unfold aproc_closed in H1. simpl in H1.
      red. apply list_forall_notin in H1.
      apply app_eq_nil in H1. desf.
  (* receiving *)
  - rewrite expr_conv_closed with E s1 s2, expr_conv_closed with T s1 s2; auto.
    + unfold aproc_closed in H1. simpl in H1.
      red. apply list_forall_notin in H1.
      apply app_eq_nil in H1. desf.
    + unfold aproc_closed in H1. simpl in H1.
      red. apply list_forall_notin in H1.
      apply app_eq_nil in H1. desf.
  (* assertions *)
  - rewrite cond_conv_closed with B s1 s2; auto.
    red in H1. red. by apply list_forall_notin in H1.
  (* sequential composition *)
  - apply aproc_closed_seq in H1. destruct H1 as (H1 & H2).
    rewrite IHAP1 with s1 s2, IHAP2 with s1 s2; auto.
  (* choice *)
  - apply aproc_closed_alt in H1. destruct H1 as (H1 & H2).
    rewrite IHAP1 with s1 s2, IHAP2 with s1 s2; auto.
  (* parallel composition *)
  - apply aproc_closed_par in H1. destruct H1 as (H1 & H2).
    rewrite IHAP1 with s1 s2, IHAP2 with s1 s2; auto.
  (* summation *)
  - red in H1. simpl in H1. apply proc_sum_ext.
    apply functional_extensionality. intro x.
    apply H. red. intros y H2. specialize H1 with y.
    apply H1. by exists x.
  (* conditionals *)
  - rewrite cond_conv_closed with (s2 := s2), IHAP with (s2 := s2); auto.
    + red in H1. red. intros x H2. specialize H1 with x.
      apply H1. simpl. by right.
    + red in H1. red. simpl in H1.
      assert (H2: forall x, ~ In x (cond_fv B)). {
        intros x H2. apply H1 with x. by left. }
      by apply list_forall_notin in H2.
  (* iteration *)
  - rewrite IHAP with s1 s2; vauto.
Qed.

Fixpoint aproc_subst (x: Var)(E: Expr)(AP: AbstrProc): AbstrProc :=
  match AP with
    | APdelta => APdelta
    | APepsilon => APepsilon
    | APsend E' T => APsend (expr_subst x E E') (expr_subst x E T)
    | APrecv E' T => APrecv (expr_subst x E E') (expr_subst x E T)
    | APassn B => APassn (cond_subst x E B)
    | APseq AP1 AP2 => APseq (aproc_subst x E AP1) (aproc_subst x E AP2)
    | APalt AP1 AP2 => APalt (aproc_subst x E AP1) (aproc_subst x E AP2)
    | APpar AP1 AP2 => APpar (aproc_subst x E AP1) (aproc_subst x E AP2)
    | APsum f => APsum (fun v => aproc_subst x E (f v))
    | APcond B AP' => APcond (cond_subst x E B) (aproc_subst x E AP')
    | APiter AP' => APiter (aproc_subst x E AP')
  end.

Definition APsigma (x: Var)(AP: AbstrProc): AbstrProc :=
  APsum (fun v => aproc_subst x (Econst v) AP).

Lemma aproc_subst_pres :
  forall AP x E, ~ aproc_fv AP x -> aproc_subst x E AP = AP.
Proof.
  induction AP; intros x E' H1; simpls; vauto.
  (* sending *)
  - repeat rewrite expr_subst_pres; auto.
    + intro H2. apply H1. apply in_app_iff. by right.
    + intro H2. apply H1. apply in_app_iff. by left.
  (* receiving *)
  - repeat rewrite expr_subst_pres; auto.
    + intro H2. apply H1. apply in_app_iff. by right.
    + intro H2. apply H1. apply in_app_iff. by left.
  (* assertions *)
  - rewrite cond_subst_pres; auto.
  (* sequential *)
  - rewrite IHAP1, IHAP2; auto.
  (* choice *)
  - rewrite IHAP1, IHAP2; auto.
  (* parallel *)
  - rewrite IHAP1, IHAP2; auto.
  (* summation *)
  - apply aproc_sum_ext. extensionality y.
    rewrite H; auto. intro H2. apply H1. by exists y.
  (* conditionals *)
  - rewrite cond_subst_pres; auto.
    rewrite IHAP; vauto. intro H2. apply H1. by right.
  (* iteration *)
  - by rewrite IHAP.
Qed.

Lemma aproc_fv_subst_notin :
  forall AP E x,
  ~ In x (expr_fv E) -> ~ aproc_fv (aproc_subst x E AP) x.
Proof.
  induction AP; intros E' x H1 H2; simpls; vauto.
  (* sending *)
  - apply in_app_or in H2. destruct H2 as [H2 | H2].
    + apply expr_fv_subst_notin with (E := E) in H1. vauto.
    + apply expr_fv_subst_notin with (E := T) in H1. vauto.
  (* receiving *)
  - apply in_app_or in H2. destruct H2 as [H2 | H2].
    + apply expr_fv_subst_notin with (E := E) in H1. vauto.
    + apply expr_fv_subst_notin with (E := T) in H1. vauto.
  (* querying *)
  - apply cond_fv_subst_notin with (B := B) in H1. vauto.
  (* sequential composition *)
  - destruct H2 as [H2 | H2].
    + apply IHAP1 in H2; vauto.
    + apply IHAP2 in H2; vauto.
  (* choice *)
  - destruct H2 as [H2 | H2].
    + apply IHAP1 in H2; vauto.
    + apply IHAP2 in H2; vauto.
  (* parallel composition *)
  - destruct H2 as [H2 | H2].
    + apply IHAP1 in H2; vauto.
    + apply IHAP2 in H2; vauto.
  (* summation *)
  - destruct H2 as (v & H2). apply H in H2; vauto.
  (* condition *)
  - destruct H2 as [H2 | H2].
    + apply cond_fv_subst_notin with (B := B) in H1. vauto.
    + apply IHAP in H2; vauto.
  (* iteration *)
  - apply IHAP in H2; vauto.
Qed.

Lemma aproc_fv_subst_in :
  forall AP E x y,
  ~ x = y ->
  ~ In x (expr_fv E) ->
  aproc_fv (aproc_subst y E AP) x <-> aproc_fv AP x.
Proof.
  induction AP; intros E' x y H1 H2; simpls.
  (* sending *)
  - split; intro H3.
    + apply in_app_or in H3. destruct H3 as [H3 | H3].
      * apply in_or_app. left. by apply expr_fv_subst_in in H3.
      * apply in_or_app. right. by apply expr_fv_subst_in in H3.
    + apply in_app_or in H3. destruct H3 as [H3 | H3].
      * apply in_or_app. left. apply expr_fv_subst_in; vauto.
      * apply in_or_app. right. apply expr_fv_subst_in; vauto.
  (* receiving *)
  - split; intro H3.
    + apply in_app_or in H3. destruct H3 as [H3 | H3].
      * apply in_or_app. left. by apply expr_fv_subst_in in H3.
      * apply in_or_app. right. by apply expr_fv_subst_in in H3.
    + apply in_app_or in H3. destruct H3 as [H3 | H3].
      * apply in_or_app. left. apply expr_fv_subst_in; vauto.
      * apply in_or_app. right. apply expr_fv_subst_in; vauto.
  (* querying *)
  - split; intro H3.
    + by apply cond_fv_subst_in in H3.
    + by apply cond_fv_subst_in.
  (* sequential composition *)
  - split; intro H3.
    + destruct H3 as [H3 | H3].
      * apply IHAP1 in H3; vauto.
      * apply IHAP2 in H3; vauto.
    + destruct H3 as [H3 | H3].
      * left. apply IHAP1; vauto.
      * right. apply IHAP2; vauto.
  (* choice *)
  - split; intro H3.
    + destruct H3 as [H3 | H3].
      * apply IHAP1 in H3; vauto.
      * apply IHAP2 in H3; vauto.
    + destruct H3 as [H3 | H3].
      * left. apply IHAP1; vauto.
      * right. apply IHAP2; vauto.
  (* parallel composition *)
  - split; intro H3.
    + destruct H3 as [H3 | H3].
      * apply IHAP1 in H3; vauto.
      * apply IHAP2 in H3; vauto.
    + destruct H3 as [H3 | H3].
      * left. apply IHAP1; vauto.
      * right. apply IHAP2; vauto.
  (* summation *)
  - split; intro H3.
    + destruct H3 as (v & H3). apply H in H3; vauto.
    + destruct H3 as (v & H3). exists v. apply H; vauto.
  (* conditionals *)
  - split; intro H3.
    + destruct H3 as [H3 | H3].
      * apply cond_fv_subst_in in H3; vauto.
      * apply IHAP in H3; vauto.
    + destruct H3 as [H3 | H3].
      * left. apply cond_fv_subst_in; vauto.
      * right. apply IHAP; vauto.
  (* summation *)
  - split; intro H3.
    + apply IHAP in H3; vauto.
    + apply IHAP; vauto.
Qed.

Lemma aproc_conv_subst :
  forall AP x E s,
  bisim (aproc_conv (aproc_subst x E AP) s)
    (aproc_conv AP (updatestore s x (expr_eval E s))).
Proof.
  induction AP; intros x E' s; vauto.
  (* sending *)
  - unfold aproc_conv. simpls. apply bisim_send.
    + by repeat apply expr_conv_subst.
    + by repeat apply expr_conv_subst.
  (* receiving *)
  - unfold aproc_conv. simpls. apply bisim_recv.
    + by repeat apply expr_conv_subst.
    + by repeat apply expr_conv_subst.
  (* assertions *)
  - unfold aproc_conv. simpls. apply bisim_assn.
    by apply cond_conv_subst.
  (* sequential *)
  - simpl. by rewrite IHAP1, IHAP2.
  (* choice *)
  - simpl. by rewrite IHAP1, IHAP2.
  (* parallel *)
  - simpl. by rewrite IHAP1, IHAP2.
  (* summation *)
  - simpl. apply bisim_sum. red. auto.
  (* conditionals *)
  - simpl. rewrite IHAP. apply bisim_cond_eval; vauto.
    by apply cond_conv_subst.
  (* iteration *)
  - simpl. by rewrite IHAP.
Qed.

Lemma aproc_conv_agree :
  forall AP s1 s2,
    (forall x, aproc_fv AP x -> s1 x = s2 x) ->
  aproc_conv AP s1 = aproc_conv AP s2.
Proof.
  induction AP; intros s1 s2 H1; vauto.
  (* sending *)
  - simpl. rewrite expr_conv_agree with E s1 s2, expr_conv_agree with T s1 s2; auto.
    + intros x H2. apply H1. simpl. apply in_or_app. by right.
    + intros x H2. apply H1. simpl. apply in_or_app. by left.
  (* receiving *)
  - simpl. rewrite expr_conv_agree with E s1 s2, expr_conv_agree with T s1 s2; auto.
    + intros x H2. apply H1. simpl. apply in_or_app. by right.
    + intros x H2. apply H1. simpl. apply in_or_app. by left.
  (* assertions *)
  - simpl. rewrite cond_conv_agree with B s1 s2; auto.
  (* sequential *)
  - simpl. rewrite IHAP1 with s1 s2, IHAP2 with s1 s2; auto.
    + intros x H2. apply H1. simpl. by right.
    + intros x H2. apply H1. simpl. by left.
  (* choice *)
  - simpl. rewrite IHAP1 with s1 s2, IHAP2 with s1 s2; auto.
    + intros x H2. apply H1. simpl. by right.
    + intros x H2. apply H1. simpl. by left.
  (* parallel *)
  - simpl. rewrite IHAP1 with s1 s2, IHAP2 with s1 s2; auto.
    + intros x H2. apply H1. simpl. by right.
    + intros x H2. apply H1. simpl. by left.
  (* summation *)
  - simpl. apply proc_sum_ext. extensionality v.
    apply H. intros x H2. apply H1. simpl. exists v. done.
  (* conditionals *)
  - simpl. rewrite IHAP with (s2 := s2), cond_conv_agree with (s2 := s2); auto.
    + intros x H2. apply H1. simpl. by left.
    + intros x H2. apply H1. simpl. by right.
  (* iteration *)
  - simpl. rewrite IHAP with s1 s2; auto.
Qed.

Lemma aproc_conv_seq :
  forall AP AQ s,
  aproc_conv (APseq AP AQ) s = Pseq (aproc_conv AP s) (aproc_conv AQ s).
Proof. ins. Qed.
Lemma aproc_conv_alt :
  forall AP AQ s,
  aproc_conv (APalt AP AQ) s = Palt (aproc_conv AP s) (aproc_conv AQ s).
Proof. ins. Qed.
Lemma aproc_conv_par :
  forall AP AQ s,
  aproc_conv (APpar AP AQ) s = Ppar (aproc_conv AP s) (aproc_conv AQ s).
Proof. ins. Qed.
Lemma aproc_conv_sigma :
  forall x AP s,
  aproc_conv (APsigma x AP) s =
  Psum (fun v => aproc_conv (aproc_subst x (Econst v) AP) s).
Proof.
  ins.
Qed.

Lemma aproc_conv_subst_upd :
  forall AP x y s v,
  ~ aproc_fv AP y ->
  aproc_conv (aproc_subst x (Evar y) AP) (updatestore s y v) =
  aproc_conv (aproc_subst x (Econst v) AP) s.
Proof.
  induction AP; intros x y s v H1; simpls.
  (* sending *)
  - repeat rewrite expr_conv_subst_upd; auto.
    + intro H2. apply H1. apply in_or_app. by right.
    + intro H2. apply H1. apply in_or_app. by left.
  (* receiving *)
  - repeat rewrite expr_conv_subst_upd; auto.
    + intro H2. apply H1. apply in_or_app. by right.
    + intro H2. apply H1. apply in_or_app. by left.
  (* assertions *)
  - by rewrite cond_conv_subst_upd.
  (* sequential *)
  - rewrite IHAP1, IHAP2; auto.
  (* choice *)
  - rewrite IHAP1, IHAP2; auto.
  (* parallel *)
  - rewrite IHAP1, IHAP2; auto.
  (* summation *)
  - apply proc_sum_ext. extensionality v'.
    rewrite H; auto. intro H2. apply H1.
    exists v'. done.
  (* conditionals *)
  - rewrite IHAP, cond_conv_subst_upd; auto.
  (* iteration *)
  - rewrite IHAP; auto.
Qed.

Lemma aproc_conv_subst_upd_swap :
  forall AP E x1 x2 y v s,
  ~ aproc_fv AP y ->
  ~ x1 = x2 ->
  ~ x1 = y ->
  ~ In x2 (expr_fv E) ->
  aproc_conv (aproc_subst x1 E (aproc_subst x2 (Evar y) AP)) (updatestore s y v) =
  aproc_conv (aproc_subst x2 (Evar y) (aproc_subst x1 E AP)) (updatestore s y v).
Proof.
  induction AP; intros E' x1 x2 y v' s H1 H2 H3 H4; try (simpls; fail).
  (* sending *)
  - simpl. repeat rewrite expr_conv_subst_upd_swap; vauto.
    + intro H5. apply H1. simpl. apply in_or_app. by right.
    + intro H5. apply H1. simpl. apply in_or_app. by left.
  (* receiving *)
  - simpl. repeat rewrite expr_conv_subst_upd_swap; vauto.
    + intro H5. apply H1. simpl. apply in_or_app. by right.
    + intro H5. apply H1. simpl. apply in_or_app. by left.
  (* assertions *)
  - simpl. rewrite cond_conv_subst_upd_swap; vauto.
  (* sequential composition *)
  - simpl. rewrite IHAP1, IHAP2; vauto.
    + intro H5. apply H1. simpl. by right.
    + intro H5. apply H1. simpl. by left.
  (* choice *)
  - simpl. rewrite IHAP1, IHAP2; vauto.
    + intro H5. apply H1. simpl. by right.
    + intro H5. apply H1. simpl. by left.
  (* parallel composition *)
  - simpl. rewrite IHAP1, IHAP2; vauto.
    + intro H5. apply H1. simpl. by right.
    + intro H5. apply H1. simpl. by left.
  (* summation *)
  - simpl. apply proc_sum_ext. extensionality v.
    rewrite H; vauto. intro H5. apply H1. simpl.
    exists v. vauto.
  (* conditionals *)
  - simpl. rewrite IHAP, cond_conv_subst_upd_swap; vauto.
    + intro H5. apply H1. simpl. by left.
    + intro H5. apply H1. simpl. by right.
  (* iteration *)
  - simpl. rewrite IHAP; vauto.
Qed.

(** *** Bisimilarity *)

(** The [bisim] relation is lifted to bisimilarity of abstract processes. *)

Definition abisim (AP AQ: AbstrProc): Prop :=
  forall s: Store, bisim (aproc_conv AP s) (aproc_conv AQ s).
Definition abisim_lambda (f1 f2: Val -> AbstrProc): Prop :=
  forall v: Val, abisim (f1 v) (f2 v).

Instance abisim_refl : Reflexive abisim.
Proof. intros AP. red. auto. Qed.
Instance abisim_symm : Symmetric abisim.
Proof. intros AP AQ H. red. symmetry. by apply H. Qed.
Instance abisim_trans  : Transitive abisim.
Proof. intros AP AQ AR H1 H2 s. by transitivity (aproc_conv AQ s). Qed.
Instance abisim_equiv : Equivalence abisim.
Proof. split; intuition. Qed.
Hint Resolve abisim_refl abisim_symm.

Instance abisim_lambda_refl : Reflexive abisim_lambda.
Proof. intros f v s. auto. Qed.
Instance abisim_lambda_symm : Symmetric abisim_lambda.
Proof. intros f1 f2 H v s. symmetry. by apply H. Qed.
Instance abisim_lambda_trans : Transitive abisim_lambda.
Proof. intros f1 f2 f3 H1 H2 v. transitivity (f2 v); auto. Qed.
Instance abisim_lambda_equiv : Equivalence abisim_lambda.
Proof. split; intuition. Qed.
Hint Resolve abisim_lambda_refl abisim_lambda_symm.

Add Parametric Morphism : aproc_conv
  with signature abisim ==> eq ==> bisim as aproc_conv_mor.
Proof.
  intros AP AQ H1 s. red in H1. by apply H1.
Qed.

(** *** Congruence *)

(** Bisimilarity of abstract processes is a _congruence_ for all process-algebraic
    connectives (this is entirely derived from the congruence properties of [bisim]). *)

Add Parametric Morphism : APseq
  with signature abisim ==> abisim ==> abisim as abisim_seq.
Proof. intros ???????. by apply bisim_seq. Qed.
Add Parametric Morphism : APalt
  with signature abisim ==> abisim ==> abisim as abisim_alt.
Proof. intros ???????. by apply bisim_alt. Qed.
Add Parametric Morphism : APpar
  with signature abisim ==> abisim ==> abisim as abisim_par.
Proof. intros ???????. by apply bisim_par. Qed.
Add Parametric Morphism : APsum
  with signature abisim_lambda ==> abisim as abisim_sum.
Proof. intros ????. simpl. apply bisim_sum. red. intro. by apply H. Qed.
Add Parametric Morphism : APiter
  with signature abisim ==> abisim as abisim_iter.
Proof. intros ????. by apply bisim_iter. Qed.

(** *** Standard bisimulation equivalences *)

(** All standard bisimulation equivalences can be derived from the
    [bisim] equivalences proven earlier. The two most important equivalences
    for the remaining theory are associativity and commutativity of [APpar]
    with respect to [abisim]. *)

Theorem apar_assoc :
  forall AP AQ AR, abisim (APpar AP (APpar AQ AR)) (APpar (APpar AP AQ) AR).
Proof. intros ????. by apply par_assoc. Qed.
Theorem apar_comm :
  forall AP AQ, abisim (APpar AP AQ) (APpar AQ AP).
Proof. intros ???. by apply par_comm. Qed.
Theorem apar_epsilon_l :
  forall AP, abisim (APpar APepsilon AP) AP.
Proof. intros ??. by apply par_epsilon_l. Qed.
Theorem apar_epsilon_r :
  forall AP, abisim (APpar AP APepsilon) AP.
Proof. intros ??. by apply par_epsilon_r. Qed.

End Models.
