Require Import HahnBase.
Require Import List.
Require Import Prelude.
Require Import Nat.
Require Import Setoid.
Require Import Utf8.

Import ListNotations.

Set Implicit Arguments.

(** * Process Algebra Theory *)

Module Type Processes(dom : Domains).

Export dom.

(** ** Syntax *)

(** Process terms are closed by construction (i.e. [ProcExpr] does not contain
    variables). In turn, [Psum] allows to "quantify" over data using a lambda. *)

Inductive ProcExpr :=
  | PEconst(v: Val)
  | PEplus(e1 e2: ProcExpr).

Add Search Blacklist "ProcExpr_rect".
Add Search Blacklist "ProcExpr_ind".
Add Search Blacklist "ProcExpr_rec".

Inductive ProcCond :=
  | PBconst(b: bool)
  | PBnot(b: ProcCond)
  | PBand(b1 b2: ProcCond)
  | PBeq(e1 e2: ProcExpr).

Add Search Blacklist "ProcCond_rect".
Add Search Blacklist "ProcCond_ind".
Add Search Blacklist "ProcCond_rec".

Definition PBor (b1 b2: ProcCond): ProcCond :=
  PBnot (PBand (PBnot b1) (PBnot b2)).

Inductive Proc :=
  | Pdelta
  | Pepsilon
  | Psend(e tag: ProcExpr)
  | Precv(e tag: ProcExpr)
  | Passn(b: ProcCond)
  | Pseq(P1 P2: Proc)
  | Palt(P1 P2: Proc)
  | Ppar(P1 P2: Proc)
  | Psum(f: Val -> Proc)
  | Pcond(b: ProcCond)(P: Proc)
  | Piter(P: Proc).

Add Search Blacklist "Proc_rect".
Add Search Blacklist "Proc_ind".
Add Search Blacklist "Proc_rec".

(** Infinite iteration "P^\omega" of [P] is defined by [PInfIter P]. *)

Definition PInfIter(P: Proc): Proc := Pseq (Piter P) Pdelta.

Lemma proc_sum_ext : forall f g, f = g -> Psum f = Psum g.
Proof. intuition vauto. Qed.

(** ** Denotational semantics *)

Fixpoint pexpr_eval (e: ProcExpr): Val :=
  match e with
    | PEconst v => v
    | PEplus e1 e2 => val_plus (pexpr_eval e1) (pexpr_eval e2)
  end.

Fixpoint pcond_eval (b: ProcCond): bool :=
  match b with
    | PBconst b' => b'
    | PBnot b' => negb (pcond_eval b')
    | PBand b1 b2 => (pcond_eval b1) && (pcond_eval b2)
    | PBeq e1 e2 => if val_eq_dec (pexpr_eval e1) (pexpr_eval e2) then true else false
  end.

(** *** Successful termination *)

Inductive pterm: Proc -> Prop :=
  (* epsilon *)
  | pterm_epsilon : pterm Pepsilon
  (* sequential *)
  | pterm_seq P Q : pterm P -> pterm Q -> pterm (Pseq P Q)
  (* choice *)
  | pterm_alt_l P Q : pterm P -> pterm (Palt P Q)
  | pterm_alt_r P Q : pterm Q -> pterm (Palt P Q)
  (* parallel *)
  | pterm_par P Q : pterm P -> pterm Q -> pterm (Ppar P Q)
  (* summation *)
  | pterm_sum f v : pterm (f v) -> pterm (Psum f)
  (* conditions *)
  | pterm_cond b P : pcond_eval b -> pterm P -> pterm (Pcond b P)
  (* iteration *)
  | pterm_iter P : pterm (Piter P).

(** ** Small-step operational semantics *)

Inductive ProcLabel :=
  (* assertions *)
  | PLassn(b: bool)
  (* explicit send *)
  | PLsend(v: Val)(tag: Val)
  (* explicit receive *)
  | PLrecv(v: Val)(tag: Val)
  (* explicit communication *)
  | PLcomm(v: Val)(tag: Val).

Add Search Blacklist "ProcLabel_rect".
Add Search Blacklist "ProcLabel_ind".
Add Search Blacklist "ProcLabel_rec".

Inductive pstep : Proc -> ProcLabel -> Proc -> Prop :=
  (* sends *)
  | pstep_send e tag : pstep (Psend e tag) (PLsend (pexpr_eval e) (pexpr_eval tag)) Pepsilon
  (* receives *)
  | pstep_recv e tag : pstep (Precv e tag) (PLrecv (pexpr_eval e) (pexpr_eval tag)) Pepsilon
  (* assertions *)
  | pstep_assn b : pcond_eval b -> pstep (Passn b) (PLassn (pcond_eval b)) Pepsilon
  (* sequential *)
  | pstep_seq_l P P' Q l : pstep P l P' -> pstep (Pseq P Q) l (Pseq P' Q)
  | pstep_seq_r P Q Q' l : pterm P -> pstep Q l Q' -> pstep (Pseq P Q) l Q'
  (* choice *)
  | pstep_alt_l P P' Q l : pstep P l P' -> pstep (Palt P Q) l P'
  | pstep_alt_r P Q Q' l : pstep Q l Q' -> pstep (Palt P Q) l Q'
  (* parallel *)
  | pstep_par_l P P' Q l : pstep P l P' -> pstep (Ppar P Q) l (Ppar P' Q)
  | pstep_par_r P Q Q' l : pstep Q l Q' -> pstep (Ppar P Q) l (Ppar P Q')
  (* communication *)
  | pstep_comm_l P P' Q Q' v tag : pstep P (PLsend v tag) P' -> pstep Q (PLrecv v tag) Q' -> pstep (Ppar P Q) (PLcomm v tag) (Ppar P' Q')
  | pstep_comm_r P P' Q Q' v tag : pstep P (PLrecv v tag) P' -> pstep Q (PLsend v tag) Q' -> pstep (Ppar P Q) (PLcomm v tag) (Ppar P' Q')
  (* summation *)
  | pstep_sum f l v P : pstep (f v) l P -> pstep (Psum f) l P
  (* conditions *)
  | pstep_cond b P l P' : pcond_eval b -> pstep P l P' -> pstep (Pcond b P) l P'
  (* iteration *)
  | pstep_iter P P' l : pstep P l P' -> pstep (Piter P) l (Pseq P' (Piter P)).

Add Search Blacklist "pstep_ind".

Lemma pstep_par_frame_l :
  forall P P' Q l, pstep P l P' -> pstep (Ppar P Q) l (Ppar P' Q).
Proof.
  intros P P' Q l H1. by apply pstep_par_l.
Qed.

Lemma pstep_par_frame_r :
  forall P P' Q l, pstep P l P' -> pstep (Ppar Q P) l (Ppar Q P').
Proof.
  intros P P' Q l H1. by apply pstep_par_r.
Qed.

(** ** Faulting semantics *)

(** A process [P] _exhibits a fault_ if [P] can violate an assertion. *)

Inductive pfault : Proc -> Prop :=
  (* assertions *)
  | pfault_assn b : ~ pcond_eval b -> pfault (Passn b)
  (* sequential *)
  | pfault_seq_l P Q : pfault P -> pfault (Pseq P Q)
  | pfault_seq_r P Q : pterm P -> pfault Q -> pfault (Pseq P Q)
  (* choice *)
  | pfault_alt_l P Q : pfault P -> pfault (Palt P Q)
  | pfault_alt_r P Q : pfault Q -> pfault (Palt P Q)
  (* parallel *)
  | pfault_par_l P Q : pfault P -> pfault (Ppar P Q)
  | pfault_par_r P Q : pfault Q -> pfault (Ppar P Q)
  (* summation *)
  | pfault_sum f v : pfault (f v) -> pfault (Psum f)
  (* conditionals *)
  | pfault_cond b P : pcond_eval b -> pfault P -> pfault (Pcond b P)
  (* iteration *)
  | pfault_iter P : pfault P -> pfault (Piter P).

Add Search Blacklist "pfault_ind".

Lemma passn_nfault :
  forall b, ~ pfault (Passn b) -> pcond_eval b.
Proof.
  intros b H1. apply NNPP. intro H2. apply H1. vauto.
Qed.

(** ** Bisimulation *)

CoInductive bisim : relation Proc :=
  | bisim_proc P Q :
      (* termination is preserved *)
      (pterm P <-> pterm Q) /\
      (* all faults are preserved *)
      (pfault P <-> pfault Q) /\
      (* left-to-right simulation *)
      (forall P' l, pstep P l P' -> exists Q', pstep Q l Q' /\ bisim P' Q') /\
      (* right-to-left simulation *)
      (forall Q' l, pstep Q l Q' -> exists P', pstep P l P' /\ bisim P' Q') ->
    bisim P Q.

Definition bisim_lambda (f1 f2: Val -> Proc): Prop :=
  forall v: Val, bisim (f1 v) (f2 v).

Instance bisim_refl : Reflexive bisim.
Proof. cofix CH. intro P. constructor. intuition vauto. Qed.
Instance bisim_symm : Symmetric bisim.
Proof.
  cofix CH. intros P Q H. inv H. destruct H0 as (H1&H2&H3&H4).
  constructor. repeat split; try (intuition vauto; fail).
  - intros Q' l H5. apply H4 in H5. destruct H5 as (P'&H5&H6).
    exists P'. by intuition.
  - intros P' l H5. apply H3 in H5. destruct H5 as (Q'&H5&H6).
    exists Q'. by intuition.
Qed.
Instance bisim_trans : Transitive bisim.
Proof.
  cofix CH. intros P Q R H1 H2. constructor.
  inv H1. clear H1. destruct H as (K1 & K2 & K3 & K4).
  inv H2. clear H2. destruct H as (K5 & K6 & K7 & K8).
  repeat split; try (intuition vauto; fail).
  - intros P' l STEP. apply K3 in STEP. destruct STEP as (Q'&S1&S2).
    apply K7 in S1. destruct S1 as (R'&S1&S3). exists R'.
    intuition vauto. by transitivity Q'.
  - intros R' l STEP. apply K8 in STEP. destruct STEP as (Q'&S1&S2).
    apply K4 in S1. destruct S1 as (P'&S1&S3). exists P'.
    intuition vauto. by transitivity Q'.
Qed.
Instance bisim_equiv : Equivalence bisim.
Proof. split; intuition. Qed.

Hint Resolve bisim_refl bisim_symm.

Instance bisim_lambda_refl : Reflexive bisim_lambda.
Proof. intros f v. auto. Qed.
Instance bisim_lambda_symm : Symmetric bisim_lambda.
Proof. intros f1 f2 H v. symmetry. by apply H. Qed.
Instance bisim_lambda_trans : Transitive bisim_lambda.
Proof. intros f1 f2 f3 H1 H2 v. transitivity (f2 v); auto. Qed.
Instance bisim_lambda_equiv : Equivalence bisim_lambda.
Proof. split; intuition. Qed.

Hint Resolve bisim_lambda_refl bisim_lambda_symm.

Lemma bisim_term : forall P Q, bisim P Q -> pterm P -> pterm Q.
Proof. intros P Q H1 H2. inv H1. destruct H as (T&_). by apply T. Qed.
Add Parametric Morphism : pterm with signature bisim ==> iff as pterm_mor.
Proof. intros P Q ?. split; ins; [apply bisim_term with P|apply bisim_term with Q]; auto. Qed.

Lemma bisim_fault : forall P Q, bisim P Q -> pfault P -> pfault Q.
Proof. intros P Q H1 H2. inv H1. destruct H as (_&T&_). by apply T. Qed.
Add Parametric Morphism : pfault with signature bisim ==> iff as pfault_mor.
Proof. intros P Q ?. split; ins; [apply bisim_fault with P|apply bisim_fault with Q]; auto. Qed.

Lemma bisim_send :
  forall e1 e2 t1 t2,
  pexpr_eval e1 = pexpr_eval e2 ->
  pexpr_eval t1 = pexpr_eval t2 ->
  bisim (Psend e1 t1) (Psend e2 t2).
Proof.
  intros e1 e2 t1 t2 H1 H2. constructor. repeat split.
  - intro H3. inv H3.
  - intro H3. inv H3.
  - intro H3. inv H3.
  - intro H3. inv H3.
  - intros P' l H3. inv H3. exists Pepsilon.
    split; auto. rewrite H1, H2. constructor.
  - intros P' l H3. inv H3. exists Pepsilon.
    split; auto. rewrite <- H1, <- H2. constructor.
Qed.

Lemma bisim_recv :
  forall e1 e2 t1 t2,
  pexpr_eval e1 = pexpr_eval e2 ->
  pexpr_eval t1 = pexpr_eval t2 ->
  bisim (Precv e1 t1) (Precv e2 t2).
Proof.
  intros e1 e2 t1 t2 H1 H2. constructor. repeat split.
  - intro H3. inv H3.
  - intro H3. inv H3.
  - intro H3. inv H3.
  - intro H3. inv H3.
  - intros P' l H3. inv H3. exists Pepsilon.
    split; auto. rewrite H1, H2. constructor.
  - intros P' l H3. inv H3. exists Pepsilon.
    split; auto. rewrite <- H1, <- H2. constructor.
Qed.

Lemma bisim_assn :
  forall b1 b2, pcond_eval b1 = pcond_eval b2 -> bisim (Passn b1) (Passn b2).
Proof.
  intros b1 b2 H1. constructor. repeat split.
  (* termination *)
  - intro H2. inv H2.
  - intro H2. inv H2.
  (* faults *)
  - intro H2. inv H2. clear H2.
    constructor. by rewrite <- H1.
  - intro H2. inv H2. clear H2.
    constructor. by rewrite H1.
  (* reduction *)
  - intros P' l H2. inv H2. exists Pepsilon.
    split; auto. rewrite H1. constructor.
    by rewrite <- H1.
  - intros P' l H2. inv H2. exists Pepsilon.
    split; auto. rewrite <- H1. constructor.
    by rewrite H1.
Qed.

Lemma bisim_cond_eval :
  forall b1 b2 P1 P2,
  pcond_eval b1 = pcond_eval b2 ->
  bisim P1 P2 ->
  bisim (Pcond b1 P1) (Pcond b2 P2).
Proof.
  intros b1 b2 P1 P2 H1 H2. constructor. repeat split.
  (* termination *)
  - intro H3. inv H3. clear H3. constructor; vauto.
    by rewrite <- H2.
  - intro H3. inv H3. clear H3. constructor; vauto.
    by rewrite H2.
  (* faults *)
  - intro H3. inv H3. clear H3. constructor; vauto.
    by rewrite <- H2.
  - intro H3. inv H3. clear H3. constructor; vauto.
    by rewrite H2.
  (* reduction *)
  - intros P1' l H3. inv H3. clear H3.
    inv H2. clear H2. destruct H as (_ & _ & H & _).
    apply H in H7. clear H. destruct H7 as (P2' & H7 & H8).
    exists P2'. intuition vauto.
  - intros P2' l H3. inv H3. clear H3.
    inv H2. clear H2. destruct H as (_ & _ & _ & H).
    apply H in H7. clear H. destruct H7 as (P1' & H7 & H8).
    exists P1'. intuition vauto.
Qed.

(** *** Congruence *)

(** Bisimilarity is a _congruence_ for all process-algebraic connectives. *)

Add Parametric Morphism : Pseq
  with signature bisim ==> bisim ==> bisim as bisim_seq.
Proof.
  cofix CH. intros P1 P2 H1 Q1 Q2 H2. constructor. repeat split.
  (* termination *)
  - intro H3. inv H3. constructor; [by rewrite <- H1|by rewrite <- H2].
  - intro H3. inv H3. constructor; [by rewrite H1|by rewrite H2].
  (* faults *)
  - intro H3. inv H3; clear H3.
    + apply pfault_seq_l. by rewrite <- H1.
    + apply pfault_seq_r; [by rewrite <- H1|by rewrite <- H2].
  - intro H3. inv H3; clear H3.
    + apply pfault_seq_l. by rewrite H1.
    + apply pfault_seq_r; [by rewrite H1|by rewrite H2].
  (* reduction *)
  - intros P' l STEP. inv STEP; clear STEP.
    + rename P'0 into P1'. inv H1. destruct H as (_&_&H&_).
      apply H in H5. destruct H5 as (P2'&H5&H6).
      exists (Pseq P2' Q2). intuition. vauto.
    + rename P' into Q1'. inv H2. destruct H as (_&_&H&_).
      apply H in H6. destruct H6 as (Q2'&H6&H7).
      exists Q2'. intuition. apply pstep_seq_r; auto. by rewrite <- H1.
  - intros P' l STEP. inv STEP; clear STEP.
    + rename P'0 into P2'. inv H1. destruct H as (_&_&_&H).
      apply H in H5. destruct H5 as (P1'&H5&H6).
      exists (Pseq P1' Q1). intuition. vauto.
    + rename P' into Q2'. inv H2. destruct H as (_&_&_&H).
      apply H in H6. destruct H6 as (Q1'&H6&H7).
      exists Q1'. intuition. apply pstep_seq_r; auto. by rewrite H1.
Qed.

Add Parametric Morphism : Palt
  with signature bisim ==> bisim ==> bisim as bisim_alt.
Proof.
  intros P1 P2 H1 Q1 Q2 H2. constructor. repeat split.
  (* termination *)
  - intro H3. inv H3; clear H3.
    + apply pterm_alt_l. by rewrite <- H1.
    + apply pterm_alt_r. by rewrite <- H2.
  - intro H3. inv H3; clear H3.
    + apply pterm_alt_l. by rewrite H1.
    + apply pterm_alt_r. by rewrite H2.
  (* faults *)
  - intro H3. inv H3; clear H3.
    + apply pfault_alt_l. by rewrite <- H1.
    + apply pfault_alt_r. by rewrite <- H2.
  - intro H3. inv H3; clear H3.
    + apply pfault_alt_l. by rewrite H1.
    + apply pfault_alt_r. by rewrite H2.
  (* reduction *)
  - intros P' l H3. inv H3; clear H3.
    + rename P' into P1'. inv H1. destruct H as (_&_&H&_).
      apply H in H6. clear H. destruct H6 as (P2'&H6&H7).
      exists P2'. intuition. vauto.
    + rename P' into Q1'. inv H2. destruct H as (_&_&H&_).
      apply H in H6. clear H. destruct H6 as (Q2'&H6&H7).
      exists Q2'. intuition. vauto.
  - intros P' l H3. inv H3; clear H3.
    + rename P' into P2'. inv H1. destruct H as (_&_&_&H).
      apply H in H6. clear H. destruct H6 as (P1'&H6&H7).
      exists P1'. intuition. vauto.
    + rename P' into Q2'. inv H2. destruct H as (_&_&_&H).
      apply H in H6. clear H. destruct H6 as (Q1'&H6&H7).
      exists Q1'. intuition. vauto.
Qed.

Add Parametric Morphism : Ppar
  with signature bisim ==> bisim ==> bisim as bisim_par.
Proof.
  cofix CH. intros P1 P2 H1 Q1 Q2 H2. constructor. repeat split.
  (* termination *)
  - intro H3. inv H3. constructor; [by rewrite <- H1|by rewrite <- H2].
  - intro H3. inv H3. constructor; [by rewrite H1|by rewrite H2].
  (* faults *)
  - intro H3. inv H3; clear H3.
    + apply pfault_par_l. by rewrite <- H1.
    + apply pfault_par_r. by rewrite <- H2.
  - intro H3. inv H3; clear H3.
    + apply pfault_par_l. by rewrite H1.
    + apply pfault_par_r. by rewrite H2.
  (* reduction *)
  - intros P' l H3. inv H3; clear H3.
    (* step in left program *)
    + rename P'0 into P1'. inv H1. clear H1. destruct H as (_&_&H&_).
      apply H in H6. clear H. destruct H6 as (P2'&H6&H7).
      exists (Ppar P2' Q2). intuition vauto. by apply CH.
    (* step in right program *)
    + rename Q' into Q1'. inv H2. clear H2. destruct H as (_&_&H&_).
      apply H in H6. clear H. destruct H6 as (Q2'&H6&H7).
      exists (Ppar P2 Q2'). intuition vauto. by apply CH.
    (* communication, left-to-right *)
    + rename P'0 into P1', Q' into Q1'.
      inv H1. destruct H as (_&_&B1&_). inv H2. destruct H as (_&_&B2&_).
      apply B1 in H4. clear B1. destruct H4 as (P2'&H4&H5).
      apply B2 in H7. clear B2. destruct H7 as (Q2'&H6&H7).
      exists (Ppar P2' Q2'). intuition. vauto.
    (* communication, right-to-left *)
    + rename P'0 into P1', Q' into Q1'.
      inv H1. destruct H as (_&_&B1&_). inv H2. destruct H as (_&_&B2&_).
      apply B1 in H4. clear B1. destruct H4 as (P2'&H4&H5).
      apply B2 in H7. clear B2. destruct H7 as (Q2'&H6&H7).
      exists (Ppar P2' Q2'). intuition. vauto.
  - intros P' l H3. inv H3; clear H3.
    (* step in left program *)
    + rename P'0 into P2'. inv H1. clear H1. destruct H as (_&_&_&H).
      apply H in H6. clear H. destruct H6 as (P1'&H6&H7).
      exists (Ppar P1' Q1). intuition vauto. by apply CH.
    (* step in right program *)
    + rename Q' into Q2'. inv H2. clear H2. destruct H as (_&_&_&H).
      apply H in H6. clear H. destruct H6 as (Q1'&H6&H7).
      exists (Ppar P1 Q1'). intuition vauto. by apply CH.
    (* communication, left-to-right *)
    + rename P'0 into P2', Q' into Q2'.
      inv H1. destruct H as (_&_&_&B1). inv H2. destruct H as (_&_&_&B2).
      apply B1 in H4. clear B1. destruct H4 as (P1'&H4&H5).
      apply B2 in H7. clear B2. destruct H7 as (Q1'&H6&H7).
      exists (Ppar P1' Q1'). intuition. vauto.
    (* communication, right-to-left *)
    + rename P'0 into P2', Q' into Q2'.
      inv H1. destruct H as (_&_&_&B1). inv H2. destruct H as (_&_&_&B2).
      apply B1 in H4. clear B1. destruct H4 as (P1'&H4&H5).
      apply B2 in H7. clear B2. destruct H7 as (Q1'&H6&H7).
      exists (Ppar P1' Q1'). intuition. vauto.
Qed.

Add Parametric Morphism : Psum
  with signature bisim_lambda ==> bisim as bisim_sum.
Proof.
  intros f1 f2 H1. constructor. repeat split.
  (* termination *)
  - intro H2. inv H2. clear H2. apply pterm_sum with v. red in H1. by rewrite <- H1.
  - intro H2. inv H2. clear H2. apply pterm_sum with v. red in H1. by rewrite H1.
  (* faults *)
  - intro H2. inv H2. clear H2. apply pfault_sum with v. red in H1. by rewrite <- H1.
  - intro H2. inv H2. clear H2. apply pfault_sum with v. red in H1. by rewrite H1.
  (* reduction *)
  - intros P' l H2. inv H2. clear H2. red in H1. specialize H1 with v.
    inv H1. clear H1. destruct H as (_&_&H&_). apply H in H0. clear H.
    destruct H0 as (P&H1&H2). exists P. intuition. vauto.
  - intros P' l H2. inv H2. clear H2. red in H1. specialize H1 with v.
    inv H1. clear H1. destruct H as (_&_&_&H). apply H in H0. clear H.
    destruct H0 as (P&H1&H2). exists P. intuition. vauto.
Qed.

Add Parametric Morphism : Pcond
  with signature eq ==> bisim ==> bisim as bisim_cond.
Proof.
  intros b P Q H1. constructor. repeat split.
  (* termination *)
  - intro H2. inv H2. clear H2. constructor; vauto. by rewrite <- H1.
  - intro H2. inv H2. clear H2. constructor; vauto. by rewrite H1.
  (* faults *)
  - intro H2. inv H2. clear H2. constructor; vauto. by rewrite <- H1.
  - intro H2. inv H2. clear H2. constructor; vauto. by rewrite H1.
  (* reduction *)
  - intros P' l H2. inv H2. clear H2.
    inv H1. clear H1. destruct H as (_ & _ & H & _).
    apply H in H6. clear H. destruct H6 as (Q' & H1 & H2).
    exists Q'. intuition. constructor; vauto.
  - intros Q' l H2. inv H2. clear H2.
    inv H1. clear H1. destruct H as (_ & _ & _ & H).
    apply H in H6. clear H. destruct H6 as (P' & H1 & H2).
    exists P'. intuition. constructor; vauto.
Qed.

Lemma bisim_iter_seq :
  forall P1 P2 Q1 Q2,
  bisim P1 P2 -> bisim Q1 Q2 -> bisim (Pseq P1 (Piter Q1)) (Pseq P2 (Piter Q2)).
Proof.
  cofix CH. intros P1 P2 Q1 Q2 H1 H2. constructor. repeat split.
  (* termination *)
  - intro H3. inv H3. clear H3. constructor; vauto. by rewrite <- H1.
  - intro H3. inv H3. clear H3. constructor; vauto. by rewrite H1.
  (* faults *)
  - intro H3. inv H3; clear H3.
    + apply pfault_seq_l; vauto. by rewrite <- H1.
    + apply pfault_seq_r; vauto.
      * by rewrite <- H1.
      * inv H5. clear H5. apply pfault_iter. by rewrite <- H2.
  - intro H3. inv H3; clear H3.
    + apply pfault_seq_l; vauto. by rewrite H1.
    + apply pfault_seq_r; vauto.
      * by rewrite H1.
      * inv H5. clear H5. apply pfault_iter. by rewrite H2.
  (* reduction *)
  - intros P l H3. inv H3; clear H3.
    + rename P' into P1'. inv H1. clear H1. destruct H as (_&_&H&_).
      apply H in H6. clear H. destruct H6 as (P2'&H6&H7).
      exists (Pseq P2' (Piter Q2)). intuition vauto. apply CH; vauto.
    + inv H7. clear H7. rename P' into Q1'. inv H2. destruct H as (_&_&H&_).
      apply H in H0. clear H. destruct H0 as (Q2'&H6&H7).
      exists (Pseq Q2' (Piter Q2)). split.
      * apply pstep_seq_r; [by rewrite <- H1|]. vauto.
      * apply CH; vauto.
  - intros P l H3. inv H3; clear H3.
    + rename P' into P2'. inv H1. clear H1. destruct H as (_&_&_&H).
      apply H in H6. clear H. destruct H6 as (P1'&H6&H7).
      exists (Pseq P1' (Piter Q1)). intuition vauto. apply CH; vauto.
    + inv H7. clear H7. rename P' into Q2'. inv H2. destruct H as (_&_&_&H).
      apply H in H0. clear H. destruct H0 as (Q1'&H6&H7).
      exists (Pseq Q1' (Piter Q1)). split.
      * apply pstep_seq_r; [by rewrite H1|]. vauto.
      * apply CH; vauto.
Qed.

Add Parametric Morphism : Piter
  with signature bisim ==> bisim as bisim_iter.
Proof.
  intros P1 P2 H1. constructor. repeat split; try (intuition vauto; fail).
  (* faults *)
  - intro H. apply pfault_iter. inv H. clear H. by rewrite <- H1.
  - intro H. apply pfault_iter. inv H. clear H. by rewrite H1.
  (* reduction *)
  - intros P' l H2. inv H2. clear H2. rename P'0 into P1'.
    inv H1. destruct H as (_&_&H&_). apply H in H0. clear H.
    destruct H0 as (P2'&H2&H3). exists (Pseq P2' (Piter P2)).
    intuition; vauto. apply bisim_iter_seq; vauto.
  - intros P' l H2. inv H2. clear H2. rename P'0 into P2'.
    inv H1. destruct H as (_&_&_&H). apply H in H0. clear H.
    destruct H0 as (P1'&H2&H3). exists (Pseq P1' (Piter P1)).
    intuition; vauto. apply bisim_iter_seq; vauto.
Qed.

(** ** Axiom system *)

Theorem pseq_epsilon_l :
  forall P, bisim (Pseq P Pepsilon) P.
Proof.
  cofix CH.
  intros P. constructor. repeat split.
  (* termination *)
  - intro H. inv H.
  - intro H. constructor; auto. constructor.
  (* faults *)
  - intro H. inv H. inv H3.
  - intro H. constructor. done.
  (* reduction *)
  - intros P' l H1. inv H1; clear H1.
    + rename P'0 into P'. exists P'.
      intuition.
    + inv H5.
  - intros P' l H1. exists (Pseq P' Pepsilon).
    intuition. by constructor.
Qed.

Theorem pseq_epsilon_r :
  forall P, bisim (Pseq Pepsilon P) P.
Proof.
  cofix CH.
  intros P. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1.
  - intro H1. constructor; auto. constructor.
  (* faults *)
  - intro H1. inv H1. inv H0.
  - intro H1. apply pfault_seq_r; vauto.
  (* reduction *)
  - intros P' l H1. inv H1; clear H1.
    + inv H4.
    + exists P'. intuition.
  - intros P' l H1. exists P'.
    intuition. constructor; vauto.
Qed.

Theorem pseq_delta :
  forall P, bisim (Pseq Pdelta P) Pdelta.
Proof.
  intro P. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1.
  - intro H1. inv H1.
  (* faults *)
  - intro H1. inv H1. inv H2.
  - intro H1. inv H1.
  (* reduction *)
  - intros P' l STEP. inv STEP; clear STEP.
    + inv H3.
    + inv H1.
  - intros P' l STEP. inv STEP.
Qed.

Theorem pseq_assoc :
  forall P Q R, bisim (Pseq P (Pseq Q R)) (Pseq (Pseq P Q) R).
Proof.
  cofix CH.
  intros P Q R. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1. clear H1.
    inv H3. clear H3. vauto.
  - intro H1. inv H1. clear H1.
    inv H2. clear H2. vauto.
  (* faults *)
  - intro H1. inv H1; clear H1.
    + by repeat apply pfault_seq_l.
    + inv H3; clear H3; vauto.
  - intro H1. inv H1; clear H1.
    + inv H0; clear H0; vauto.
    + inv H2. clear H2. vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP; clear STEP.
    + rename P'0 into P'.
      exists (Pseq (Pseq P' Q) R). split; vauto.
    + inv H4; clear H4.
      * rename P'0 into Q'.
        exists (Pseq Q' R). split; vauto.
      * rename P' into R'.
        exists R'. split; vauto.
  - intros Q' l STEP. inv STEP; clear STEP.
    + inv H3; clear H3.
      * rename P'0 into P'.
        exists (Pseq P' (Pseq Q R)). split; vauto.
      * rename P' into Q'.
        exists (Pseq Q' R). split; vauto.
    + rename Q' into R'. inv H1. clear H1.
      exists R'. split; vauto.
Qed.

Theorem palt_comm :
  forall P Q, bisim (Palt P Q) (Palt Q P).
Proof.
  cofix CH.
  intros P Q. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1; clear H1; vauto.
  - intro H1. inv H1; clear H1; vauto.
  (* faults *)
  - intro H1. inv H1; clear H1; vauto.
  - intro H1. inv H1; clear H1; vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP; clear STEP.
    + exists P'. split; vauto.
    + rename P' into Q'. exists Q'. split; vauto.
  - intros Q' l STEP. inv STEP; clear STEP.
    + exists Q'. split; vauto.
    + rename Q' into P'. exists P'. split; vauto.
Qed.

Theorem palt_assoc :
  forall P Q R, bisim (Palt P (Palt Q R)) (Palt (Palt P Q) R).
Proof.
  cofix CH.
  intros P Q R. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1; clear H1; vauto.
    inv H0; clear H0; vauto.
  - intro H1. inv H1; clear H1; vauto.
    inv H0; clear H0; vauto.
  (* faults *)
  - intro H1. inv H1; clear H1; vauto.
    inv H0; clear H0; vauto.
  - intro H1. inv H1; clear H1; vauto.
    inv H0; clear H0; vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP; clear STEP.
    + exists P'. split; vauto.
    + inv H3; clear H3.
      * rename P' into Q'. exists Q'. split; vauto.
      * rename P' into R'. exists R'. split; vauto.
  - intros Q' l STEP. inv STEP; clear STEP.
    + inv H3; clear H3.
      * rename Q' into P'. exists P'. split; vauto.
      * exists Q'. split; vauto.
    + rename Q' into R'. exists R'. split; vauto.
Qed.

Theorem palt_dupl :
  forall P, bisim (Palt P P) P.
Proof.
  cofix CH.
  intros P. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1.
  - intro H1. vauto.
  (* faulting *)
  - intro H1. inv H1.
  - intro H1. vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP; clear STEP.
    + exists P'. split; vauto.
    + exists P'. split; vauto.
  - intros P' l STEP. exists P'. split; vauto.
Qed.

Theorem palt_delta :
  forall P, bisim (Palt P Pdelta) P.
Proof.
  cofix CH.
  intros P. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1. inv H0.
  - intro H1. vauto.
  (* faulting *)
  - intro H1. inv H1. inv H0.
  - intro H1. vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP; vauto. inv H3.
  - intros P' l STEP. exists P'. split; vauto.
Qed.

Theorem palt_distr :
  forall P Q R, bisim (Pseq (Palt P Q) R) (Palt (Pseq P R) (Pseq Q R)).
Proof.
  cofix CH.
  intros P Q R. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1; clear H1.
    inv H2; clear H2; vauto.
  - intro H1. inv H1; clear H1.
    + inv H0. clear H0. vauto.
    + inv H0. clear H0. vauto.
  (* faulting *)
  - intro H1. inv H1; clear H1.
    + inv H0; clear H0; vauto.
    + inv H2; clear H2; vauto.
  - intro H1. inv H1; clear H1.
    + inv H0; clear H0; vauto.
    + inv H0; clear H0; vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP; clear STEP.
    + inv H3; clear H3.
      * rename P'0 into P'. exists (Pseq P' R). split; vauto.
      * rename P'0 into Q'. exists (Pseq Q' R). split; vauto.
    + rename P' into R'. inv H1; clear H1.
      * exists R'. split; vauto.
      * exists R'. split; vauto.
  - intros Q' l STEP. inv STEP; clear STEP.
    + inv H3; clear H3.
      * exists (Pseq P' R). split; vauto.
      * rename Q' into R'. exists R'. split; vauto.
    + inv H3; clear H3.
      * rename P' into Q'.
        exists (Pseq Q' R). split; vauto.
      * rename Q' into R'. exists R'. split; vauto.
Qed.

Theorem par_comm :
  forall P Q, bisim (Ppar P Q) (Ppar Q P).
Proof.
  cofix CH. intros P Q. constructor. repeat split.
  (* termination *)
  - intro H. inv H. vauto.
  - intro H. inv H. vauto.
  (* faults *)
  - intro H. inv H; clear H.
    + by apply pfault_par_r.
    + by apply pfault_par_l.
  - intro H. inv H; clear H.
    + by apply pfault_par_r.
    + by apply pfault_par_l.
  (* reduction *)
  - intros P' l H1. inv H1; clear H1.
    + rename P'0 into P'. exists (Ppar Q P'). intuition vauto.
    + exists (Ppar Q' P). intuition vauto.
    + rename P'0 into P'. exists (Ppar Q' P'). intuition vauto.
    + rename P'0 into P'. exists (Ppar Q' P'). intuition vauto.
  - intros P' l H1. inv H1; clear H1.
    + rename P'0 into Q'. exists (Ppar P Q'). intuition vauto.
    + rename Q' into P'. exists (Ppar P' Q). intuition vauto.
    + rename Q' into P', P'0 into Q'. exists (Ppar P' Q'). intuition vauto.
    + rename Q' into P', P'0 into Q'. exists (Ppar P' Q'). intuition vauto.
Qed.

Theorem par_assoc :
  forall P Q R, bisim (Ppar P (Ppar Q R)) (Ppar (Ppar P Q) R).
Proof.
  cofix CH. intros P Q R. constructor. repeat split.
  (* termination *)
  - intro H. inv H. clear H. inv H3. clear H3. vauto.
  - intro H. inv H. clear H. inv H2. clear H2. vauto.
  (* faults *)
  - intro H. inv H; clear H.
    + by repeat apply pfault_par_l.
    + inv H1; clear H1.
      * apply pfault_par_l. by apply pfault_par_r.
      * by repeat apply pfault_par_r.
  - intro H. inv H; clear H.
    + inv H1; clear H1.
      * by repeat apply pfault_par_l.
      * apply pfault_par_r. by apply pfault_par_l.
    + by repeat apply pfault_par_r.
  (* simulation *)
  - intros S l H1. inv H1; clear H1.
    + exists (Ppar (Ppar P' Q) R). intuition vauto.
    + inv H4; clear H4.
      * rename P' into Q'. exists (Ppar (Ppar P Q') R). intuition vauto.
      * rename Q'0 into R'. exists (Ppar (Ppar P Q) R'). intuition vauto.
      * rename P' into Q', Q'0 into R'. exists (Ppar (Ppar P Q') R'). intuition vauto.
      * rename P' into Q', Q'0 into R'. exists (Ppar (Ppar P Q') R'). intuition vauto.
    + inv H5; clear H5.
      * rename P'0 into Q'. exists (Ppar (Ppar P' Q') R). intuition vauto.
      * rename Q'0 into R'. exists (Ppar (Ppar P' Q) R'). intuition vauto.
    + inv H5; clear H5.
      * rename P'0 into Q'. exists (Ppar (Ppar P' Q') R). intuition vauto.
      * rename Q'0 into R'. exists (Ppar (Ppar P' Q) R'). intuition vauto.
  - intros S l H1. inv H1; clear H1.
    + inv H4; clear H4.
      * rename P'0 into P'. exists (Ppar P' (Ppar Q R)). intuition vauto.
      * exists (Ppar P (Ppar Q' R)). intuition vauto.
      * rename P'0 into P'. exists (Ppar P' (Ppar Q' R)). intuition vauto.
      * rename P'0 into P'. exists (Ppar P' (Ppar Q' R)). intuition vauto.
    + rename Q' into R'. exists (Ppar P (Ppar Q R')). intuition vauto.
    + inv H2; clear H2.
      * rename P'0 into P', Q' into R'. exists (Ppar P' (Ppar Q R')). intuition vauto.
      * rename Q' into R', Q'0 into Q'. exists (Ppar P (Ppar Q' R')). intuition vauto.
    + inv H2; clear H2.
      * rename Q' into R', P'0 into P'. exists (Ppar P' (Ppar Q R')). intuition vauto.
      * rename Q' into R', Q'0 into Q'. exists (Ppar P (Ppar Q' R')). intuition vauto.
Qed.

Theorem par_epsilon_l :
  forall P, bisim (Ppar Pepsilon P) P.
Proof.
  cofix CP.
  intros P. constructor. repeat split.
  (* termination *)
  - intro H. inv H.
  - intro H. apply pterm_par; auto.
    apply pterm_epsilon.
  (* faults *)
  - intro H. inv H. inv H1.
  - intro H. by apply pfault_par_r.
  (* reduction *)
  - intros P' l H. inv H; clear H.
    + by inv H4.
    + rename Q' into P'. exists P'. split; vauto.
    + inv H2.
    + inv H2.
  - intros P' l H. exists (Ppar Pepsilon P'). split; vauto.
Qed.

Theorem par_epsilon_r :
  forall P, bisim (Ppar P Pepsilon) P.
Proof.
  intro P. rewrite par_comm. by apply par_epsilon_l.
Qed.

Theorem ppar_delta :
  forall P, bisim (Ppar P Pdelta) (Pseq P Pdelta).
Proof.
  cofix CH.
  intros P. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1. inv H3.
  - intro H1. inv H1. inv H3.
  (* faulting *)
  - intro H1. inv H1; vauto. inv H0.
  - intro H1. inv H1; vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP; clear STEP.
    + rename P'0 into P'.
      exists (Pseq P' Pdelta). intuition vauto.
    + inv H3.
    + inv H4.
    + inv H4.
  - intros Q' l STEP. inv STEP; clear STEP.
    + exists (Ppar P' Pdelta). intuition vauto.
    + inv H4.
Qed.

Theorem pcond_true :
  forall P b, pcond_eval b -> bisim (Pcond b P) P.
Proof.
  intro P. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1.
  - intro H1. constructor; auto.
  (* faults *)
  - intro H1. inv H1.
  - intro H1. vauto.
  (* reduction *)
  - intros P' l H1. inv H1. clear H1.
    exists P'. vauto.
  - intros P' l H1. exists P'. intuition.
    constructor; vauto.
Qed.

Theorem pcond_false :
  forall P b, ~ pcond_eval b -> bisim (Pcond b P) Pdelta.
Proof.
  intros P. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1.
  - intro H1. inv H1.
  (* faults *)
  - intro H1. inv H1.
  - intro H1. inv H1.
  (* reduction *)
  - intros P' l H1. inv H1.
  - intros P' l H1. inv H1.
Qed.

Theorem pcond_and :
  forall b1 b2 P, bisim (Pcond b1 (Pcond b2 P)) (Pcond (PBand b1 b2) P).
Proof.
  intros b1 b2 P. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1. clear H1. inv H3. clear H3.
    constructor; vauto. simpl.
    apply andb_true_intro. vauto.
  - intros H1. inv H1. clear H1. simpl in H2.
    apply andb_prop in H2. destruct H2 as (H1 & H2). vauto.
  (* faults *)
  - intros H1. inv H1. clear H1. inv H3. clear H3.
    constructor; vauto. simpl.
    apply andb_true_intro. vauto.
  - intros H1. inv H1. clear H1. simpl in H2.
    apply andb_prop in H2. destruct H2 as (H1 & H2). vauto.
  (* reduction *)
  - intros P' l H1. inv H1. clear H1. inv H5. clear H5.
    exists P'. intuition. constructor; vauto.
    simpl. apply andb_true_intro. intuition.
  - intros P' l H1. inv H1. clear H1. simpl in H2.
    apply andb_prop in H2. destruct H2 as (H1 & H2).
    exists P'. intuition. constructor; vauto.
Qed.

Theorem psum_alt :
  forall f v, bisim (Psum f) (Palt (f v) (Psum f)).
Proof.
  intros f v. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1. clear H1. rename v0 into v'.
    apply pterm_alt_r. by apply pterm_sum with v'.
  - intro H1. inv H1. clear H1. vauto.
  (* faulting *)
  - intro H1. inv H1. clear H1. rename v0 into v'.
    apply pfault_alt_r. vauto.
  - intro H1. inv H1. clear H1. vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP. clear STEP.
    rename v0 into v'. exists P'.
    intuition vauto.
  - intros P' l STEP. inv STEP; clear STEP.
    + exists P'. intuition vauto.
    + inv H3. clear H3. rename v0 into v'.
      exists P'. intuition vauto.
Qed.

Theorem psum_alt_distr :
  forall f g,
  bisim (Psum (fun v => Palt (f v) (g v))) (Palt (Psum f) (Psum g)).
Proof.
  intros f g. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1. clear H1. inv H0; clear H0; vauto.
  - intro H1. inv H1; clear H1.
    + inv H0. clear H0. vauto.
    + inv H0. clear H0. vauto.
  (* faulting *)
  - intros H1. inv H1. clear H1. inv H0; clear H0; vauto.
  - intros H1. inv H1; clear H1.
    + inv H0. clear H0. vauto.
    + inv H0. clear H0. vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP. clear STEP.
    inv H0; clear H0.
    + exists P'. intuition vauto.
    + exists P'. intuition vauto.
  - intros P' l STEP. inv STEP; clear STEP.
    + inv H3. clear H3. exists P'. intuition vauto.
    + inv H3. clear H3. exists P'. intuition vauto.
Qed.

Theorem psum_seq :
  forall f P, bisim (Pseq (Psum f) P) (Psum (fun v => Pseq (f v) P)).
Proof.
  intros f P. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1. clear H1. inv H2. clear H2. vauto.
  - intros H1. inv H1. clear H1. inv H0. clear H0. vauto.
  (* faulting *)
  - intros H1. inv H1; clear H1.
    + inv H0. clear H0. vauto.
    + inv H2. clear H2. vauto.
  - intros H1. inv H1. clear H1.
    inv H0; clear H0; vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP; clear STEP.
    + rename P'0 into P'. inv H3. clear H3.
      exists (Pseq P' P). intuition vauto.
    + inv H1. clear H1. exists P'. intuition vauto.
  - intros P' l STEP. inv STEP. clear STEP.
    inv H0; clear H0.
    + rename P'0 into P'. exists (Pseq P' P).
      intuition vauto.
    + exists P'. intuition vauto.
Qed.

Theorem psum_indep :
  forall P, bisim (Psum (fun v => P)) P.
Proof.
  intros P. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1.
  - intros H1. by apply pterm_sum with val_unit.
  (* reduction *)
  - intros H1. inv H1.
  - intros H1. by apply pfault_sum with val_unit.
  (* reduction *)
  - intros P' l STEP. inv STEP. clear STEP.
    exists P'. intuition.
  - intros P' l STEP. exists P'. intuition vauto.
    by apply pstep_sum with val_unit.
Qed.

Theorem bisim_sum_cond :
  forall b (f: Val -> Proc),
  bisim (Psum (fun v => Pcond b (f v))) (Pcond b (Psum f)).
Proof.
  intros b f. constructor. repeat split; vauto.
  (* termination *)
  - intro H1. inv H1. clear H1. inv H0. clear H0.
    constructor; vauto.
  - intro H1. inv H1. clear H1. inv H3. clear H3.
    apply pterm_sum with v. constructor; vauto.
  (* faults *)
  - intro H1. inv H1. clear H1. inv H0. clear H0.
    constructor; vauto.
  - intro H1. inv H1. clear H1. inv H3. clear H3.
    apply pfault_sum with v. constructor; vauto.
  (* reduction *)
  - intros P' l H1. inv H1. clear H1. inv H0. clear H0.
    exists P'. intuition. constructor; vauto.
  - intros P' l H1. inv H1. clear H1. inv H5. clear H5.
    exists P'. intuition. apply pstep_sum with v. vauto.
Qed.

Theorem piter_unfold :
  forall P, bisim (Palt (Pseq P (Piter P)) Pepsilon) (Piter P).
Proof.
  intros P. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1; clear H1; vauto.
  - intros _. vauto.
  (* faulting *)
  - intros H1. inv H1; clear H1.
    + inv H0. clear H0. vauto.
    + inv H0.
  - intros H1. inv H1. clear H1. vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP; clear STEP.
    + inv H3; clear H3; vauto. rename P'0 into P'.
      exists (Pseq P' (Piter P)). intuition vauto.
    + inv H3.
  - intros P' l STEP. inv STEP. clear STEP.
    rename P'0 into P'. exists (Pseq P' (Piter P)).
    intuition vauto.
Qed.

Theorem piter_epsilon :
  bisim (Piter Pepsilon) Pepsilon.
Proof.
  constructor. repeat split; try (intuition vauto; fail).
  (* faulting *)
  - intro H1. inv H1.
  (* reduction *)
  - intros P' l STEP. inv STEP. clear STEP. inv H0.
  - intros Q' l STEP. inv STEP.
Qed.

Theorem piter_delta :
  bisim (Piter Pdelta) Pepsilon.
Proof.
  constructor. repeat split; try (intuition vauto; fail).
  (* faulting *)
  - intro H1. inv H1. inv H0.
  - intro H1. inv H1.
  (* reduction *)
  - intros P' l STEP. inv STEP. clear STEP. inv H0.
  - intros Q' l STEP. inv STEP.
Qed.

Lemma piter_alt_helper :
  forall P Q R,
  bisim (Pseq P (Piter (Palt Q R))) (Pseq (Pseq P (Piter Q)) (Piter (Pseq R (Piter Q)))).
Proof.
  cofix CH.
  intros P Q R. constructor.
  repeat split; try (intuition vauto; fail).
  (* termination *)
  - intros H1. inv H1. clear H1 H3.
    constructor; vauto.
  - intros H1. inv H1. clear H1 H3. inv H2.
    clear H2 H3. vauto.
  (* faulting *)
  - intros H1. inv H1; clear H1; vauto.
    inv H3. clear H3. inv H0; clear H0.
    + constructor. vauto.
    + apply pfault_seq_r; vauto.
  - intros H1. inv H1; clear H1.
    + inv H0; clear H0; vauto.
      inv H3. clear H3.
      apply pfault_seq_r; vauto.
    + inv H2. clear H2 H4.
      inv H3. clear H3. inv H0; clear H0.
      * apply pfault_seq_r; vauto.
      * apply pfault_seq_r; vauto.
        inv H4. clear H4. vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP; clear STEP.
    + rename P'0 into P'.
      exists (Pseq (Pseq P' (Piter Q)) (Piter (Pseq R (Piter Q)))).
      intuition vauto.
    + inv H4. clear H4. inv H0; clear H0.
      * rename P'0 into Q'.
        exists (Pseq (Pseq Q' (Piter Q)) (Piter (Pseq R (Piter Q)))).
        intuition vauto. apply pstep_seq_l.
        apply pstep_seq_r; vauto.
      * rename P'0 into R'.
        exists (Pseq (Pseq R' (Piter Q)) (Piter (Pseq R (Piter Q)))).
        intuition vauto. apply pstep_seq_r; vauto.
  - intros P' l STEP. inv STEP; clear STEP.
    + inv H3; clear H3.
      * exists (Pseq P' (Piter (Palt Q R))).
        intuition vauto.
      * inv H5. clear H5. rename P' into Q'.
        exists (Pseq Q' (Piter (Palt Q R))).
        intuition vauto.
        apply pstep_seq_r; vauto.
    + inv H1. clear H1 H3. inv H4; clear H4.
      inv H0; clear H0.
      * rename P' into R'.
        exists (Pseq R' (Piter (Palt Q R))).
        intuition vauto. apply pstep_seq_r; vauto.
      * inv H6. clear H6. rename P' into Q'.
        exists (Pseq Q' (Piter (Palt Q R))).
        intuition vauto. apply pstep_seq_r; vauto.
Qed.

Theorem piter_alt :
  forall P Q,
  bisim (Piter (Palt P Q)) (Pseq (Piter P) (Piter (Pseq Q (Piter P)))).
Proof.
  intros P Q. constructor. repeat split.
  (* termination *)
  - intros _. vauto.
  - intros _. vauto.
  (* faulting *)
  - intros H1. inv H1. clear H1. inv H0; clear H0; vauto.
    apply pfault_seq_r; vauto.
  - intros H1. inv H1; clear H1.
    + inv H0. clear H0. constructor. vauto.
    + clear H2. inv H3. clear H3. inv H0; clear H0; vauto.
      inv H3. clear H3. constructor. vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP. clear STEP.
    inv H0; clear H0.
    + rename P'0 into P'.
      exists (Pseq (Pseq P' (Piter P)) (Piter (Pseq Q (Piter P)))).
      intuition vauto. by apply piter_alt_helper.
    + rename P'0 into Q'.
      exists (Pseq (Pseq Q' (Piter P)) (Piter (Pseq Q (Piter P)))).
      intuition vauto.
      * apply pstep_seq_r; vauto.
      * by apply piter_alt_helper.
  - intros P' l STEP. inv STEP; clear STEP.
    + inv H3. clear H3. exists (Pseq P' (Piter (Palt P Q))).
      intuition vauto. by apply piter_alt_helper.
    + clear H1. inv H4. clear H4. inv H0; clear H0.
      * rename P' into Q'. exists (Pseq Q' (Piter (Palt P Q))).
        intuition vauto. by apply piter_alt_helper.
      * inv H5. clear H5. exists (Pseq P' (Piter (Palt P Q))).
        intuition vauto. by apply piter_alt_helper.
Qed.

Lemma piter_seq_dupl_helper :
  forall P Q, bisim (Pseq (Pseq P (Piter Q)) (Piter Q)) (Pseq P (Piter Q)).
Proof.
  cofix CH.
  intros P Q. constructor. repeat split.
  (* termination *)
  - intros H1. inv H1.
  - intros H1. inv H1. clear H1 H3.
    apply pterm_seq; vauto.
  (* faulting *)
  - intros H1. inv H1. clear H1. inv H2. clear H2.
    inv H3. clear H3 H4. vauto.
  - intros H1. inv H1; clear H1; vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP; clear STEP.
    + inv H3; clear H3.
      * exists (Pseq P' (Piter Q)). intuition vauto.
      * inv H5. clear H5. rename P' into Q'.
        exists (Pseq Q' (Piter Q)).
        intuition vauto.
    + inv H1. clear H1 H3. inv H4. clear H4.
      rename P'0 into Q'. exists (Pseq Q' (Piter Q)).
      intuition vauto.
  - intros P' l STEP. inv STEP; clear STEP.
    + rename P'0 into P'.
      exists (Pseq (Pseq P' (Piter Q)) (Piter Q)).
      intuition vauto.
    + inv H4. clear H4. rename P'0 into Q'.
      exists (Pseq (Pseq Q' (Piter Q)) (Piter Q)).
      intuition vauto. apply pstep_seq_l.
      apply pstep_seq_r; vauto.
Qed.

Theorem piter_seq_dupl :
  forall P, bisim (Pseq (Piter P) (Piter P)) (Piter P).
Proof.
  intros P. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1.
  - intros _. vauto.
  (* faulting *)
  - intros H1. inv H1.
  - intros H1. inv H1. clear H1. vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP; clear STEP.
    + inv H3. clear H3. exists (Pseq P' (Piter P)).
      intuition vauto. by apply piter_seq_dupl_helper.
    + clear H1. inv H4. clear H4. rename P'0 into P'.
      exists (Pseq P' (Piter P)). intuition vauto.
  - intros P' l STEP. inv STEP. clear STEP.
    rename P'0 into P'. exists (Pseq (Pseq P' (Piter P)) (Piter P)).
    intuition vauto. by apply piter_seq_dupl_helper.
Qed.

Lemma piter_idemp_helper :
  forall P Q, bisim (Pseq (Pseq P (Piter Q)) (Piter (Piter Q))) (Pseq P (Piter Q)).
Proof.
  cofix CH.
  intros P Q. constructor.
  repeat split; try (intuition vauto; fail).
  (* termination *)
  - intro H1. inv H1.
  (* faulting *)
  - intros H1. inv H1; clear H1; vauto.
    inv H3. clear H3. inv H0. clear H0.
    inv H2. clear H2 H4. vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP; clear STEP.
    + inv H3; clear H3.
      * exists (Pseq P' (Piter Q)). intuition vauto.
      * inv H5. clear H5. rename P' into Q'.
        exists (Pseq Q' (Piter Q)). intuition vauto.
    + inv H1. clear H1 H3. inv H4. clear H4.
      inv H0. clear H0. rename P' into Q'.
      exists (Pseq Q' (Piter Q)). intuition vauto.
  - intros P' l STEP. inv STEP; clear STEP.
    + rename P'0 into P'.
      exists (Pseq (Pseq P' (Piter Q)) (Piter (Piter Q))).
      intuition vauto.
    + inv H4. clear H4. rename P'0 into Q'.
      exists (Pseq (Pseq Q' (Piter Q)) (Piter (Piter Q))).
      intuition vauto. apply pstep_seq_l.
      apply pstep_seq_r; vauto.
Qed.

Theorem piter_idemp :
  forall P, bisim (Piter (Piter P)) (Piter P).
Proof.
  intros P. constructor. repeat split.
  (* termination *)
  - intros _. vauto.
  - intros _. vauto.
  (* faulting *)
  - intros H1. inv H1.
  - intros H1. inv H1. clear H1. vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP.
    clear STEP. inv H0. clear H0.
    exists (Pseq P' (Piter P)). intuition vauto.
    by apply piter_idemp_helper.
  - intros P' l STEP. inv STEP. clear STEP.
    rename P'0 into P'.
    exists (Pseq (Pseq P' (Piter P)) (Piter (Piter P))).
    intuition vauto. by apply piter_idemp_helper.
Qed.

Theorem pomega_unfold :
  forall P, bisim (PInfIter P) (Pseq P (PInfIter P)).
Proof.
  intros P. unfold PInfIter. constructor. repeat split.
  (* termination *)
  - intro H1. inv H1. clear H1. inv H3.
  - intro H1. inv H1.
  (* faulting *)
  - intros H1. inv H1; clear H1.
    + inv H0. clear H0. vauto.
    + inv H3.
  - intros H1. inv H1. clear H1. vauto.
  (* reduction *)
  - intros P' l STEP. inv STEP; clear STEP.
    + inv H3. clear H3. exists (Pseq P' (Pseq (Piter P) Pdelta)).
      intuition vauto. by rewrite pseq_assoc.
    + inv H4.
  - intros P' l STEP. inv STEP; clear STEP.
    + rename P'0 into P'. exists (Pseq (Pseq P' (Piter P)) Pdelta).
      intuition vauto. by rewrite pseq_assoc.
    + inv H4; clear H4.
      * inv H5. clear H5. exists (Pseq (Pseq P' (Piter P)) Pdelta).
        intuition vauto.
      * inv H6.
Qed.

(** ** Process safety *)

(** A process [P] is _safe_ if [P] does not exhibit a fault wrt. [pfault]. *)

CoInductive psafe : Proc -> Prop :=
  | proc_safe P :
      (* no faults *)
      (~ pfault P) /\
      (* reductions *)
      (forall l P', pstep P l P' -> psafe P') ->
    psafe P.

Lemma psafe_bisim :
  forall P Q, bisim P Q -> psafe P -> psafe Q.
Proof.
  cofix CH. intros P Q H1 H2. inv H2. clear H2.
  destruct H as (H2 & H3). constructor. split.
  (* faults *)
  - intro H4. apply H2. by rewrite H1.
  (* reductions *)
  - intros l P' H4. rename P' into Q'.
    inv H1. clear H1. destruct H as (_&_&_&H1).
    apply H1 in H4. clear H1. destruct H4 as (P'&H1&H4).
    apply CH with P'; auto. by apply H3 with l.
Qed.

Add Parametric Morphism : psafe
  with signature bisim ==> iff as psafe_bisim_mor.
Proof.
  intros P Q H. split; intros.
  - apply psafe_bisim with P; auto.
  - apply psafe_bisim with Q; auto.
Qed.

Lemma psafe_seq :
  forall P1 P2, psafe P1 -> psafe P2 -> psafe (Pseq P1 P2).
Proof.
  cofix CH. intros P1 P2 H1 H2.
  constructor. intuition.
  - inv H.
    + inv H1. clear H1. destruct H0 as (H1 & _).
      by apply H1.
    + inv H2. clear H2. destruct H0 as (H2 & _).
      by apply H2.
  - inv H.
    + rename P'0 into P1'. inv H1. clear H1.
      destruct H0 as (_ & H1). apply H1 in H6.
      by apply CH.
    + rename P' into P2'. inv H2. clear H2.
      destruct H0 as (_ & H2). by apply H2 in H7.
Qed.

Lemma psafe_seq_left :
  forall P1 P2, psafe (Pseq P1 P2) -> psafe P1.
Proof.
  cofix CH.
  intros P1 P2 H1. constructor. split.
  - intro H2. inv H1. clear H1.
    destruct H as (H&_). apply H. vauto.
  - intros l P1' H2. inv H1. clear H1.
    destruct H as (_&H).
    assert (H1: pstep (Pseq P1 P2) l (Pseq P1' P2)) by vauto.
    apply H in H1. by apply CH in H1.
Qed.

Lemma psafe_seq_right :
  forall P1 P2, pterm P1 -> psafe (Pseq P1 P2) -> psafe P2.
Proof.
  cofix CH.
  intros P1 P2 H1 H2. constructor. split.
  - intro H3. inv H2. clear H2.
    destruct H as (H&_). apply H. apply pfault_seq_r; auto.
  - intros l P2' H3. inv H2. clear H2.
    destruct H as (_&H).
    assert (H2: pstep (Pseq P1 P2) l P2') by vauto.
    by apply H in H2.
Qed.

Lemma psafe_alt :
  forall P1 P2, psafe P1 -> psafe P2 -> psafe (Palt P1 P2).
Proof.
  cofix CH. intros P1 P2 H1 H2.
  constructor. intuition.
  - inv H.
    + inv H1. clear H1. destruct H0 as (H1 & _).
      by apply H1.
    + inv H2. clear H2. destruct H0 as (H2 & _).
      by apply H2.
  - inv H.
    + rename P' into P1'. inv H1. clear H1.
      destruct H0 as (_ & H1). by apply H1 in H6.
    + rename P' into P2'. inv H2. clear H2.
      destruct H0 as (_ & H2). by apply H2 in H6.
Qed.

Lemma psafe_alt_rev :
  forall P1 P2, psafe (Palt P1 P2) -> psafe P1 /\ psafe P2.
Proof.
  intros P1 P2 H1. split.
  - constructor. split.
    + intro H2. inv H1. clear H1.
      destruct H as (H & _). apply H.
      by apply pfault_alt_l.
    + intros l P1' H2. inv H1. clear H1.
      destruct H as (_ & H).
      assert (H1: pstep (Palt P1 P2) l P1') by vauto.
      by apply H in H1.
  - constructor. split.
    + intro H2. inv H1. clear H1.
      destruct H as (H & _). apply H.
      by apply pfault_alt_r.
    + intros l P2' H2. inv H1. clear H1.
      destruct H as (_ & H).
      assert (H1: pstep (Palt P1 P2) l P2') by vauto.
      by apply H in H1.
Qed.

Lemma psafe_par :
  forall P1 P2, psafe P1 -> psafe P2 -> psafe (Ppar P1 P2).
Proof.
  cofix CH. intros P1 P2 H1 H2.
  constructor. intuition.
  - inv H.
    + inv H1. clear H1. destruct H0 as (H1 & _).
      by apply H1.
    + inv H2. clear H2. destruct H0 as (H2 & _).
      by apply H2.
  - inv H.
    + rename P'0 into P1'. inv H1. clear H1.
      destruct H0 as (_ & H1). apply H1 in H6.
      by apply CH.
    + rename Q' into P2'. inv H2. clear H2.
      destruct H0 as (_ & H2). apply H2 in H6.
      by apply CH.
    + rename P'0 into P1', Q' into P2'.
      inv H1. clear H1. destruct H0 as (_ & H1).
      apply H1 in H4. clear H1.
      inv H2. clear H2. destruct H0 as (_ & H2).
      apply H2 in H7. clear H2.
      by apply CH.
    + rename P'0 into P1', Q' into P2'.
      inv H1. clear H1. destruct H0 as (_ & H1).
      apply H1 in H4. clear H1.
      inv H2. clear H2. destruct H0 as (_ & H2).
      apply H2 in H7. clear H2.
      by apply CH.
Qed.

Lemma psafe_par_left :
  forall P1 P2, psafe (Ppar P1 P2) -> psafe P1.
Proof.
  cofix CH.
  intros P1 P2 H1. constructor. split.
  - intro H2. inv H1. clear H1.
    destruct H as (H & _). apply H.
    by apply pfault_par_l.
  - intros l P1' H2. inv H1. clear H1.
    destruct H as (_ & H).
    assert (H1: pstep (Ppar P1 P2) l (Ppar P1' P2)) by vauto.
    apply H in H1. by apply CH in H1.
Qed.

Lemma psafe_par_rev :
  forall P1 P2, psafe (Ppar P1 P2) -> psafe P1 /\ psafe P2.
Proof.
  intros P1 P2 H1. split.
  - by apply psafe_par_left in H1.
  - rewrite par_comm in H1.
    by apply psafe_par_left in H1.
Qed.

Lemma psafe_sum :
  forall f,
    (forall v, psafe (f v)) ->
  psafe (Psum f).
Proof.
  intros f H. constructor. intuition.
  - inv H0. specialize H with v.
    inv H. destruct H1 as (H1 & _). done.
  - inv H0. clear H0. specialize H with v.
    inv H. destruct H0 as (_ & H1).
    by apply H1 in H2.
Qed.

Lemma psafe_iter_seq :
  forall P Q, psafe P -> psafe Q -> psafe (Pseq P (Piter Q)).
Proof.
  cofix CH. intros P Q H1 H2. constructor. split.
  - intro H3. inv H3; clear H3.
    + inv H1. clear H1. destruct H as (H&_).
      by apply H.
    + inv H2. clear H2. destruct H as (H&_).
      inv H5.
  - intros l P' STEP. inv STEP; clear STEP.
    + rename P'0 into P'. apply CH; auto.
      inv H1. clear H1. destruct H as (_&H).
      by apply H in H5.
    + inv H6. clear H6.
      rename P'0 into Q'. apply CH; auto.
      inv H2. clear H2. destruct H as (_&H).
      by apply H in H0.
Qed.

Lemma psafe_iter :
  forall P, psafe P -> psafe (Piter P).
Proof.
  intros P H1. constructor. split.
  - intro H2. inv H2. clear H2. inv H1.
    destruct H as (H & _). by apply H.
  - intros l P' H2. inv H2. clear H2.
    rename P'0 into P'. inv H1.
    destruct H as (_ & H). apply H in H0.
    by apply psafe_iter_seq.
Qed.

End Processes.
