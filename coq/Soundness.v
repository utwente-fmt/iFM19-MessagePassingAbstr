Require Import Assertions.
Require Import HahnBase.
Require Import Heaps.
Require Import List.
Require Import Models.
Require Import Permissions.
Require Import Permutation.
Require Import Prelude.
Require Import Processes.
Require Import Programs.
Require Import QArith.
Require Import Qcanon.
Require Import Utf8.

Import ListNotations.

Set Implicit Arguments.

(** * Soundness *)

Module Type Soundness
  (doms: Domains)
  (procs: Processes doms)
  (heaps: Heaps doms)
  (progs: Programs doms procs heaps)
  (models: Models doms procs heaps progs)
  (assns: Assertions doms procs heaps progs models).

Export doms procs heaps progs models assns.

(** ** Instrumented semantics *)

(** The instrumented semantics [istep] defines the _lock-step execution_
    of [step] and [pstep]. The instrumented semantics is defined 
    up to bisimulation equivalence of permission processes. This is not
    strictly necessary (one may do without all [pbisim] conditions and handle
    bisimulation inside [safe]), but gives some very nice
    properties (e.g. [istep_bisim_l] and [istep_bisim_r]). *)

Inductive istep : Cmd -> Proc -> Heap -> Store -> Label -> Cmd -> Proc -> Heap -> Store -> Prop :=
  (* internal computation *)
  | istep_comp C P Q h s C' h' s' :
    step C h s Lcomp C' h' s' ->
    bisim P Q ->
    istep C P h s Lcomp C' Q h' s'
  (* explicit send *)
  | istep_send C P Q h s C' P' Q' h' s' v tag :
    step C h s (Lsend v tag) C' h' s' ->
    bisim P P' ->
    pstep P' (PLsend v tag) Q' ->
    bisim Q' Q ->
    istep C P h s (Lsend v tag) C' Q h' s'
  (* explicit receive *)
  | istep_recv C P Q h s C' P' Q' h' s' v tag :
    step C h s (Lrecv v tag) C' h' s' ->
    bisim P P' ->
    pstep P' (PLrecv v tag) Q' ->
    bisim Q' Q ->
    istep C P h s (Lrecv v tag) C' Q h' s'
  (* explicit communication *)
  | istep_comm C P Q h s C' P' Q' h' s' v tag :
    step C h s (Lcomm v tag) C' h' s' ->
    bisim P P' ->
    pstep P' (PLcomm v tag) Q' ->
    bisim Q' Q ->
    istep C P h s (Lcomm v tag) C' Q h' s'
  (* explicit querying *)
  | istep_query C P Q h s C' P' Q' h' s' b :
    step C h s (Lquery b) C' h' s' ->
    bisim P P' ->
    pstep P' (PLassn b) Q' ->
    bisim Q' Q ->
    istep C P h s (Lquery b) C' Q h' s'.

Lemma istep_comp_proc_pres :
  forall C P h s C' P' h' s',
  istep C P h s Lcomp C' P' h' s' -> bisim P P'.
Proof.
  induction C; intros P h s C' P' h' s' H1; inv H1.
Qed.

Lemma istep_seq_l :
  forall C1 C2 P h s l C1' P' h' s',
  istep C1 P h s l C1' P' h' s' <->
  istep (Cseq C1 C2) P h s l (Cseq C1' C2) P' h' s'.
Proof.
  intros C1 C2 P h s l C1' P' h' s'.
  split; intro STEP.
  (* left to right *)
  - inv STEP; clear STEP.
    + apply istep_comp; vauto.
    + rename P'0 into Q.
      apply istep_send with Q Q'; vauto.
    + rename P'0 into Q.
      apply istep_recv with Q Q'; vauto.
    + rename P'0 into Q.
      apply istep_comm with Q Q'; vauto.
    + rename P'0 into Q.
      apply istep_query with Q Q'; vauto.
  (* right to left *)
  - inv STEP; clear STEP.
    + inv H; vauto. by apply cmd_neg_seq in H5.
    + inv H; vauto.
    + inv H; vauto.
    + inv H; vauto.
    + inv H; vauto.
Qed.

Lemma istep_seq_r :
  forall C P h s l h' s',
  step (Cseq Cskip C) h s l C h' s' <->
  istep (Cseq Cskip C) P h s l C P h' s'.
Proof.
  intros C P h s l h' s'. split; intro H1.
  (* left to right *)
  - induction l; vauto.
    + inv H1. inv H8.
    + inv H1. inv H8.
    + inv H1. inv H8.
    + inv H1. inv H8.
  (* right to left *)
  - induction l; vauto.
    + inv H1.
    + inv H1.
    + inv H1.
    + inv H1.
    + inv H1.
Qed.

Lemma istep_par_l :
  forall C1 C2 P h s l C1' P' h' s',
  istep C1 P h s l C1' P' h' s' <->
  istep (Cpar C1 C2) P h s l (Cpar C1' C2) P' h' s'.
Proof.
  intros C1 C2 P h s l C1' P' h' s'.
  split; intro H; inv H; clear H.
  - constructor; vauto.
  - apply istep_send with P'0 Q'; vauto.
  - apply istep_recv with P'0 Q'; vauto.
  - apply istep_comm with P'0 Q'; vauto.
  - apply istep_query with P'0 Q'; vauto.
  - inv H0; clear H0.
    + constructor; vauto.
    + apply prog_sos_neg_C in H10. vauto.
  - apply istep_send with P'0 Q'; vauto.
    inv H0; clear H0. by apply prog_sos_neg_C in H12.
  - apply istep_recv with P'0 Q'; vauto.
    inv H0; clear H0. by apply prog_sos_neg_C in H12.
  - apply istep_comm with P'0 Q'; vauto.
    inv H0; clear H0.
    + by apply prog_sos_neg_C in H12.
    + by apply prog_sos_neg_C in H14.
    + by apply prog_sos_neg_C in H14.
  - apply istep_query with P'0 Q'; vauto.
    inv H0; clear H0. by apply prog_sos_neg_C in H12.
Qed.

Lemma istep_par_r :
  forall C1 C2 P h s l C2' P' h' s',
  istep C2 P h s l C2' P' h' s' <->
  istep (Cpar C1 C2) P h s l (Cpar C1 C2') P' h' s'.
Proof.
  intros C1 C2 P h s l C2' P' h' s'.
  split; intro H; inv H; clear H.
  - constructor; vauto.
  - apply istep_send with P'0 Q'; vauto.
  - apply istep_recv with P'0 Q'; vauto.
  - apply istep_comm with P'0 Q'; vauto.
  - apply istep_query with P'0 Q'; vauto.
  - inv H0; clear H0.
    + by apply prog_sos_neg_C in H10.
    + constructor; vauto.
  - apply istep_send with P'0 Q'; vauto.
    inv H0; clear H0. by apply prog_sos_neg_C in H12.
  - apply istep_recv with P'0 Q'; vauto.
    inv H0; clear H0. by apply prog_sos_neg_C in H12.
  - apply istep_comm with P'0 Q'; vauto.
    inv H0; clear H0.
    + by apply prog_sos_neg_C in H12.
    + by apply prog_sos_neg_C in H13.
    + by apply prog_sos_neg_C in H13.
  - apply istep_query with P'0 Q'; vauto.
    inv H0; clear H0. by apply prog_sos_neg_C in H12.
Qed.

Lemma istep_bisim_l :
  forall C P1 P2 h s l C' Q h' s',
  bisim P1 P2 ->
  istep C P1 h s l C' Q h' s' ->
  istep C P2 h s l C' Q h' s'.
Proof.
  intros C P1 P2 h s l C' Q h' s' H1 H2.
  inv H2; vauto.
  - apply istep_comp; auto. by rewrite <- H1.
  - apply istep_send with P' Q'; auto. by rewrite <- H1.
  - apply istep_recv with P' Q'; auto. by rewrite <- H1.
  - apply istep_comm with P' Q'; auto. by rewrite <- H1.
  - apply istep_query with P' Q'; auto. by rewrite <- H1.
Qed.

Lemma istep_bisim_r :
  forall C P h s l C' Q1 Q2 h' s',
  bisim Q1 Q2 ->
  istep C P h s l C' Q1 h' s' ->
  istep C P h s l C' Q2 h' s'.
Proof.
  intros C P h s l C' Q1 Q2 h' s' H1 H2.
  inv H2; vauto.
  - apply istep_comp; auto. by rewrite <- H1.
  - apply istep_send with P' Q'; auto. by rewrite <- H1.
  - apply istep_recv with P' Q'; auto. by rewrite <- H1.
  - apply istep_comm with P' Q'; auto. by rewrite <- H1.
  - apply istep_query with P' Q'; auto. by rewrite <- H1.
Qed.

Add Parametric Morphism : istep
  with signature eq ==> bisim ==> eq ==> eq ==> eq ==> eq ==> bisim ==> eq ==> eq ==> iff as istep_bisim_mor.
Proof.
  intros C P1 P2 H1 h s l C' Q1 Q2 H2 h' s'. split; intro H3.
  - apply istep_bisim_l with P1; auto.
    apply istep_bisim_r with Q1; auto.
  - apply istep_bisim_l with P2; auto.
    apply istep_bisim_r with Q2; auto.
Qed.

Lemma istep_proc_frame :
  forall C P Q h s l C' P' h' s',
  istep C P h s l C' P' h' s' ->
  istep C (Ppar P Q) h s l C' (Ppar P' Q) h' s'.
Proof.
  intros C P1 Q h s l C' P1' h' s' H. inv H; vauto.
  - apply istep_comp; auto. by rewrite H1.
  - apply istep_send with (Ppar P' Q)(Ppar Q' Q); auto.
    + by rewrite H1.
    + by apply pstep_par_frame_l.
    + by rewrite H3.
  - apply istep_recv with (Ppar P' Q)(Ppar Q' Q); auto.
    + by rewrite H1.
    + by apply pstep_par_frame_l.
    + by rewrite H3.
  - apply istep_comm with (Ppar P' Q)(Ppar Q' Q); auto.
    + by rewrite H1.
    + by apply pstep_par_frame_l.
    + by rewrite H3.
  - apply istep_query with (Ppar P' Q)(Ppar Q' Q); auto.
    + by rewrite H1.
    + by apply pstep_par_frame_l.
    + by rewrite H3.
Qed.

Lemma istep_fv_mod :
  forall l C h P s C' h' P' s',
  istep C P h s l C' P' h' s' ->
    (forall x, In x (cmd_fv C') -> In x (cmd_fv C)) /\
    (forall x, In x (cmd_mod C') -> In x (cmd_mod C)) /\
    (forall x, ~ In x (cmd_mod C) -> s x = s' x).
Proof.
  induction l; intros C h P s C' h' P' s'; intros STEP.
  - inv STEP. repeat split; vauto.
    + intros x H3. apply step_fv_mod in H0.
      destruct H0 as (M1 & M2 & M3). by apply M1.
    + intros x H3. apply step_fv_mod in H0.
      destruct H0 as (M1 & M2 & M3). by apply M2.
    + intros x H3. apply step_fv_mod in H0.
      destruct H0 as (M1 & M2 & M3). by apply M3.
  - inv STEP. repeat split; vauto.
    + intros x H3. apply step_fv_mod in H1.
      destruct H1 as (M1 & M2 & M3). by apply M1.
    + intros x H3. apply step_fv_mod in H1.
      destruct H1 as (M1 & M2 & M3). by apply M2.
    + intros x H3. apply step_fv_mod in H1.
      destruct H1 as (M1 & M2 & M3). by apply M3.
  - inv STEP. repeat split; vauto.
    + intros x H3. apply step_fv_mod in H1.
      destruct H1 as (M1 & M2 & M3). by apply M1.
    + intros x H3. apply step_fv_mod in H1.
      destruct H1 as (M1 & M2 & M3). by apply M2.
    + intros x H3. apply step_fv_mod in H1.
      destruct H1 as (M1 & M2 & M3). by apply M3.
  - inv STEP. repeat split; vauto.
    + intros x H3. apply step_fv_mod in H1.
      destruct H1 as (M1 & M2 & M3). by apply M1.
    + intros x H3. apply step_fv_mod in H1.
      destruct H1 as (M1 & M2 & M3). by apply M2.
    + intros x H3. apply step_fv_mod in H1.
      destruct H1 as (M1 & M2 & M3). by apply M3.
  - inv STEP. repeat split; vauto.
    + intros x H3. apply step_fv_mod in H.
      destruct H as (M1 & M2 & M3). by apply M1.
    + intros x H3. apply step_fv_mod in H.
      destruct H as (M1 & M2 & M3). by apply M2.
    + intros x H3. apply step_fv_mod in H.
      destruct H as (M1 & M2 & M3). by apply M3.
Qed.

Lemma istep_agree :
  forall l C h P s1 s2 C' h' P' s1' (phi : Var -> Prop),
    (forall x, In x (cmd_fv C) -> phi x) ->
    (forall x, phi x -> s1 x = s2 x) ->
    istep C P h s1 l C' P' h' s1' ->
  exists s2',
    (forall x, phi x -> s1' x = s2' x) /\
    istep C P h s2 l C' P' h' s2'.
Proof.
  induction l; intros C h P1 s1 s2 C' h' P1' s1' phi H1 H2 STEP.
  - inv STEP. apply step_agree with (s2 := s2)(phi := phi) in H0; auto.
    destruct H0 as (s2' & H5 & H6). exists s2'. intuition.
    apply istep_query with (P' := P')(Q' := Q'); auto.
  - inv STEP. apply step_agree with (s2 := s2)(phi := phi) in H3; auto.
    destruct H3 as (s2' & H5 & H6). exists s2'. intuition.
    apply istep_send with (P' := P')(Q' := Q'); auto.
  - inv STEP. apply step_agree with (s2 := s2)(phi := phi) in H3; auto.
    destruct H3 as (s2' & H5 & H6). exists s2'. intuition.
    apply istep_recv with (P' := P')(Q' := Q'); auto.
  - inv STEP. apply step_agree with (s2 := s2)(phi := phi) in H3; auto.
    destruct H3 as (s2' & H5 & H6). exists s2'. intuition.
    apply istep_comm with (P' := P')(Q' := Q'); auto.
  - inv STEP. apply step_agree with (s2 := s2)(phi := phi) in H; auto.
    destruct H as (s2' & H5 & H6). exists s2'. intuition vauto.
Qed.

Lemma istep_agree_sim :
  forall C h P s1 s2 l C' h' P' s1' s2',
    (forall x, In x (cmd_fv C) -> s1 x = s2 x) ->
    (forall x, In x (cmd_fv C) -> s1' x = s2' x) ->
  step C h s1 l C' h' s1' ->
  istep C P h s2 l C' P' h' s2' ->
  istep C P h s1 l C' P' h' s1'.
Proof.
  induction C; intros h P s1 s2 l C' h' P' s1' s2' H1 H2 H3 H4.
  (* skip *)
  - inv H3.
  (* sequential composition *)
  - inv H3; clear H3.
    + rewrite <- istep_seq_l. apply IHC1 with s2 s2'; vauto.
      * intros x D1. apply H1. simpl.
        apply in_or_app. by left.
      * intros x D1. apply H2. simpl.
        apply in_or_app. by left.
      * by rewrite <- istep_seq_l in H4.
    + apply istep_comp_proc_pres in H4. rewrite <- H4.
      rewrite <- istep_seq_r. constructor.
  (* assignment *)
  - inv H3. constructor; vauto.
    by apply istep_comp_proc_pres in H4.
  (* heap reading *)
  - inv H3. constructor; vauto.
    by apply istep_comp_proc_pres in H4.
  (* heap writing *)
  - inv H3. constructor; vauto.
    by apply istep_comp_proc_pres in H4.
  (* if-then-else *)
  - inv H3; clear H3.
    + inv H4. clear H4. constructor; vauto.
    + inv H4. clear H4. constructor; vauto.
  (* while loops *)
  - inv H3. clear H3. inv H4. clear H4.
    constructor; vauto.
  (* parallel composition *)
  - inv H3; clear H3.
    + apply istep_par_l. apply IHC1 with s2 s2'; vauto.
      * intros x D1. apply H1. simpl.
        apply in_or_app. by left.
      * intros x D1. apply H2. simpl.
        apply in_or_app. by left.
      * by apply istep_par_l in H4.
    + apply istep_par_r. apply IHC2 with s2 s2'; vauto.
      * intros x D1. apply H1. simpl.
        apply in_or_app. by right.
      * intros x D1. apply H2. simpl.
        apply in_or_app. by right.
      * by apply istep_par_r in H4.
    + constructor; vauto. inv H4.
    + inv H4. clear H4.
      apply istep_comm with P'0 Q'; vauto.
    + inv H4. clear H4.
      apply istep_comm with P'0 Q'; vauto.
  (* heap allocation *)
  - inv H3. clear H3. constructor; vauto. inv H4.
  (* heap disposal *)
  - inv H3. clear H3. constructor; vauto. inv H4.
  (* sending *)
  - inv H3. clear H3. inv H4. clear H4.
    apply istep_send with P'0 Q'; vauto.
  (* receiving *)
  - inv H3. clear H3. inv H4. clear H4.
    apply istep_recv with P'0 Q'; vauto.
  - inv H3. clear H3. inv H4. clear H4.
    apply istep_recv with P'0 Q'; vauto.
  (* querying *)
  - inv H3. clear H3. inv H4. clear H4.
    apply istep_query with P'0 Q'; vauto.
Qed.

(** ** Adequacy *)

Definition heap_preserve (l: Label)(ph1 ph2: PermHeap): Prop :=
  match l with
    | Lsend _ _ => ph1 = ph2
    | _ => True
  end.

CoInductive safe (C: Cmd)(ph: PermHeap)(P: Proc)(s: Store)(A: Assn): Prop :=
  | safe_prog :
      (* terminating programs satisfy the postcondition *)
      (C = Cskip -> sat ph P s A) /\
      (* computation preserves safety *)
      (forall phF C' h' s' l,
        permheap_disj ph phF ->
        let h := permheap_concr (permheap_add ph phF) in
        heap_finite h ->
        psafe P ->
        step C h s l C' h' s' ->
      exists ph',
        heap_preserve l ph ph' /\
        permheap_disj ph' phF /\
        permheap_concr (permheap_add ph' phF) = h' /\
        heap_finite h' /\
      exists P',
        psafe P' /\
        istep C P h s l C' P' h' s' /\
        safe C' ph' P' s' A) ->
    safe C ph P s A.

Lemma safe_skip :
  forall ph P s A, sat ph P s A <-> safe Cskip ph P s A.
Proof.
  intros ph P s A. split; intro H1.
  - constructor. split; vauto.
    intros ????????? STEP. inv STEP.
  - inv H1. clear H1.
    destruct H as (H & _). by apply H.
Qed.

Lemma safe_agree :
  forall C ph P s1 s2 A,
    (forall x, assn_fv A x -> s1 x = s2 x) ->
    (forall x, In x (cmd_fv C) -> s1 x = s2 x) ->
  safe C ph P s1 A ->
  safe C ph P s2 A.
Proof.
  cofix CH.
  intros C ph P s1 s2 A H1 H2 H3.
  repeat split.
  (* termination *)
  - intro H4. clarify.
    apply sat_agree with s1; auto.
    by apply safe_skip in H3.
  (* computation *)
  - simpl. intros phF C' h' s' l H4 H5 H6 STEP.
    generalize STEP. intro STEP'.
    apply step_agree with (s2 := s1)(phi := fun x => In x (cmd_fv C) \/ assn_fv A x) in STEP; vauto.
    2 : { intros x [H7 | H7].
      + symmetry. by apply H2.
      + symmetry. by apply H1. }
    destruct STEP as (s2' & H7 & H8).
    inv H3. clear H3. destruct H as (_ & H).
    simpl in H. apply H in H8; vauto. clear H.
    destruct H8 as (ph' & D1 & D2 & D3 & D4 & P' & D5 & D6 & D7).
    exists ph'. intuition.
    exists P'. intuition.
    + apply istep_agree with (s2 := s2)(phi := fun x => In x (cmd_fv C) \/ assn_fv A x) in D6; vauto.
      destruct D6 as (s3 & D6 & D8).
      apply istep_agree_sim with s2 s3; vauto.
      * intros x S1. rewrite H7; vauto.
        apply D6. by left.
      * intros x [S1 | S1].
        ** apply H2. vauto.
        ** apply H1. vauto.
    + apply CH with s2'; vauto.
      * intros x S1. symmetry. apply H7. vauto.
      * intros x S1. symmetry. apply H7. vauto.
        left. apply step_fv_mod in STEP'.
        destruct STEP' as (STEP' & _).
        by apply STEP'.
Qed.

Lemma safe_bisim :
  forall C ph P1 P2 s A,
  bisim P1 P2 -> safe C ph P1 s A -> safe C ph P2 s A.
Proof.
  intros C ph P1 P2 s A H1 H2.
  repeat split.
  (* termination *)
  - intro H3. clarify. rewrite <- safe_skip in H2.
    by rewrite <- H1.
  (* computation *)
  - simpl. intros phF C' h' s' l H3 H4 H5 H6.
    inv H2. clear H2. destruct H as (_ & H2).
    apply H2 in H6; clear H2; vauto.
    2 : { by rewrite H1. }
    destruct H6 as (ph' & D1 & D2 & D3 & D4 & P' & D5 & D6 & D7).
    exists ph'. intuition.
    exists P'. intuition.
    by rewrite <- H1.
Qed.

Add Parametric Morphism : safe
  with signature eq ==> eq ==> bisim ==> eq ==> eq ==> iff as safe_mor.
Proof.
  intros C ph P1 P2 H1 s A. split; intro H2.
  - apply safe_bisim with P1; auto.
  - apply safe_bisim with P2; auto.
Qed.

(** ** Proof rules *)

Definition csl (A1: Assn)(C: Cmd)(A2: Assn): Prop :=
  forall ph P s, permheap_valid ph -> sat ph P s A1 -> safe C ph P s A2.

(** *** Skip *)

Theorem rule_skip :
  forall A, csl A Cskip A.
Proof.
  intros A ph P s H1 H2. by apply safe_skip.
Qed.

(** *** Sequential composition *)

Lemma safe_seq :
  forall C1 C2 A1 A2 ph P s,
  permheap_valid ph ->
  safe C1 ph P s A1 ->
  (forall ph' P' s',
    permheap_valid ph' ->
    sat ph' P' s' A1 ->
    safe C2 ph' P' s' A2) ->
  safe (Cseq C1 C2) ph P s A2.
Proof.
  cofix CH.
  intros C1 C2 A1 A2 ph P s H1 H2 H3.
  constructor. split.
  (* termination *)
  - intro H4. vauto.
  (* computation *)
  - simpl. intros phF C' h' s' l H4 H5 H6 STEP.
    inv STEP; clear STEP.
    (* step in [C1] *)
    + apply H2 in H13; auto. clear H2.
      destruct H13 as (ph'&D1&D2&D3&D4&P'&D5&D6&D7).
      exists ph'. intuition.
      exists P'. intuition.
      * rewrite <- istep_seq_l; auto.
      * apply CH with A1; auto.
        by apply permheap_disj_valid_l in D2.
    (* [C1] terminated *)
    + exists ph. intuition.
      exists P. intuition.
      * rewrite <- istep_seq_r; vauto.
      * apply H3; auto.
        by apply safe_skip in H2.
Qed.

Theorem rule_seq :
  forall A1 A2 A3 C1 C2,
  csl A1 C1 A2 ->
  csl A2 C2 A3 ->
  csl A1 (Cseq C1 C2) A3.
Proof.
  cofix CH.
  intros A1 A2 A3 C1 C2 H1 H2. red.
  intros ph P s H3 H4.
  apply safe_seq with A2; auto.
Qed.

(** *** If-then-else *)

Lemma safe_ite :
  forall A1 A2 B C1 C2 ph P s,
  sat ph P s A1 ->
  (sat ph P s (Astar A1 (Aplain B)) -> safe C1 ph P s A2) ->
  (sat ph P s (Astar A1 (Aplain (Bnot B))) -> safe C2 ph P s A2) ->
  safe (Cite B C1 C2) ph P s A2.
Proof.
  intros A1 A2 B C1 C2 ph P s H1 H2 H3.
  constructor. split; vauto. simpl.
  intros phF C' h' s' l H4 H5 H6 STEP.
  inv STEP; clear STEP; vauto.
  (* [B] evaluates positively *)
  - exists ph. intuition.
    exists P. intuition vauto.
    apply H2. simpl.
    exists ph, permheap_iden. intuition auto.
    { apply permheap_disj_iden_l.
      by apply permheap_disj_valid_l in H4. }
    { by rewrite permheap_add_iden_l. }
    exists P, Pepsilon. intuition.
    rewrite par_epsilon_r. auto.
  (* [B] evaluates negatively *)
  - exists ph. intuition.
    exists P. intuition vauto.
    apply H3. simpl.
    exists ph, permheap_iden. intuition vauto.
    { apply permheap_disj_iden_l.
      by apply permheap_disj_valid_l in H4. }
    { by rewrite permheap_add_iden_l. }
    exists P, Pepsilon. intuition.
    rewrite par_epsilon_r. auto.
Qed.

Theorem rule_ite :
  forall A1 A2 B C1 C2,
  csl (Astar A1 (Aplain B)) C1 A2 ->
  csl (Astar A1 (Aplain (Bnot B))) C2 A2 ->
  csl A1 (Cite B C1 C2) A2.
Proof.
  intros A1 A2 B C1 C2 H1 H2. red.
  intros ph P s H3 H4. apply safe_ite with A1; auto.
Qed.

(** *** While loops *)

Lemma safe_while1 :
  forall B C1 C2 ph P s A,
  safe C1 ph P s A ->
  csl (Astar A (Aplain B)) C2 A ->
  safe (Cseq C1 (Cwhile B C2)) ph P s (Astar A (Aplain (Bnot B))).
Proof.
  cofix CH.
  intros B C1 C2 ph P s A H1 H2.
  constructor. split; vauto. simpl.
  intros phF C' h' s' l H3 H4 H5 STEP.
  inv STEP; clear STEP.
  (* step in [C1] *)
  - apply H1 in H12; auto.
    destruct H12 as (ph'&D1&D2&D3&D4&P'&D5&D6&D7).
    exists ph'. intuition.
    exists P'. intuition.
    by apply istep_seq_l.
  (* [C1] terminated *)
  - exists ph. intuition.
    exists P. intuition vauto.
    apply safe_skip in H1.
    constructor. split; vauto. simpl.
    intros phF' C' h' s'' l D1 D2 D3 STEP.
    inv STEP; clear STEP.
    exists ph. intuition.
    exists P. intuition vauto.
    constructor. split; vauto. simpl.
    intros phF'' C' h' s' l F1 F2 F3 STEP.
    inv STEP; clear STEP.
    (* step in [C2] *)
    + exists ph. intuition.
      exists P. intuition vauto.
      apply CH; auto. apply H2; auto.
      { by apply permheap_disj_valid_l in F1. }
      exists ph, permheap_iden. intuition.
      { apply permheap_disj_iden_l.
        by apply permheap_disj_valid_l in F1. }
      { by rewrite permheap_add_iden_l. }
      exists P, Pepsilon. intuition.
      by apply par_epsilon_r.
    (* termination of the loop *)
    + exists ph. intuition.
      exists P. intuition vauto.
      apply safe_skip.
      exists ph, permheap_iden. intuition.
      { apply permheap_disj_iden_l.
        by apply permheap_disj_valid_l in F1. }
      { by rewrite permheap_add_iden_l. }
      exists P, Pepsilon. intuition vauto.
      { by apply par_epsilon_r. }
      simpl. apply eq_true_not_negb. vauto.
Qed.

Lemma safe_while2 :
  forall B C ph P s A,
  csl (Astar A (Aplain B)) C A ->
  sat ph P s A ->
  safe (Cwhile B C) ph P s (Astar A (Aplain (Bnot B))).
Proof.
  intros B C ph P s A H1 H2. constructor.
  split; vauto. simpl.
  intros phF C' h' s' l H3 H4 H5 STEP.
  inv STEP. clear STEP. exists ph. intuition.
  exists P. intuition vauto.
  apply safe_ite with A; auto.
  (* any loop iteration must be safe *)
  - intro H6. apply safe_while1; auto.
    apply H1; auto.
    by apply permheap_disj_valid_l in H3.
  (* safety must be preserved after termination of the loop *)
  - intro H6. by apply safe_skip.
Qed.

Theorem rule_while :
  forall A B C,
  csl (Astar A (Aplain B)) C A ->
  csl A (Cwhile B C) (Astar A (Aplain (Bnot B))).
Proof.
  intros A B C CSL. red. intros ph P s H1 H2.
  apply safe_while2; auto.
Qed.

(** *** Assignment *)

Lemma safe_assign :
  forall A x E ph P s,
  sat ph P s (assn_subst x E A) -> safe (Cass x E) ph P s A.
Proof.
  cofix CH. intros A x E ph P s H1.
  repeat split; vauto. simpl.
  intros phF C' h' s' l H2 H3 H4 STEP. inv STEP.
  exists ph. intuition.
  exists P. intuition vauto.
  apply safe_skip. rewrite sat_subst in H1. vauto.
Qed.

Theorem rule_assign :
  forall A x E,
  csl (assn_subst x E A) (Cass x E) A.
Proof.
  ins. red. split; vauto. ins. by apply safe_assign.
Qed.

(** *** Framing *)

Lemma safe_frame :
  forall C ph1 ph2 P1 P2 s A1 A2,
  permheap_disj ph1 ph2 ->
  disjoint (assn_fv A2) (cmd_mod C) ->
  sat ph2 P2 s A2 ->
  safe C ph1 P1 s A1 ->
  safe C (permheap_add ph1 ph2) (Ppar P1 P2) s (Astar A1 A2).
Proof.
  cofix CH.
  intros C ph1 ph2 P1 P2 s A1 A2 H1 FV1 SAT1 SAFE1.
  repeat split.
  (* termination *)
  - intros ?. clarify. apply safe_skip in SAFE1.
    exists ph1, ph2. intuition.
    exists P1, P2. intuition.
  (* computation *)
  - simpl. intros phF C' h' s' l H2 H3 SAFE2 STEP.
    inv SAFE1. clear SAFE1. destruct H as (_ & SAFE1).
    rewrite permheap_add_swap_r with (ph2 := ph2) in STEP.
    rewrite permheap_add_assoc in STEP.
    rewrite permheap_add_comm with phF ph2 in STEP.
    apply SAFE1 in STEP; clear SAFE1; vauto.
    + destruct STEP as (ph' & D1 & D2 & D3 & D4 & P' & D5 & D6 & D7).
      clarify. exists (permheap_add ph' ph2). intuition.
      { red in D1. desf. }
      { apply permheap_disj_assoc_r; auto.
        apply permheap_disj_add_l with ph1; auto. }
      { rewrite permheap_add_swap_r with (ph2 := ph2).
        rewrite permheap_add_assoc.
        by rewrite permheap_add_comm with phF ph2. }
      exists (Ppar P' P2). intuition.
      { apply psafe_par_rev in SAFE2.
        destruct SAFE2 as (_ & SAFE2).
        by apply psafe_par. }
      { rewrite permheap_add_swap_r with (ph2 := ph2).
        rewrite permheap_add_assoc.
        rewrite permheap_add_comm with phF ph2.
        by apply istep_proc_frame. }
      apply CH; vauto.
      { apply permheap_disj_add_r with phF; auto.
        apply permheap_disj_add_l with ph1; auto. }
      { red. intros x H7 H8. apply istep_fv_mod in D6.
        destruct D6 as (FV2 & FV3 & FV4).
        apply FV1 in H7. by apply FV3 in H8. }
      { apply istep_fv_mod in D6.
        destruct D6 as (FV2 & FV3 & FV4).
        apply sat_agree with s; auto.
        intros x ?. apply FV4. intro. by apply FV1 with x. }
    + apply permheap_disj_assoc_l; auto.
    + by rewrite <- permheap_add_assoc.
    + apply psafe_par_rev in SAFE2. desf.
Qed.

Theorem rule_frame :
  forall A1 A2 A3 C,
  disjoint (assn_fv A3) (cmd_mod C) ->
  csl A1 C A2 ->
  csl(Astar A1 A3) C (Astar A2 A3).
Proof.
  intros A1 A2 A3 C H1 H2. red.
  intros ph P s H3 H4. simpl in H4.
  destruct H4 as (ph1&ph2&H4&H5&P1&P2&H6&H7&H8).
  rewrite <- H5, <- H6. apply safe_frame; vauto.
  apply H2; vauto. by apply permheap_disj_valid_l in H4.
Qed.

(** *** Parallel composition *)

Lemma safe_par :
  forall C1 C2 ph1 ph2 P1 P2 s A1 A2,
  permheap_disj ph1 ph2 ->
  disjoint (cmd_fv C1) (cmd_mod C2) ->
  disjoint (assn_fv A1) (cmd_mod C2) ->
  disjoint (cmd_fv C2) (cmd_mod C1) ->
  disjoint (assn_fv A2) (cmd_mod C1) ->
  safe C1 ph1 P1 s A1 ->
  safe C2 ph2 P2 s A2 ->
  safe (Cpar C1 C2) (permheap_add ph1 ph2) (Ppar P1 P2) s (Astar A1 A2).
Proof.
  cofix CH.
  intros C1 C2 ph1 ph2 P1 P2 s A1 A2 H1 H2 H3 H4 H5 SAFE1 SAFE2.
  repeat split.
  (* termination *)
  - intro H8. clarify.
  (* computation *)
  - simpl. intros phF C' h' s' l H6 H7 SAFE3 STEP.
    inv STEP; clear STEP.
    (* step in left program *)
    + inv SAFE1. clear SAFE1. destruct H as (_ & H).
      simpl in H. specialize H with (permheap_add ph2 phF) C1' h' s' l.
      rewrite permheap_add_assoc in H14.
      apply H in H14; clear H.

      2:{ apply permheap_disj_assoc_l; auto. }
      2:{ rewrite <- permheap_add_assoc. auto. }
      2:{ apply psafe_par_rev in SAFE3. desf. }

      destruct H14 as (ph' & D1 & D2 & D3 & D4 & P' & D5 & D6 & D7).
      exists (permheap_add ph' ph2). intuition.

      { red in D1. desf. }
      { apply permheap_disj_assoc_r; auto.
        apply permheap_disj_add_l with ph1; auto. }
      { by rewrite permheap_add_assoc. }

      exists (Ppar P' P2). intuition.

      { apply psafe_par_rev in SAFE3.
        destruct SAFE3 as (_ & SAFE3).
        apply psafe_par; auto. }
      { clarify. rewrite permheap_add_assoc with ph1 ph2 phF.
        apply istep_par_l.
        apply istep_proc_frame. auto. }

      apply CH; auto.

      { apply permheap_disj_add_r with phF; auto.
        apply permheap_disj_add_l with ph1; auto. }
      { red. intros x FV1 FV2. apply istep_fv_mod in D6.
        destruct D6 as (D6 & _).
        apply D6 in FV1. by apply H2 with x. }
      { red. intros x FV1 FV2. apply istep_fv_mod in D6.
        destruct D6 as (_ & D6 & _).
        apply D6 in FV2. by apply H4 with x. }
      { red. intros x FV1 FV2. apply istep_fv_mod in D6.
        destruct D6 as (_ & D6 & _).
        apply D6 in FV2. by apply H5 with x. }

      apply safe_agree with s; vauto.

      { intros x S1. apply istep_fv_mod in D6.
        destruct D6 as (_ & _ & D6). apply D6.
        intro S2. red in H5. apply H5 with x; vauto. }
      { intros x S1. apply istep_fv_mod in D6.
        destruct D6 as (_ & _ & D6). apply D6.
        intro S2. red in H4. apply H4 with x; vauto. }

    (* step in right program *)
    + inv SAFE2. clear SAFE2. destruct H as (_ & H).
      simpl in H. specialize H with (permheap_add ph1 phF) C2' h' s' l.
      rewrite permheap_add_comm with ph1 ph2 in H14.
      rewrite permheap_add_assoc in H14.
      apply H in H14; clear H.

      2:{ apply permheap_disj_assoc_l; auto.
          by rewrite permheap_add_comm. }
      2:{ rewrite <- permheap_add_assoc.
          by rewrite permheap_add_comm with ph2 ph1. }
      2:{ apply psafe_par_rev in SAFE3. desf. }

      destruct H14 as (ph' & D1 & D2 & D3 & D4 & P' & D5 & D6 & D7).

      exists (permheap_add ph1 ph'). intuition.

      { red in D1. desf. }
      { rewrite permheap_add_comm.
        apply permheap_disj_assoc_r; auto.
        apply permheap_disj_add_l with ph2; auto.
        by rewrite permheap_add_comm. }
      { rewrite permheap_add_comm with ph1 ph'.
        by rewrite permheap_add_assoc. }
      exists (Ppar P1 P'). intuition.
      { apply psafe_par_rev in SAFE3.
        destruct SAFE3 as (SAFE3 & _).
        apply psafe_par; auto. }
      { clarify. rewrite permheap_add_comm with ph1 ph2.
        rewrite permheap_add_assoc with ph2 ph1 phF.
        apply istep_par_r.
        rewrite par_comm with (P := P1)(Q := P2).
        rewrite par_comm with (P := P1)(Q := P').
        apply istep_proc_frame. auto. }

      apply CH; auto.

      { symmetry.
        apply permheap_disj_add_r with phF; auto.
        apply permheap_disj_add_l with ph2; auto.
        by rewrite permheap_add_comm. }
      { red. intros x FV1 FV2. apply istep_fv_mod in D6.
        destruct D6 as (_ & D6 & _).
        apply D6 in FV2. by apply H2 with x. }
      { red. intros x FV1 FV2. apply istep_fv_mod in D6.
        destruct D6 as (_ & D6 & _).
        apply D6 in FV2. by apply H3 with x. }
      { red. intros x FV1 FV2. apply istep_fv_mod in D6.
        destruct D6 as (D6 & _ & _).
        apply D6 in FV1. by apply H4 with x. }

      apply safe_agree with s; vauto.

      { intros x S1. apply istep_fv_mod in D6.
        destruct D6 as (_ & _ & D6). apply D6.
        intro S2. red in H3. apply H3 with x; vauto. }
      { intros x S1. apply istep_fv_mod in D6.
        destruct D6 as (_ & _ & D6). apply D6.
        intro S2. red in H2. apply H2 with x; vauto. }

    (* both programs are empty *)
    + exists (permheap_add ph1 ph2). intuition.
      exists (Ppar P1 P2). intuition.
      * constructor; vauto.
      * apply safe_skip. simpl.
        exists ph1, ph2. intuition.
        exists P1, P2. intuition.
        ** inv SAFE1. clear SAFE1.
           destruct H as (H & _). by apply H.
        ** inv SAFE2. clear SAFE2.
           destruct H as (H & _). by apply H.

    (* communication: left program sends, right program receives *)
    + inv SAFE1. clear SAFE1. destruct H as (_ & SAFE1).
      simpl in SAFE1. repeat rewrite permheap_add_assoc in H8.
      apply SAFE1 in H8; clear SAFE1; vauto.

      2:{ apply permheap_disj_assoc_l; vauto. }
      2:{ by rewrite <- permheap_add_assoc. }
      2:{ apply psafe_par_rev in SAFE3. desf. }

      destruct H8 as (ph1' & D1 & D2 & D3 & D4 & P1' & D5 & D6 & D7).
      simpl in D1. clarify. rename ph1' into ph1. clear D3.

      inv SAFE2. clear SAFE2. destruct H as (_ & SAFE2).
      simpl in SAFE2. repeat rewrite permheap_add_comm with ph1 ph2 in H15.
      repeat rewrite permheap_add_assoc in H15.
      apply SAFE2 in H15; clear SAFE2.

      2:{ apply permheap_disj_assoc_l.
          - by symmetry.
          - by rewrite permheap_add_comm with ph2 ph1. }
      2:{ rewrite <- permheap_add_assoc.
          by rewrite permheap_add_comm with ph2 ph1. }
      2:{ apply psafe_par_rev in SAFE3. desf. }

      destruct H15 as (ph2' & F1 & F2 & F3 & F4 & P2' & F5 & F6 & F7).
      simpl in F1. clear F1.

      exists (permheap_add ph1 ph2'). intuition.

      { red. vauto. }
      { rewrite permheap_add_comm.
        apply permheap_disj_assoc_r; auto.
        apply permheap_disj_add_l with ph2; auto.
        by rewrite permheap_add_comm. }
      { rewrite permheap_add_comm with ph1 ph2'.
        rewrite permheap_add_assoc.
        rewrite F3.
        rewrite <- permheap_add_assoc.
        by rewrite permheap_add_comm with ph2 ph1. }

      exists (Ppar P1' P2'). intuition.

      { apply psafe_par; vauto. }
      { inv D6. clear D6. inv F6. clear F6.
        rename P'0 into Q2, Q'0 into Q2'.
        rename P' into Q1, Q' into Q1'.
        apply istep_comm with (Ppar Q1 Q2) (Ppar Q1' Q2'); vauto.
        - apply step_comm_l; vauto.
          + by repeat rewrite permheap_add_assoc.
          + repeat rewrite permheap_add_comm with ph1 ph2.
            by repeat rewrite permheap_add_assoc.
        - apply bisim_par; vauto.
        - apply bisim_par; vauto. }

      apply CH; vauto.

      { symmetry. apply permheap_disj_add_r with phF; auto.
        apply permheap_disj_add_l with ph2; auto.
        by rewrite permheap_add_comm. }
      { red. intros x FV1 FV2.
        apply istep_fv_mod in D6. destruct D6 as (D6 & _).
        apply istep_fv_mod in F6. destruct F6 as (_ & F6 & _).
        apply D6 in FV1. apply F6 in FV2. by apply H2 with x. }
      { red. intros x FV1 FV2.
        apply istep_fv_mod in F6. destruct F6 as (_ & F6 & _).
        apply F6 in FV2. by apply H3 with x. }
      { red. intros x FV1 FV2.
        apply istep_fv_mod in D6. destruct D6 as (_ & D6 & _).
        apply istep_fv_mod in F6. destruct F6 as (F6 & _).
        apply D6 in FV2. apply F6 in FV1.
        by apply H4 with x. }
      { red. intros x FV1 FV2.
        apply istep_fv_mod in D6. destruct D6 as (_ & D6 & _).
        apply D6 in FV2. by apply H5 with x. }

      apply safe_agree with s; vauto.

      { intros x FV1. apply istep_fv_mod in F6.
        destruct F6 as (_ & _ & F6). apply F6.
        intro FV2. by apply H3 with x. }
      { intros x FV1. apply istep_fv_mod in F6.
        destruct F6 as (_ & _ & F6). apply F6.
        intro FV2. apply istep_fv_mod in D6.
        destruct D6 as (D6 & _). apply D6 in FV1.
        by apply H2 with x. }

    (* communication: right program sends, left program receives *)
    + inv SAFE1. clear SAFE1. destruct H as (_ & SAFE1).
      simpl in SAFE1. repeat rewrite permheap_add_assoc in H8.
      apply SAFE1 in H8; clear SAFE1; vauto.

      2:{ apply permheap_disj_assoc_l; vauto. }
      2:{ by rewrite <- permheap_add_assoc. }
      2:{ apply psafe_par_rev in SAFE3. desf. }

      destruct H8 as (ph1' & D1 & D2 & D3 & D4 & P1' & D5 & D6 & D7).
      simpl in D1. clear D1.

      inv SAFE2. clear SAFE2. destruct H as (_ & SAFE2).
      simpl in SAFE2. repeat rewrite permheap_add_comm with ph1 ph2 in H15.
      repeat rewrite permheap_add_assoc in H15.
      apply SAFE2 in H15; clear SAFE2.

      2:{ apply permheap_disj_assoc_l.
          - by symmetry.
          - by rewrite permheap_add_comm with ph2 ph1. }
      2:{ rewrite <- permheap_add_assoc.
          by rewrite permheap_add_comm with ph2 ph1. }
      2:{ apply psafe_par_rev in SAFE3. desf. }

      destruct H15 as (ph2' & F1 & F2 & F3 & F4 & P2' & F5 & F6 & F7).
      simpl in F1. clarify. rename ph2' into ph2. clear F3.

      exists (permheap_add ph1' ph2). intuition.

      { red. vauto. }
      { apply permheap_disj_assoc_r; auto.
        by apply permheap_disj_add_l with ph1. }
      { by repeat rewrite permheap_add_assoc. }

      exists (Ppar P1' P2'). intuition.

      { apply psafe_par; vauto. }
      { inv D6. clear D6. inv F6. clear F6.
        rename P'0 into Q2, Q'0 into Q2'.
        rename P' into Q1, Q' into Q1'.
        apply istep_comm with (Ppar Q1 Q2) (Ppar Q1' Q2'); vauto.
        - apply step_comm_r; vauto.
          + by repeat rewrite permheap_add_assoc.
          + repeat rewrite permheap_add_comm with ph1 ph2.
            by repeat rewrite permheap_add_assoc.
        - apply bisim_par; vauto.
        - apply bisim_par; vauto. }

      apply CH; vauto.

      { apply permheap_disj_add_r with phF; auto.
        apply permheap_disj_add_l with ph1; auto. }

      { red. intros x FV1 FV2.
        apply istep_fv_mod in D6. destruct D6 as (D6 & _).
        apply istep_fv_mod in F6. destruct F6 as (_ & F6 & _).
        apply D6 in FV1. apply F6 in FV2. by apply H2 with x. }
      { red. intros x FV1 FV2.
        apply istep_fv_mod in F6. destruct F6 as (_ & F6 & _).
        apply F6 in FV2. by apply H3 with x. }
      { red. intros x FV1 FV2.
        apply istep_fv_mod in D6. destruct D6 as (_ & D6 & _).
        apply istep_fv_mod in F6. destruct F6 as (F6 & _).
        apply D6 in FV2. apply F6 in FV1.
        by apply H4 with x. }
      { red. intros x FV1 FV2.
        apply istep_fv_mod in D6. destruct D6 as (_ & D6 & _).
        apply D6 in FV2. by apply H5 with x. }

      apply safe_agree with s; vauto.

      { intros x FV1. apply istep_fv_mod in D6.
        destruct D6 as (_ & _ & D6). apply D6.
        intro FV2. by apply H5 with x. }
      { intros x FV1. apply istep_fv_mod in D6.
        destruct D6 as (_ & _ & D6). apply D6.
        intro FV2. apply istep_fv_mod in F6.
        destruct F6 as (F6 & _). apply F6 in FV1.
        by apply H4 with x. }
Qed.

Theorem rule_par :
  forall C1 C2 A1 A2 A1' A2',
  disjoint (cmd_fv C1) (cmd_mod C2) ->
  disjoint (assn_fv A1') (cmd_mod C2) ->
  disjoint (cmd_fv C2) (cmd_mod C1) ->
  disjoint (assn_fv A2') (cmd_mod C1) ->
  csl A1 C1 A1' ->
  csl A2 C2 A2' ->
  csl (Astar A1 A2) (Cpar C1 C2) (Astar A1' A2').
Proof.
  intros C1 C2 A1 A2 A1' A2' FV1 FV2 FV3 FV4 CSL1 CSL2.
  red. intros ph P s H1 H2. simpl in H2.
  destruct H2 as (ph1 & ph2 & H2 & H3 & P1 & P2 & H4 & H5 & H6).
  clarify. rewrite <- H4.
  apply safe_par; vauto.
  - red in CSL1. apply CSL1 in H5; vauto.
    by apply permheap_disj_valid_l in H2.
  - red in CSL2. apply CSL2 in H6; vauto.
    by apply permheap_disj_valid_r in H2.
Qed.

(** *** Sending *)

Theorem rule_send :
  forall E T AP,
  csl (Aproc (APseq (APsend E T) AP)) (Csend E T) (Aproc AP).
Proof.
  intros E T AP ph P s H1 SAT1.
  constructor. split.
  (* termination *)
  - intros ?. vauto.
  (* computation *)
  - simpl. intros phF C' h' s' l H2 FIN1 SAFE1 STEP.
    inv STEP. rename v0 into v', s' into s.
    exists ph. intuition. destruct SAT1 as (P'' & H3).
    set (P' := Ppar (aproc_conv AP s) P'').
    exists P'. intuition.
    { rewrite H3 in SAFE1.
      apply psafe_par_rev in SAFE1. destruct SAFE1 as (SAFE1 & SAFE2).
      simpl in SAFE1. inv SAFE1. clear SAFE1. destruct H as (_ & SAFE1).
      subst P'. apply psafe_par; auto.
      assert (H4: pstep (Pseq (Psend (expr_conv E s) (expr_conv T s)) (aproc_conv AP s)) (PLsend (pexpr_eval (expr_conv E s)) (pexpr_eval (expr_conv T s))) (Pseq Pepsilon (aproc_conv AP s))) by vauto.
      apply SAFE1 in H4. clear SAFE1. rewrite pseq_epsilon_r in H4. simpls. }
    { inv STEP. clear H8. rewrite H3. subst P'.
      apply istep_proc_frame.
      apply istep_send with
        (P' := aproc_conv (APseq (APsend E T) AP) s)
        (Q' := aproc_conv (APseq APepsilon AP) s); auto.
      - repeat constructor. subst v'.
        rewrite expr_conv_eval. subst tag0.
        rewrite expr_conv_eval. constructor.
      - simpl. by rewrite pseq_epsilon_r. }
    inv STEP. clear H8. apply safe_skip.
    subst P'. exists P''. intuition.
Qed.

(** *** Receiving *)

Theorem rule_recv1 :
  forall x1 x2 y1 y2 AP,
  ~ aproc_fv AP x1 ->
  ~ aproc_fv AP x2 ->
  ~ y1 = y2 ->
  ~ x1 = y2 ->
  ~ x2 = y1 ->
  ~ x1 = x2 ->
  csl (Aproc (APsigma y1 (APsigma y2 (APseq (APrecv (Evar y1) (Evar y2)) AP)))) (Crecv1 x1 x2) (Aproc (aproc_subst y2 (Evar x2) (aproc_subst y1 (Evar x1) AP))).
Proof.
  intros x1 x2 y1 y2 AP H1 H2 V1 V2 V3 V4 ph P s H3 SAT1.
  constructor. split.
  (* termination *)
  - intros ?. vauto.
  (* computation *)
  - simpl. intros phF C' h' s' l H4 FIN1 SAFE1 STEP.
    inv STEP. exists ph. intuition. destruct SAT1 as (P'' & H5).
    assert (H6: pstep
	    (aproc_conv (APsigma y1 (APsigma y2 (APseq (APrecv (Evar y1) (Evar y2)) AP))) s)
	    (PLrecv v1 v2)
	    (aproc_conv (aproc_subst y1 (Econst v1) (aproc_subst y2 (Econst v2) (APseq APepsilon AP))) s)). {
      simpl. desf. apply pstep_sum with v1, pstep_sum with v2.
      apply pstep_seq_l. simpl. desf. vauto. }
    assert (H7:
      aproc_conv (aproc_subst y2 (Evar x2) (aproc_subst y1 (Evar x1) AP)) (updatestore (updatestore s x1 v1) x2 v2) =
      aproc_conv (aproc_subst y1 (Econst v1) (aproc_subst y2 (Econst v2) AP)) s). {
      rewrite aproc_conv_subst_upd, aproc_conv_subst_upd_swap, aproc_conv_subst_upd; vauto.
      + intro H8. apply aproc_fv_subst_in in H8; vauto.
      + intro H7. apply V1. by symmetry.
      + intro H7. apply V2. by symmetry.
      + intro H8. apply aproc_fv_subst_in in H8; vauto. simpls.
        apply and_not_or. intuition. }
    set (P' := Ppar (aproc_conv (aproc_subst y2 (Evar x2) (aproc_subst y1 (Evar x1) AP)) (updatestore (updatestore s x1 v1) x2 v2)) P'').
    exists P'. intuition.
    { rewrite H5 in SAFE1. apply psafe_par_rev in SAFE1.
      destruct SAFE1 as (SAFE1 & SAFE2).
      inv SAFE1. clear SAFE1. destruct H as (_ & SAFE1).
      apply SAFE1 in H6. clear SAFE1. simpl in H6.
      rewrite pseq_epsilon_r in H6. subst P'.
      apply psafe_par; auto. rewrite H7; vauto. }
    { rewrite H5. subst P'. apply istep_proc_frame.
      apply istep_recv with
        (P' := aproc_conv (APsigma y1 (APsigma y2 (APseq (APrecv (Evar y1) (Evar y2)) AP))) s)
        (Q' := aproc_conv (APseq APepsilon (aproc_subst y2 (Evar x2) (aproc_subst y1 (Evar x1) AP))) (updatestore (updatestore s x1 v1) x2 v2)); auto.
      - rewrite aproc_conv_sigma.
        apply pstep_sum with v1. simpl. desf. clear e.
        apply pstep_sum with v2. simpl. desf. clear e.
        rewrite <- H7. vauto.
      - simpls. intuition. by rewrite pseq_epsilon_r. }
    apply safe_skip. subst P'. exists P''.
    apply bisim_par; intuition.
Qed.

Theorem rule_recv2 :
  forall x y T AP,
  ~ aproc_fv AP x ->
  ~ In y (expr_fv T) ->
  csl (Aproc (APsigma y (APseq (APrecv (Evar y) T) AP))) (Crecv2 x T) (Aproc (aproc_subst y (Evar x) AP)).
Proof.
  intros x y T AP H1 H2 ph P s H3 SAT1.
  constructor. split.
  (* termination *)
  - intros ?. vauto.
  (* computation *)
  - simpl. intros phF C' h' s' l H4 FIN1 SAFE1 STEP.
    inv STEP. exists ph. intuition. destruct SAT1 as (P'' & H5).
    set (P' := Ppar (aproc_conv (aproc_subst y (Evar x) AP) (updatestore s x v)) P'').
    exists P'. intuition.
    { rewrite H5 in SAFE1.
      apply psafe_par_rev in SAFE1. destruct SAFE1 as (SAFE1 & SAFE2).
      inv SAFE1. clear SAFE1. destruct H as (_ & SAFE1).
      subst P'. repeat apply ppsafe_add; auto.
      rewrite aproc_conv_subst_upd; auto.
      assert (H6: pstep (aproc_conv (APsigma y (APseq (APrecv (Evar y) T) AP)) s) (PLrecv v tag) (aproc_conv (aproc_subst y (Econst v) (APseq APepsilon AP)) s)). {
        simpl. desf. apply pstep_sum with v.
        constructor. subst tag. rewrite expr_subst_pres.
        + rewrite expr_conv_eval. vauto.
        + intro H6. by apply H2. }
      apply SAFE1 in H6. clear SAFE1. simpl in H6.
      rewrite pseq_epsilon_r in H6. simpls.
      apply psafe_par; auto. }
    { rewrite H5. subst P'. apply istep_proc_frame.
      apply istep_recv with
        (P' := aproc_conv (APsigma y (APseq (APrecv (Evar y) T) AP)) s)
        (Q' := aproc_conv (APseq APepsilon (aproc_subst y (Evar x) AP)) (updatestore s x v)); auto.
      - rewrite aproc_conv_sigma.
        apply pstep_sum with v. simpl. desf. clear e.
        simpl. rewrite aproc_conv_subst_upd; auto.
        apply pstep_seq_l. rewrite expr_subst_pres.
        + subst tag. rewrite expr_conv_eval. vauto.
        + intro H6. by apply H2.
      - simpls. intuition. by rewrite pseq_epsilon_r. }
      apply safe_skip. subst P'. exists P''. intuition.
Qed.

(** *** Querying *)

Theorem rule_query :
  forall B AP,
  csl (Aproc (APseq (APassn B) AP)) (Cquery B) (Astar (Aproc AP) (Aplain B)).
Proof.
  intros B AP ph P s H1 SAT1.
  constructor. split.
  (* termination *)
  - intros H. inv H.
  (* computation *)
  - simpl. intros phF C' h' s' l H2 FIN1 SAFE1 STEP.
    inv STEP. rename s' into s. exists ph.
    intuition. destruct SAT1 as (P'' & H3).
    assert (H5: cond_eval B s). {
      rewrite cond_conv_eval. rewrite H3 in SAFE1.
      apply psafe_par_rev in SAFE1. destruct SAFE1 as (SAFE1 & _).
      simpl in SAFE1.
      apply psafe_seq_left in SAFE1. inv SAFE1. clear SAFE1.
      destruct H as (SAFE1 & _). by apply passn_nfault. }
    set (P' := Ppar (aproc_conv AP s) P'').
    exists P'. intuition.
    { rewrite H3 in SAFE1.
      apply psafe_par_rev in SAFE1. destruct SAFE1 as (SAFE1 & SAFE2).
      simpl in SAFE1. inv SAFE1. clear SAFE1. destruct H as (_ & SAFE1).
      subst P'. repeat apply ppsafe_add; auto.
      assert (H6: pstep (Pseq (Passn (cond_conv B s)) (aproc_conv AP s)) (PLassn (pcond_eval (cond_conv B s))) (Pseq Pepsilon (aproc_conv AP s))). {
        repeat constructor. by rewrite <- cond_conv_eval. }
      apply SAFE1 in H6. clear SAFE1. rewrite pseq_epsilon_r in H6.
      apply psafe_par; auto. }
    { subst P'. rewrite H3. apply istep_proc_frame.
      apply istep_query with
        (P' := aproc_conv (APseq (APassn B) AP) s)
        (Q' := aproc_conv (APseq APepsilon AP) s); auto.
      - apply pstep_seq_l. rewrite cond_conv_eval at 1. constructor.
        by rewrite <- cond_conv_eval.
      - simpl. intuition. by rewrite pseq_epsilon_r. }
    apply safe_skip. subst P'.
    exists ph, permheap_iden. intuition.
    { by rewrite permheap_add_iden_l. }
    exists (aproc_conv AP s), P''. intuition. simpl.
    exists Pepsilon. by rewrite par_epsilon_r.
Qed.

End Soundness.
