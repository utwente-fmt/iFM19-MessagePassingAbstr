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

(** * Program Logic *)

Module Type Assertions
  (doms: Domains)
  (procs: Processes doms)
  (heaps: Heaps doms)
  (progs: Programs doms procs heaps)
  (models: Models doms procs heaps progs).

Export doms procs heaps progs models.

(** ** Assertion Language *)

Inductive Assn :=
  | Aplain(B: Cond)
  | Aex(f: Val -> Assn)
  | Adisj(A1 A2: Assn)
  | Astar(A1 A2: Assn)
  | Awand(A1 A2: Assn)
  | Apointsto(q: Qc)(E1 E2: Expr)
  | Aproc(AP: AbstrProc)
  | Abisim (AP AQ: AbstrProc).

Add Search Blacklist "Assn_rect".
Add Search Blacklist "Assn_ind".
Add Search Blacklist "Assn_rec".

Definition Atrue: Assn := Aplain (Bconst true).
Definition Afalse: Assn := Aplain (Bconst false).

Lemma assn_aex_ext : forall f g, f = g -> Aex f = Aex g.
Proof. intuition vauto. Qed.

Fixpoint Aiter (xs: list Assn): Assn :=
  match xs with
    | nil => Atrue
    | A :: xs' => Astar A (Aiter xs')
  end.

Fixpoint assn_fv (A: Assn)(x: Var): Prop :=
  match A with
    | Aplain B => In x (cond_fv B)
    | Aex f => exists v: Val, assn_fv (f v) x
    | Adisj A1 A2
    | Astar A1 A2
    | Awand A1 A2 => assn_fv A1 x \/ assn_fv A2 x
    | Apointsto _ E1 E2 => In x (expr_fv E1) \/ In x (expr_fv E2)
    | Aproc AP => aproc_fv AP x
    | Abisim AP AQ => aproc_fv AP x \/ aproc_fv AQ x
  end.

Lemma assn_fv_iter :
  forall (xs: list Assn)(x: Var),
  assn_fv (Aiter xs) x <-> exists A, In A xs /\ assn_fv A x.
Proof.
  induction xs as [|A xs IH]; intro x.
  - split; intro H; desf.
  - split; intro H.
    + simpl in H. destruct H as [H | H].
      * exists A. split; vauto.
      * rewrite IH in H. destruct H as (A' & H1 & H2).
        exists A'. split; auto. by apply in_cons.
    + destruct H as (A' & H1 & H2).
      simpls. destruct H1 as [H1 | H1]; vauto.
      right. rewrite IH. exists A'. split; vauto.
Qed.

Fixpoint assn_subst (x: Var)(E: Expr)(A: Assn): Assn :=
  match A with
    | Aplain B => Aplain (cond_subst x E B)
    | Aex f => Aex (fun v => assn_subst x E (f v))
    | Adisj A1 A2 => Adisj (assn_subst x E A1) (assn_subst x E A2)
    | Astar A1 A2 => Astar (assn_subst x E A1) (assn_subst x E A2)
    | Awand A1 A2 => Awand (assn_subst x E A1) (assn_subst x E A2)
    | Apointsto q E1 E2 => Apointsto q (expr_subst x E E1) (expr_subst x E E2)
    | Aproc AP =>  Aproc (aproc_subst x E AP)
    | Abisim AP AQ => Abisim (aproc_subst x E AP) (aproc_subst x E AQ)
  end.

Definition Aexists (x: Var)(A: Assn): Assn :=
  Aex (fun v => assn_subst x (Econst v) A).

Lemma assn_subst_pres :
  forall A x E, ~ assn_fv A x -> assn_subst x E A = A.
Proof.
  induction A; intros x E H1; simpls.
  - rewrite cond_subst_pres; auto.
  - apply assn_aex_ext. extensionality y. rewrite H; auto.
    intro H2. apply H1. by exists y.
  - rewrite IHA1, IHA2; auto.
  - rewrite IHA1, IHA2; auto.
  - rewrite IHA1, IHA2; auto.
  - repeat rewrite expr_subst_pres; auto.
  - rewrite aproc_subst_pres; auto.
  - repeat rewrite aproc_subst_pres; auto.
Qed.

(** ** Sematics of Assertions *)

Fixpoint sat (ph: PermHeap)(P: Proc)(s: Store)(A: Assn): Prop :=
  match A with
    (* non-spatial assertions *)
    | Aplain B => cond_eval B s = true
    (* existential quantifiers *)
    | Aex f => exists v, sat ph P s (f v)
    (* disjunction *)
    | Adisj A1 A2 => sat ph P s A1 \/ sat ph P s A2
     (* separating conjunction *)
    | Astar A1 A2 =>
        exists ph1 ph2,
          permheap_disj ph1 ph2 /\
          permheap_add ph1 ph2 = ph /\
        exists P1 P2,
          bisim (Ppar P1 P2) P /\
          sat ph1 P1 s A1 /\
          sat ph2 P2 s A2
    (* magic wand *)
    | Awand A1 A2 =>
        forall ph' P',
        permheap_disj ph ph' ->
        sat ph' P' s A1 ->
        sat (permheap_add ph ph') (Ppar P P') s A2
    (* heap ownership *)
    | Apointsto q E1 E2 =>
        let l := expr_eval E1 s in
        let v := expr_eval E2 s in
        phc_leq (PHCcell q v) (ph l)
    (* process ownership *)
    | Aproc AP =>
        let P1 := aproc_conv AP s in
        exists P2, bisim P (Ppar P1 P2)
    (* process bisimulation *)
    | Abisim AP AQ => bisim (aproc_conv AP s) (aproc_conv AQ s)
  end.

Lemma sat_pproc_eq :
  forall A ph P1 P2 s, bisim P1 P2 -> sat ph P1 s A -> sat ph P2 s A.
Proof.
  induction A; intros ph P1 P2 s H1 H2; vauto.
  (* existential quantifiers *)
  - simpl in H2. destruct H2 as (v & H2).
    exists v. by apply H with P1.
  (* disjunction *)
  - simpls. destruct H2 as [H2 | H2].
    left. by apply IHA1 with P1.
    right. by apply IHA2 with P1.
  (* separating conjunction *)
  - simpls.
    destruct H2 as (ph1 & ph2 & D1 & H2 & P3 & P4 & H3 & SAT1 & SAT2).
    exists ph1, ph2. intuition.
    exists P3, P4. intuition. by rewrite <- H1.
  (* magic wand *)
  - simpls. intros ph' P' H3 H4.
    apply IHA2 with (Ppar P1 P').
    + rewrite H1. reflexivity.
    + apply H2; auto.
  (* process ownership *)
  - unfold sat in *.
    destruct H2 as (P & H2).
    exists P. rewrite <- H2. intuition.
Qed.

Add Parametric Morphism : sat
  with signature eq ==> bisim ==> eq ==> eq ==> iff
    as assn_sat_procmap_mor.
Proof.
  intros ph P1 P2 H1 s A. split; intro H2.
  - apply sat_pproc_eq with P1; auto.
  - apply sat_pproc_eq with P2; auto.
Qed.

Lemma sat_subst :
  forall A ph P s x E,
  sat ph P s (assn_subst x E A) <->
  sat ph P (updatestore s x (expr_eval E s)) A.
Proof.
  induction A; intros ph P s y E'; auto.
  (* non-spatial assertions *)
  - split; intro H; simpls.
    + by rewrite <- cond_eval_subst.
    + by rewrite cond_eval_subst.
  (* existential quantifiers *)
  - split; intro H1; simpls.
    + destruct H1 as (v & H1).
      exists v. by apply H.
    + destruct H1 as (v & H1).
      exists v. by apply <- H.
  (* disjunction *)
  - split; intro H; simpls.
    + destruct H as [H | H].
      * left. by rewrite <- IHA1.
      * right. by rewrite <- IHA2.
    + destruct H as [H | H].
      * left. by rewrite IHA1.
      * right. by rewrite IHA2.
  (* separating conjunction *)
  - split; intro H; simpls.
    + destruct H as (ph1 & ph2 & D1 & H1 & P1 & P2 & H2 & SAT1 & SAT2).
      exists ph1, ph2. intuition.
      exists P1, P2. intuition.
      * by apply IHA1.
      * by apply IHA2.
    + destruct H as (ph1 & ph2 & D1 & H1 & P1 & P2 & H2 & SAT1 & SAT2).
      exists ph1, ph2. intuition.
      exists P1, P2. intuition.
      * by apply <- IHA1.
      * by apply <- IHA2.
  (* magic wands *)
  - split; intro H; simpls.
    + intros ph' P' D1 SAT.
      apply IHA2, H; auto.
      by apply IHA1.
    + intros ph' P' D1 SAT.
      apply IHA2, H; auto.
      by apply IHA1.
  (* heap ownership *)
  - split; intro H.
    + simpl. repeat rewrite <- expr_eval_subst in *. vauto.
    + simpl. repeat rewrite expr_eval_subst in *. vauto.
  (* process ownership *)
  - split; intro H.
    + destruct H as (P' & H1). exists P'.
      rewrite H1. apply bisim_par; auto.
      by apply aproc_conv_subst.
    + destruct H as (P' & H1). exists P'.
      rewrite H1. apply bisim_par; auto.
      symmetry. by apply aproc_conv_subst.
  (* process bisimulation *)
  - split; intro H.
    + simpls. by repeat rewrite <- aproc_conv_subst.
    + simpls. by repeat rewrite aproc_conv_subst.
Qed.

Lemma sat_agree :
  forall A ph P s1 s2,
    (forall x, assn_fv A x -> s1 x = s2 x) ->
  sat ph P s1 A -> sat ph P s2 A.
Proof.
  induction A; intros ph P s1 s2 H1.
  (* plain assertions *)
  - intro H2. simpls.
    rewrite <- cond_agree with (s1 := s1); vauto.
  (* existential quantifiers *)
  - intro H2. simpls. destruct H2 as (v & H2).
    exists v. apply H with s1; auto.
    intros x H3. apply H1. by exists v.
  (* disjunction *)
  - intro H2. simpls.
    destruct H2 as [H2 | H2].
    + left. apply IHA1 with s1; auto.
    + right. apply IHA2 with s1; auto.
  (* separating conjunction *)
  - intro H2; simpls.
    destruct H2 as (ph1 & ph2 & D1 & H2 & P1 & P2 & H3 & SAT1 & SAT2).
    exists ph1, ph2. intuition.
    exists P1, P2. intuition.
    * apply IHA1 with s1; auto.
    * apply IHA2 with s1; auto.
  (* magic wand *)
  - intro H2. simpls.
    intros ph' P' H3 H4.
    apply IHA2 with s1; auto.
    apply H2; auto. apply IHA1 with s2; auto.
    intros x H6. symmetry. apply H1. by left.
  (* heap ownership *)
  - intro H2. unfold sat in *.
    rewrite <- expr_agree with E1 s1 s2, <- expr_agree with E2 s1 s2; auto.
    + red. intros x H3. apply H1. simpl. by right.
    + red. intros x H3. apply H1. simpl. by left.
  (* process ownership *)
  - intro H2. unfold sat in *.
    destruct H2 as (P' & H2). exists P'.
    rewrite aproc_conv_agree with AP s2 s1; auto.
    intros x H4. symmetry. apply H1. simpl. done.
  (* process bisimulation *)
  - intro H2. simpls.
    rewrite aproc_conv_agree with AP s2 s1, aproc_conv_agree with AQ s2 s1; auto.
    + intros x H3. symmetry. apply H1. by right.
    + intros x H3. symmetry. apply H1. by left.
Qed.

Lemma sat_weaken :
  forall A ph1 ph2 P1 P2 s,
  permheap_disj ph1 ph2 ->
  sat ph1 P1 s A ->
  sat (permheap_add ph1 ph2) (Ppar P1 P2) s A.
Proof.
  induction A; intros ph1 ph2 P1 P2 s H1 H2; auto.
  (* existential quantifiers *)
  - simpls. destruct H2 as (v & H2).
    exists v. by apply H.
  (* disjunction *)
  - simpls. destruct H2 as [H2 | H2].
    + left. by apply IHA1.
    + right. by apply IHA2.
  (* separating conjunction *)
  - simpls.
    destruct H2 as (ph3 & ph4 & D1 & H2 & P3 & P4 & H3 & SAT1 & SAT2).
    clarify. exists ph3, (permheap_add ph4 ph2). intuition.
    { by apply permheap_disj_assoc_l. }
    { by rewrite permheap_add_assoc. }
    exists P3, (Ppar P4 P2). intuition.
    { rewrite par_assoc; auto. by rewrite H3. }
    apply IHA2; auto. by apply permheap_disj_add_l with ph3.
  (* magic wand *)
  - simpls. intros ph' P' H4 H5.
    rewrite permheap_add_assoc, <- par_assoc.
    apply H2.
    { by apply permheap_disj_assoc_l. }
    rewrite permheap_add_comm, par_comm.
    apply IHA1; auto.
    apply permheap_disj_add_r with ph1; auto.
    symmetry. by rewrite permheap_add_comm.
  (* heap ownership *)
  - unfold sat in *. rewrite <- permheap_add_cell.
    apply phc_leq_weaken; vauto.
  (* process ownership *)
  - unfold sat in *. destruct H2 as (P & H2).
    exists (Ppar P P2). by rewrite par_assoc, <- H2.
Qed.

Lemma sat_iter_permut :
  forall xs ys,
  Permutation xs ys ->
  forall ph P s,
  sat ph P s (Aiter xs) ->
  sat ph P s (Aiter ys).
Proof.
  intros xs ys PERM.
  induction PERM; intros ph P s SAT; simpls.
  - destruct SAT as (ph1 & ph2 & D1 & H1 & P1 & P2 & H2 & SAT1 & SAT2).
    exists ph1, ph2. intuition.
    exists P1, P2. intuition.
  - destruct SAT as (ph1 & ph2 & D1 & H1 & P1 & P2 & H2 & SAT1 & SAT).
    destruct SAT as (ph3 & ph4 & D2 & H3 & P3 & P4 & H4 & SAT3 & SAT4).
    clarify.
    exists ph3, (permheap_add ph1 ph4). intuition.
    { apply permheap_disj_assoc_l.
      + symmetry. by apply permheap_disj_add_r with ph4.
      + rewrite permheap_add_comm.
        by apply permheap_disj_assoc_r. }
    { rewrite <- permheap_add_assoc.
      rewrite permheap_add_comm with ph3 ph1.
      by rewrite permheap_add_assoc. }
    exists P3, (Ppar P1 P4). intuition.
    { rewrite par_assoc.
      rewrite par_comm with (P := P3)(Q := P1).
      rewrite <- par_assoc.
      by rewrite <- H2, <- H4. }
    exists ph1, ph4. intuition.
    { apply permheap_disj_add_r with ph3; auto.
      by rewrite permheap_add_comm. }
    exists P1, P4. intuition.
  - by apply IHPERM2, IHPERM1.
Qed.

(** ** Logical consequence *)

Definition entails (A1 A2: Assn): Prop :=
  forall ph P s,
    permheap_valid ph -> sat ph P s A1 -> sat ph P s A2.
Definition entails_rev (A1 A2: Assn): Prop := entails A2 A1.
Definition equiv (A1 A2: Assn): Prop := entails A1 A2 /\ entails A2 A1.

Instance entails_refl : Reflexive entails.
Proof. intro. red. intuition. Qed.
Instance entails_trans : Transitive entails.
Proof. unfold entails. intuition. Qed.
Instance entails_rev_refl : Reflexive entails_rev.
Proof. intro. red. intuition. Qed.
Instance entails_rev_trans : Transitive entails_rev.
Proof. unfold entails_rev. intros ?????. by transitivity y. Qed.
Instance equiv_refl : Reflexive equiv.
Proof. red. ins. split; vauto. Qed.
Instance equiv_symm : Symmetric equiv.
Proof. red. intros A1 A2 (H1&H2). split; auto. Qed.
Instance equiv_trans : Transitive equiv.
Proof. red. intros A1 A2 A3 (H1&H2) (H3&H4). split; by transitivity A2. Qed.
Instance equiv_eq : Equivalence equiv.
Proof. split; intuition. Qed.

Hint Resolve entails_refl entails_rev_refl equiv_refl.

Lemma entails_flip : forall A1 A2, entails A1 A2 <-> entails_rev A2 A1.
Proof. ins. Qed.

(** *** Congruence *)

Add Parametric Morphism : Adisj
  with signature entails ==> entails ==> entails as adisj_entails_mor.
Proof.
  intros A1 A1' ENT1 A2 A2' ENT2.
  red. intros ph P s H1 [SAT | SAT]; simpls.
  - left. apply ENT1; auto.
  - right. apply ENT2; auto.
Qed.

Add Parametric Morphism : Adisj
  with signature equiv ==> equiv ==> entails as adisj_equiv_ent_mor.
Proof. intros A1 A2 (H1&_) A3 A4 (H2&_). by rewrite H1, H2. Qed.

Add Parametric Morphism : Adisj
  with signature equiv ==> equiv ==> equiv as adisj_equiv_mor.
Proof.
  intros A1 A2 (H1&H2) A3 A4 (H3&H4). split.
  - by rewrite H1, H3.
  - by rewrite H2, H4.
Qed.

Add Parametric Morphism : Astar
  with signature entails ==> entails ==> entails
    as astar_entails_mor.
Proof.
  intros A1 A1' ENT1 A2 A2' ENT2.
  red. intros ph P s H1 SAT. simpls.
  destruct SAT as (ph1 & ph2 & D1 & H2 & P1 & P2 & H3 & SAT1 & SAT2).
  exists ph1, ph2. intuition.
  exists P1, P2. intuition.
  - apply ENT1; auto. by apply permheap_disj_valid_l in D1.
  - apply ENT2; auto. by apply permheap_disj_valid_r in D1.
Qed.

Add Parametric Morphism : Astar
  with signature equiv ==> equiv ==> entails as astar_equiv_ent_mor.
Proof. intros A1 A2 (H1&_) A3 A4 (H2&_). by rewrite H1, H2. Qed.

Add Parametric Morphism : Astar
  with signature equiv ==> equiv ==> equiv as astar_equiv_mor.
Proof.
  intros A1 A2 (H1&H2) A3 A4 (H3&H4). split.
  - by rewrite H1, H3.
  - by rewrite H2, H4.
Qed.

Add Parametric Morphism : Awand
  with signature entails_rev ==> entails ==> entails as awand_entails_mor.
Proof.
  intros A1 A1' ENT1 A2 A2' ENT2.
  red. intros ph P s H1 WAND. simpls.
  intros ph' P' D1 SAT1.
  apply ENT2; auto. apply WAND; auto.
  apply ENT1; auto. by apply permheap_disj_valid_r in D1.
Qed.

Add Parametric Morphism : Awand
  with signature equiv ==> equiv ==> equiv as awand_equiv_mor.
Proof.
  intros A1 A2 (H1&H2) A3 A4 (H3&H4). split.
  - rewrite entails_flip in H2. by rewrite H2, H3.
  - rewrite entails_flip in H1. by rewrite H1, H4.
Qed.

(** *** Weakening rule *)

(** The weakening rule shows that our separation logic is _intuitionistic_. *)

Lemma sat_star_combine :
  forall ph1 ph2 P1 P2 s A1 A2,
  permheap_disj ph1 ph2 ->
  sat ph1 P1 s A1 ->
  sat ph2 P2 s A2 ->
  sat (permheap_add ph1 ph2) (Ppar P1 P2) s (Astar A1 A2).
Proof.
  intros ph1 ph2 P1 P2 s A1 A2 D1 H1 H2.
  exists ph1, ph2. repeat split; auto.
  exists P1, P2. intuition.
Qed.

Lemma sat_star_weaken :
  forall ph P s A1 A2,
  sat ph P s (Astar A1 A2) -> sat ph P s A1.
Proof.
  intros ph P s A1 A2 SAT.
  destruct SAT as (ph1 & ph2 & D1 & H1 & P1 & P2 & H2 & SAT1 & SAT2).
  rewrite <- H1, <- H2. by apply sat_weaken.
Qed.

Theorem assn_weaken :
  forall A1 A2, entails (Astar A1 A2) A1.
Proof.
  intros A1 A2 ph P s H1 H2.
  by apply sat_star_weaken with A2.
Qed.

(** *** Separating conjunction *)

(** Soundness of the axioms of _associativity_ and _commutativity_. *)

Lemma sat_star_assoc_l :
  forall ph P s A1 A2 A3,
  sat ph P s (Astar A1 (Astar A2 A3)) ->
  sat ph P s (Astar (Astar A1 A2) A3).
Proof.
  intros ph P s A1 A2 A3 SAT.
  destruct SAT as (ph1 & ph1' & D1 & H1 & P1 & P1' & H2 & SAT1 & SAT2).
  destruct SAT2 as (ph2 & ph3 & D3 & H3 & P2 & P3 & H4 & SAT2 & SAT3).
  exists (permheap_add ph1 ph2), ph3. repeat split; vauto.
  { by apply permheap_disj_assoc_r. }
  { by rewrite permheap_add_assoc. }
  exists (Ppar P1 P2), P3. intuition.
  { rewrite <- par_assoc. by rewrite H4. }
  exists ph1, ph2. repeat split; vauto.
  apply permheap_disj_add_r with ph3; auto.
Qed.

Theorem star_assoc_l :
  forall A1 A2 A3,
  entails (Astar A1 (Astar A2 A3)) (Astar (Astar A1 A2) A3).
Proof.
  intros A1 A2 A3 ph P s H1 H2.
  by apply sat_star_assoc_l.
Qed.

Lemma sat_star_assoc_r :
  forall ph P s A1 A2 A3,
  sat ph P s (Astar (Astar A1 A2) A3) ->
  sat ph P s (Astar A1 (Astar A2 A3)).
Proof.
  intros ph P s A1 A2 A3 SAT.
  destruct SAT as (ph1' & ph3 & D1 & H1 & P1' & P3 & H2 & SAT1 & SAT2).
  destruct SAT1 as (ph1 & ph2 & D3 & H3 & P1 & P2 & H4 & SAT1 & SAT3).
  exists ph1, (permheap_add ph2 ph3). repeat split; vauto.
  { by apply permheap_disj_assoc_l. }
  { by rewrite permheap_add_assoc. }
  exists P1, (Ppar P2 P3). intuition.
  { rewrite par_assoc; auto. by rewrite H4. }
  exists ph2, ph3. repeat split; vauto.
  apply permheap_disj_add_l with ph1; auto.
Qed.

Theorem star_assoc_r :
  forall A1 A2 A3,
  entails (Astar (Astar A1 A2) A3) (Astar A1 (Astar A2 A3)).
Proof.
  intros A1 A2 A3 ph P s H1 H2.
  by apply sat_star_assoc_r.
Qed.

Theorem star_assoc :
  forall A1 A2 A3,
  equiv (Astar (Astar A1 A2) A3) (Astar A1 (Astar A2 A3)).
Proof.
  ins. split; [apply star_assoc_r|apply star_assoc_l].
Qed.

Lemma sat_star_comm :
  forall ph P s A1 A2,
  sat ph P s (Astar A1 A2) -> sat ph P s (Astar A2 A1).
Proof.
  intros ph P s A1 A2 SAT.
  destruct SAT as (ph1 & ph2 & D1 & H1 & P1 & P2 & H2 & SAT1 & SAT2).
  exists ph2, ph1. repeat split; auto.
  - by rewrite permheap_add_comm.
  - exists P2, P1. intuition. by rewrite par_comm.
Qed.

Theorem star_comm :
  forall A1 A2, entails (Astar A1 A2) (Astar A2 A1).
Proof.
  intros A1 A2 ph P s H1 H2.
  by apply sat_star_comm.
Qed.

Theorem star_comm_equiv :
  forall A1 A2, equiv (Astar A1 A2) (Astar A2 A1).
Proof.
  ins. split; by apply star_comm.
Qed.

Corollary star_weaken_r :
  forall A1 A2, entails (Astar A1 A2) A2.
Proof.
  intros A1 A2. transitivity (Astar A2 A1).
  apply star_comm. apply assn_weaken.
Qed.

Corollary star_weaken_l :
  forall A1 A2, entails (Astar A1 A2) A1.
Proof.
  intros A1 A2. rewrite star_comm.
  by apply star_weaken_r.
Qed.

Lemma sat_star_true :
  forall ph P s A,
  permheap_valid ph -> sat ph P s A -> sat ph P s (Astar A Atrue).
Proof.
  intros ph P s A H1 SAT.
  exists ph, permheap_iden. repeat split; auto.
  { by rewrite permheap_add_iden_l. }
  exists P, Pepsilon. intuition vauto.
  by rewrite par_epsilon_r.
Qed.

Theorem star_true :
  forall A, entails A (Astar A Atrue).
Proof.
  intros A ph P s H1 SAT.
  by apply sat_star_true.
Qed.

Lemma sat_star_swap_l :
  forall ph P s A1 A2 A3,
  sat ph P s (Astar A1 (Astar A2 A3)) ->
  sat ph P s (Astar A2 (Astar A1 A3)).
Proof.
  intros ph P s A1 A2 A3 SAT.
  apply sat_star_assoc_r.
  apply sat_star_assoc_l in SAT.
  destruct SAT as (ph1 & ph2 & D1 & H1 & P1 & P2 & H2 & SAT1 & SAT2).
  exists ph1, ph2. repeat split; vauto.
  exists P1, P2. intuition. by apply sat_star_comm.
Qed.

Lemma star_swap_l :
  forall A1 A2 A3,
  entails (Astar A1 (Astar A2 A3)) (Astar A2 (Astar A1 A3)).
Proof.
  intros A1 A2 A3. rewrite star_assoc_l.
  rewrite star_comm with (A1 := A1)(A2 := A2).
  by rewrite star_assoc_r.
Qed.

Lemma sat_star_swap_r :
  forall ph P s A1 A2 A3,
  sat ph P s (Astar (Astar A1 A2) A3) ->
  sat ph P s (Astar (Astar A1 A3) A2).
Proof.
  intros ph P s A1 A2 A3 SAT.
  apply sat_star_assoc_l.
  apply sat_star_assoc_r in SAT.
  destruct SAT as (ph1 & ph2 & D1 & H1 & P1 & P2 & H2 & SAT1 & SAT2).
  exists ph1, ph2. repeat split; vauto.
  exists P1, P2. intuition. by apply sat_star_comm.
Qed.

Lemma star_swap_r :
  forall A1 A2 A3,
  entails (Astar (Astar A1 A2) A3) (Astar (Astar A1 A3) A2).
Proof.
  intros A1 A2 A3. rewrite star_assoc_r.
  rewrite star_comm with (A1 := A2)(A2 := A3).
  by rewrite star_assoc_l.
Qed.

Theorem star_add_l :
  forall A1 A2 A3, entails A2 A3 -> entails (Astar A1 A2) (Astar A1 A3).
Proof.
  intros ??? ENT. by rewrite ENT.
Qed.

Theorem star_add_r :
  forall A1 A2 A3, entails A2 A3 -> entails (Astar A2 A1) (Astar A3 A1).
Proof.
  intros ??? ENT. by rewrite ENT.
Qed.

Lemma star_disj_l :
  forall A1 A2 A3,
  entails (Astar A1 (Adisj A2 A3)) (Adisj (Astar A1 A2) (Astar A1 A3)).
Proof.
  intros A1 A2 A3 ph P s H1 SAT.
  destruct SAT as (ph1 & ph2 & H2 & H3 & P1 & P2 & H4 & SAT1 & SAT2).
  destruct SAT2 as [SAT2 | SAT2].
  - left. exists ph1, ph2. intuition. exists P1, P2. intuition.
  - right. exists ph1, ph2. intuition. exists P1, P2. intuition.
Qed.

Lemma star_disj_r :
  forall A1 A2 A3,
  entails (Adisj (Astar A1 A2) (Astar A1 A3)) (Astar A1 (Adisj A2 A3)).
Proof.
  intros A1 A2 A3 ph P s H1 [SAT | SAT];
  destruct SAT as (ph1 & ph2 & H2 & H3 & P1 & P2 & H4 & SAT1 & SAT2).
  - exists ph1, ph2. intuition. exists P1, P2. intuition. by left.
  - exists ph1, ph2. intuition. exists P1, P2. intuition. by right.
Qed.

Lemma star_disj :
  forall A1 A2 A3,
  equiv (Astar A1 (Adisj A2 A3)) (Adisj (Astar A1 A2) (Astar A1 A3)).
Proof.
  ins. split; [by apply star_disj_l|by apply star_disj_r].
Qed.

(** *** Iterated separating conjunction *)

Theorem aiter_permut :
  forall xs ys, Permutation xs ys -> entails (Aiter xs) (Aiter ys).
Proof.
  intros xs ys H. red. intros ph p s H1 SAT.
  by apply sat_iter_permut with xs.
Qed.

Add Parametric Morphism : Aiter
  with signature @Permutation Assn ==> entails as iter_permut_mor.
Proof.
  ins. by apply aiter_permut.
Qed.

Lemma sat_aiter_cons_l :
  forall ph p s A xs,
  sat ph p s (Astar A (Aiter xs)) -> sat ph p s (Aiter (A :: xs)).
Proof.
  intuition vauto.
Qed.

Theorem aiter_cons_l :
  forall A xs, entails (Astar A (Aiter xs)) (Aiter (A :: xs)).
Proof.
  intuition vauto.
Qed.

Lemma sat_aiter_cons_r :
  forall ph p s A xs,
  sat ph p s (Aiter (A :: xs)) -> sat ph p s (Astar A (Aiter xs)).
Proof.
  intuition vauto.
Qed.

Theorem aiter_cons_r :
  forall A xs, entails (Aiter (A :: xs)) (Astar A (Aiter xs)).
Proof.
  intuition vauto.
Qed.

Lemma sat_aiter_add_l :
  forall (xs ys : list Assn) ph P s,
  sat ph P s (Astar (Aiter xs) (Aiter ys)) -> sat ph P s (Aiter (xs ++ ys)).
Proof.
  induction xs as [|A xs IH]; intros ys ph P s SAT.
  - simpl (Aiter []) in SAT. rewrite app_nil_l.
    by apply sat_star_comm, sat_star_weaken in SAT.
  - simpl (Aiter (A :: xs)) in SAT.
    replace ((A :: xs) ++ ys) with (A :: (xs ++ ys)); auto.
    apply sat_aiter_cons_l. apply sat_star_assoc_r in SAT.
    destruct SAT as (ph1 & ph2 & H1 & H2 & P1 & P2 & H3 & SAT1 & SAT2).
    exists ph1, ph2. repeat split; vauto.
    exists P1, P2. intuition.
Qed.

Theorem aiter_add_l :
  forall xs ys, entails (Astar (Aiter xs) (Aiter ys)) (Aiter (xs ++ ys)).
Proof.
  intros xs ys ph P s H SAT.
  by apply sat_aiter_add_l.
Qed.

Lemma sat_aiter_add_r :
  forall (xs ys : list Assn) ph P s,
  permheap_valid ph ->
  sat ph P s (Aiter (xs ++ ys)) ->
  sat ph P s (Astar (Aiter xs) (Aiter ys)).
Proof.
  induction xs as [|A xs IH]; intros ys ph P s H1 SAT.
  - simpl (Aiter []). rewrite app_nil_l in SAT.
    apply sat_star_comm. by apply sat_star_true.
  - simpl (Aiter (A :: xs)).
    replace ((A :: xs) ++ ys) with (A :: (xs ++ ys)) in SAT; auto.
    apply sat_aiter_cons_r in SAT. apply sat_star_assoc_l.
    destruct SAT as (ph1 & ph2 & H2 & H3 & P1 & P2 & H4 & SAT1 & SAT2).
    exists ph1, ph2. repeat split; vauto.
    exists P1, P2. intuition. apply IH; vauto.
    by apply permheap_disj_valid_r in H2.
Qed.

Theorem aiter_add_r :
  forall xs ys, entails (Aiter (xs ++ ys)) (Astar (Aiter xs) (Aiter ys)).
Proof.
  induction xs; intro ys; simpls.
  - rewrite <- star_comm. by rewrite <- star_true.
  - rewrite <- star_assoc_l. by rewrite <- IHxs.
Qed.

Lemma sat_aiter_star_l :
  forall ph p s A1 A2 (xs : list Assn),
  sat ph p s (Aiter (Astar A1 A2 :: xs)) ->
  sat ph p s (Aiter (A1 :: A2 :: xs)).
Proof.
  intros ph p s A1 A2 xs SAT.
  simpl (Aiter (A1 :: A2 :: xs)).
  by apply sat_star_assoc_r.
Qed.

Theorem aiter_star_l :
  forall A1 A2 xs,
  entails (Aiter (Astar A1 A2 :: xs)) (Aiter (A1 :: A2 :: xs)).
Proof.
  intros A1 A2 xs. simpls.
  by rewrite star_assoc_r.
Qed.

Lemma sat_aiter_star_r :
  forall ph P s A1 A2 (xs : list Assn),
  sat ph P s (Aiter (A1 :: A2 :: xs)) ->
  sat ph P s (Aiter (Astar A1 A2 :: xs)).
Proof.
  intros ph P s A1 A2 xs SAT.
  simpl (Aiter (A1 :: A2 :: xs)) in SAT.
  by apply sat_star_assoc_l.
Qed.

Theorem aiter_star_r :
  forall A1 A2 xs,
  entails (Aiter (A1 :: A2 :: xs)) (Aiter (Astar A1 A2 :: xs)).
Proof.
  intros A1 A2 xs. simpls.
  by rewrite star_assoc_l.
Qed.

Lemma sat_aiter_weaken :
  forall ph P s A (xs : list Assn),
  sat ph P s (Aiter (A :: xs)) -> sat ph P s (Aiter xs).
Proof.
  intros ph P s A xs SAT.
  simpl (Aiter (A :: xs)) in SAT.
  apply sat_star_weaken with A.
  by apply sat_star_comm.
Qed.

Corollary aiter_weaken :
  forall A xs, entails (Aiter (A :: xs)) (Aiter xs).
Proof.
  intros A xs.
  rewrite aiter_cons_r.
  rewrite star_comm.
  by rewrite assn_weaken.
Qed.

(** *** Plain assertions *)

Theorem atrue_intro :
  forall A, entails A Atrue.
Proof.
  red. simpls.
Qed.

Theorem afalse_elim :
  forall A1 A2, entails A1 Afalse -> entails A1 A2.
Proof.
  unfold entails.
  intros A1 A2 H1 ph P s H2 H4.
  apply H1 in H4; vauto.
Qed.

Lemma aplain_tauto :
  forall E,
  entails (Aplain (Beq E E)) Atrue /\
  entails Atrue (Aplain (Beq E E)).
Proof.
  intros E. split.
  - red. ins.
  - red. ins. desf.
Qed.

(** Plain assertions can freely be duplicated. *)

Lemma aplain_dupl :
  forall B, entails (Aplain B) (Astar (Aplain B) (Aplain B)).
Proof.
  intros B. red. intros ph P s H3 H4. simpls.
  exists permheap_iden, ph. intuition.
  { apply permheap_add_iden_r. }
  exists Pepsilon, P. intuition.
  apply par_epsilon_l.
Qed.

(** *** Existential quantifiers *)

Theorem aexists_intro :
  forall A1 A2 x v,
  entails A1 (assn_subst x (Econst v) A2) ->
  entails A1 (Aexists x A2).
Proof.
  intros A1 A2 x v H ph P s H1 H2.
  exists v. by apply H.
Qed.

(** *** Disjunction *)

Lemma sat_adisj_elim_l :
  forall ph P s A1 A2, sat ph P s A1 -> sat ph P s (Adisj A1 A2).
Proof.
  intros ph p s A1 A2 SAT. simpl. by left.
Qed.

Lemma sat_adisj_elim_r :
  forall ph P s A1 A2, sat ph P s A2 -> sat ph P s (Adisj A1 A2).
Proof.
  intros ph P s A1 A2 SAT. simpl. by right.
Qed.

Theorem adisj_elim_l :
  forall A A1 A2, entails A A1 -> entails A (Adisj A1 A2).
Proof.
  intros A A1 A2 H ph P s H1 SAT.
  by apply sat_adisj_elim_l, H.
Qed.

Theorem adisj_elim_r :
  forall A A1 A2, entails A A2 -> entails A (Adisj A1 A2).
Proof.
  intros A A1 A2 H ph P s H1 SAT.
  by apply sat_adisj_elim_r, H.
Qed.

Lemma adisj_idemp :
  forall A, entails A (Adisj A A) /\ entails (Adisj A A) A.
Proof.
  intro A. split; ins; vauto. red. ins. desf.
Qed.

(** *** Magic wand *)

Theorem awand_intro :
  forall A1 A2 A3, entails (Astar A1 A2) A3 -> entails A1 (Awand A2 A3).
Proof.
  intros A1 A2 A3 H1 ph P s H2 H3 ph' P' H4 H5.
  apply H1; auto.
  exists ph, ph'. intuition.
  exists P, P'. intuition.
Qed.

Theorem awand_elim :
  forall A1 A2 A A',
  entails A1 (Awand A A') -> entails A2 A -> entails (Astar A1 A2) A'.
Proof.
  intros A1 A2 A A' H1 H2 ph P s H3 H4.
  simpls. desf. rewrite <- H5.
  apply H1; auto.
  { by apply permheap_disj_valid_l in H4. }
  apply H2; auto.
  by apply permheap_disj_valid_r in H4.
Qed.

(** *** Heap ownership *)

(** *** Process ownership *)

Theorem aproc_bisim :
  forall AP1 AP2, abisim AP1 AP2 -> entails (Aproc AP1) (Aproc AP2).
Proof.
  intros AP1 AP2 H ph P s H2 H3.
  unfold sat in *. destruct H3 as (P' & H3).
  exists P'. rewrite H3. by rewrite H.
Qed.

Theorem aproc_split :
  forall AP1 AP2,
  entails (Aproc (APpar AP1 AP2)) (Astar (Aproc AP1) (Aproc AP2)).
Proof.
  intros AP1 AP2 ph P s H1 (P' & H2). rewrite H2.
  exists permheap_iden, ph. intuition.
  { by apply permheap_add_iden_r. }
  exists (aproc_conv AP1 s), (Ppar (aproc_conv AP2 s) P').
  intuition vauto.
  - rewrite par_assoc. simpl. done.
  - exists Pepsilon. by rewrite par_epsilon_r.
Qed.

Theorem aproc_merge :
  forall AP1 AP2,
  entails (Astar (Aproc AP1) (Aproc AP2)) (Aproc (APpar AP1 AP2)).
Proof.
  intros AP1 AP2 ph P s H1 H2. unfold sat in H2.
  destruct H2 as (ph1 & ph2 & D1 & H2 & P1 & P2 & H3 & SAT1 & SAT2).
  destruct SAT1 as (P1' & H4). destruct SAT2 as (P2' & H5).
  exists (Ppar P1' P2'). intuition clarify.
  simpl (aproc_conv (APpar AP1 AP2) s). rewrite <- H3, H4, H5.
  repeat rewrite <- par_assoc.
  apply bisim_par; auto.
  repeat rewrite par_assoc.
  apply bisim_par; auto.
  by rewrite par_comm with (P := P1').
Qed.

Theorem aproc_weaken :
  forall AP1 AP2, entails (Aproc (APpar AP1 AP2)) (Aproc AP1).
Proof.
  intros AP1 AP2.
  transitivity (Astar (Aproc AP1) (Aproc AP2)).
  - by apply aproc_split.
  - apply assn_weaken.
Qed.

(** *** Process bisimulation *)

Theorem abisim_proc :
  forall AP AQ, entails (Astar (Aproc AP) (Abisim AP AQ)) (Aproc AQ).
Proof.
  intros AP AQ. red. intros ph P s H1 H2.
  destruct H2 as (ph1 & ph2 & D1 & H2 & P1 & P2 & H3 & SAT1 & SAT2).
  clarify. simpls. destruct SAT1 as (P1' & H4).
  exists (Ppar P1' P2). rewrite <- SAT2, <- H3.
  rewrite par_assoc. by rewrite <- H4.
Qed.

Theorem abisim_closed :
  forall AP AQ, abisim AP AQ -> entails (Atrue) (Abisim AP AQ).
Proof.
  intros AP AQ H1. red. intros ph P s H2 H3. simpls.
Qed.

Theorem abisim_cond_true :
  forall B AP, entails (Aplain B) (Abisim (APcond B AP) AP).
Proof.
  intros B AP. red. intros ph P s H1 H2. simpls.
  transitivity (Pcond (PBconst true) (aproc_conv AP s)).
  - apply bisim_cond_eval; vauto. simpls.
    by rewrite <- cond_conv_eval.
  - by apply pcond_true.
Qed.

Theorem abisim_cond_false :
  forall B AP, entails (Aplain (Bnot B)) (Abisim (APcond B AP) APdelta).
Proof.
  intros B AP. red. intros ph P s H1 H2. simpls.
  unfold negb in H2. desf. clear H2.
  transitivity (Pcond (PBconst false) (aproc_conv AP s)).
  - apply bisim_cond_eval; vauto. simpls.
    by rewrite <- cond_conv_eval.
  - by apply pcond_false.
Qed.

Theorem abisim_sigma_cond :
  forall x B AP,
  ~ In x (cond_fv B) ->
  entails (Atrue) (Abisim (APsigma x (APcond B AP)) (APcond B (APsigma x AP))).
Proof.
  intros x B AP H1. red. intros ph P s H2 _. simpls.
  set (f := fun v => aproc_conv (aproc_subst x (Econst v) AP) s).
  set (g := fun v => Pcond (cond_conv B s) (f v)).
  transitivity (Psum g).
  - subst g f. apply bisim_sum. red. intro v.
    rewrite cond_subst_pres; vauto.
  - subst g f. apply bisim_sum_cond.
Qed.

(** Likewise to [bisim], also [Abisim] resembles an equivalence relation and
    is a congruence for all connectives defined for [AbstrProc]. *)

Theorem abisim_refl :
  forall AP, entails Atrue (Abisim AP AP).
Proof.
  intros AP. red. intros ph P s H1 H2. simpls.
Qed.

Theorem abisim_symm :
  forall AP AQ, entails (Abisim AP AQ) (Abisim AQ AP).
Proof.
  intros AP AQ. red. intros ph P s H1 H2. simpls. auto.
Qed.

Theorem abisim_trans :
  forall AP AQ AR, entails (Astar (Abisim AP AQ) (Abisim AQ AR)) (Abisim AP AR).
Proof.
  intros AP AQ AR. red. intros ph P s H1 H2. simpls.
  destruct H2 as (ph1 & ph2 & H3 & H2 & P1 & P2 & H4 & SAT1 & SAT2).
  transitivity (aproc_conv AQ s); auto.
Qed.

Theorem abisim_seq :
  forall AP AP' AQ AQ',
  entails (Astar (Abisim AP AP') (Abisim AQ AQ')) (Abisim (APseq AP AQ) (APseq AP' AQ')).
Proof.
  intros AP AP' AQ AQ'. red. intros ph P s H1 H2. simpls.
  destruct H2 as (ph1 & ph2 & H3 & H2 & P1 & P2 & H4 & SAT1 & SAT2).
  apply bisim_seq; auto.
Qed.

Theorem abisim_alt :
  forall AP AP' AQ AQ',
  entails (Astar (Abisim AP AP') (Abisim AQ AQ')) (Abisim (APalt AP AQ) (APalt AP' AQ')).
Proof.
  intros AP AP' AQ AQ'. red. intros ph P s H1 H2. simpls.
  destruct H2 as (ph1 & ph2 & H3 & H2 & P1 & P2 & H4 & SAT1 & SAT2).
  apply bisim_alt; auto.
Qed.

Theorem abisim_par :
  forall AP AP' AQ AQ',
  entails (Astar (Abisim AP AP') (Abisim AQ AQ')) (Abisim (APpar AP AQ) (APpar AP' AQ')).
Proof.
  intros AP AP' AQ AQ'. red. intros ph P s H1 H2. simpls.
  destruct H2 as (ph1 & ph2 & H3 & H2 & P1 & P2 & H4 & SAT1 & SAT2).
  apply bisim_par; auto.
Qed.

Theorem abisim_sum :
  forall AP AQ x,
  ~ aproc_fv AP x ->
  ~ aproc_fv AQ x ->
  entails (Abisim AP AQ) (Abisim (APsigma x AP) (APsigma x AQ)).
Proof.
  intros AP AQ x H1 H2. red. intros ph P s H3 H4. simpls.
  apply bisim_sum. red. intro v.
  repeat rewrite aproc_subst_pres; auto.
Qed.

Theorem abisim_cond :
  forall AP AQ b,
  entails (Abisim AP AQ) (Abisim (APcond b AP) (APcond b AQ)).
Proof.
  intros AP AQ b. red. intros ph P s H3 H4. simpls.
  apply bisim_cond; auto.
Qed.

Theorem abisim_iter :
  forall AP AQ,
  entails (Abisim AP AQ) (Abisim (APiter AP) (APiter AQ)).
Proof.
  intros AP AQ. red. intros ph P s H3 H4. simpls.
  apply bisim_iter; auto.
Qed.

End Assertions.
