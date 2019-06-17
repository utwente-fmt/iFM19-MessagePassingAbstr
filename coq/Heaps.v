Require Import Equalities.
Require Import FunctionalExtensionality.
Require Import HahnBase.
Require Import List.
Require Import Permissions.
Require Import Prelude.
Require Import QArith.
Require Import Qcanon.
Require Import Utf8.
Require Import ZArith.

Import ListNotations.

(** * Heaps *)

Module Type Heaps(dom: Domains).
  Export dom.

(** ** Ordinary Heaps *)

Definition Heap := Val -> option Val.
Definition updateheap (h: Heap) l v := update val_eq_dec h l v.

(** *** Finiteness *)

(** A heap [h] is _finite_ if all [h]s occupied mappings can be projected onto a
    finite structure; in this case a list. *)

Definition heap_finite (h: Heap): Prop :=
  exists xs: list Val, forall l: Val, h l <> None -> In l xs.

Lemma heap_finite_free :
  forall h: Heap, heap_finite h -> exists l: Val, h l = None.
Proof.
  intros h (ls & FIN).
  assert (H: exists l: Val, ~ In l ls) by apply val_inf.
  destruct H as (l & H). specialize FIN with l. exists l. tauto.
Qed.

Lemma heap_finite_upd :
  forall h l v, heap_finite h -> heap_finite (updateheap h l v).
Proof.
  intros ph l val (xs & FIN).
  assert (H1: val = None \/ ~ val = None) by apply classic.
  destruct H1 as [H1 | H1].
  (* [val] is free *)
  - exists xs. intros l' H2. apply FIN.
    unfold updateheap, update in H2. desf.
  (* [val] is not free *)
  - exists (l :: xs). intros l' H2.
    specialize FIN with l'. simpls.
    unfold updateheap, update in H2.
    destruct (val_eq_dec l l') as [|H3]; vauto.
    right. by apply FIN.
Qed.

(** ** Permission Heaps *)

(** *** Heap cells *)

Inductive PermHeapCell :=
  | PHCfree
  | PHCcell(q: Qc)(v: Val)
  | PHCinv.

Add Search Blacklist "PermHeapCell_rect".
Add Search Blacklist "PermHeapCell_ind".
Add Search Blacklist "PermHeapCell_rec".

(** **** Validity *)

Definition phc_valid (c: PermHeapCell): Prop :=
  match c with
    | PHCfree => True
    | PHCcell q _ => perm_valid q
    | PHCinv => False
  end.

Lemma phc_valid_contra : forall c, phc_valid c -> c <> PHCinv.
Proof. intros c H. unfold phc_valid in H. desf. Qed.
Hint Resolve phc_valid_contra.

(** **** Disjointness *)

Definition phc_disj (c1 c2: PermHeapCell): Prop :=
  match c1, c2 with
    | PHCinv, _
    | _, PHCinv => False
    | PHCfree, PHCfree => True
    | PHCfree, c
    | c, PHCfree => phc_valid c
    | PHCcell q1 v1, PHCcell q2 v2 => perm_disj q1 q2 /\ v1 = v2
  end.

Instance phc_disj_symm : Symmetric phc_disj.
Proof. unfold phc_disj. red. ins; desf; simpls; intuition. Qed.
Hint Resolve phc_disj_symm.

Lemma phc_disj_iden_l : forall c, phc_valid c -> phc_disj c PHCfree.
Proof. ins. red. desf. Qed.
Lemma phc_disj_iden_r : forall c, phc_valid c -> phc_disj PHCfree c.
Proof. ins. desf. Qed.
Hint Resolve phc_disj_iden_l phc_disj_iden_r.

Lemma phc_disj_valid_l :
  forall c1 c2, phc_disj c1 c2 -> phc_valid c1.
Proof.
  unfold phc_disj, phc_valid.
  intros ?? H. desf. destruct H as (H1 & H2). vauto.
  apply perm_disj_valid in H1. desf.
Qed.
Lemma phc_disj_valid_r :
  forall c1 c2, phc_disj c1 c2 -> phc_valid c2.
Proof.
  intros ?? H. symmetry in H.
  by apply phc_disj_valid_l in H.
Qed.
Lemma phc_disj_valid :
  forall c1 c2,
  phc_disj c1 c2 -> phc_valid c1 /\ phc_valid c2.
Proof.
  intros c1 c2 H. split.
  - by apply phc_disj_valid_l in H.
  - by apply phc_disj_valid_r in H.
Qed.

(** **** Disjoint union *)

Definition phc_add (c1 c2: PermHeapCell): PermHeapCell :=
  match c1, c2 with
    | PHCinv, _
    | _, PHCinv => PHCinv
    | PHCfree, c
    | c, PHCfree => c
    | PHCcell q1 v1, PHCcell q2 v2 =>
        if val_eq_dec v1 v2 then PHCcell (q1 + q2) v1 else PHCinv
  end.

Lemma phc_add_assoc :
  forall c1 c2 c3,
  phc_add c1 (phc_add c2 c3) = phc_add (phc_add c1 c2) c3.
Proof.
  intros c1 c2 c3. unfold phc_add.
  destruct c1, c2, c3; simpls; desf.
  by rewrite Qcplus_assoc.
Qed.

Lemma phc_add_comm : forall c1 c2, phc_add c1 c2 = phc_add c2 c1.
Proof. unfold phc_add. ins. desf. by rewrite Qcplus_comm. Qed.
Hint Resolve phc_add_comm.

Lemma phc_add_valid :
  forall c1 c2, phc_disj c1 c2 -> phc_valid (phc_add c1 c2).
Proof.
  unfold phc_disj, phc_add, phc_valid.
  ins. repeat desf; by apply perm_add_valid.
Qed.

Lemma phc_add_iden_l : forall c, phc_add c PHCfree = c.
Proof. unfold phc_add. ins. desf. Qed.
Lemma phc_add_iden_r : forall c, phc_add PHCfree c = c.
Proof. unfold phc_add. ins. desf. Qed.
Hint Rewrite phc_add_iden_l phc_add_iden_r.

Lemma phc_disj_add_l :
  forall c1 c2 c3,
  phc_disj c1 c2 ->
  phc_disj (phc_add c1 c2) c3 ->
  phc_disj c2 c3.
Proof.
  intros ??? H1 H2.
  unfold phc_add, phc_disj in *.
  desf; simpls; intuition; vauto.
  - by apply perm_disj_valid_r in H.
  - by apply perm_disj_valid_r in H.
  - by apply perm_disj_add_l with q2.
Qed.

Lemma phc_disj_add_r :
  forall c1 c2 c3,
  phc_disj c2 c3 ->
  phc_disj c1 (phc_add c2 c3) ->
  phc_disj c1 c2.
Proof.
  intros c1 c2 c3 H1 H2.
  symmetry in H1, H2.
  rewrite phc_add_comm with c2 c3 in H2; auto.
  apply phc_disj_add_l in H2; auto.
Qed.

Lemma phc_disj_assoc_l :
  forall c1 c2 c3,
  phc_disj c1 c2 ->
  phc_disj (phc_add c1 c2) c3 ->
  phc_disj c1 (phc_add c2 c3).
Proof.
  unfold phc_disj, phc_add.
  intros c1 c2 c3 H1 H2.
  desf; simpls; intuition vauto; desf.
  - by apply perm_add_valid.
  - by apply perm_disj_assoc_l.
Qed.

Lemma phc_disj_assoc_r :
  forall c1 c2 c3,
  phc_disj c2 c3 ->
  phc_disj c1 (phc_add c2 c3) ->
  phc_disj (phc_add c1 c2) c3.
Proof.
  intros c1 c2 c3 H1 H2. symmetry in H1, H2.
  rewrite phc_add_comm in H2; auto.
  apply phc_disj_assoc_l in H2; auto.
  rewrite phc_add_comm in H2; auto.
Qed.

Lemma phc_disj_middle :
  forall c1 c2 c3 c4,
  phc_disj c1 c2 ->
  phc_disj c3 c4 ->
  phc_disj (phc_add c1 c2) (phc_add c3 c4) ->
  phc_disj c2 c3.
Proof.
  intros c1 c2 c3 c4 H1 H2 H3.
  apply phc_disj_add_l with c1; auto.
  by apply phc_disj_add_r with c4.
Qed.

Lemma phc_disj_compat :
  forall c1 c2 c3 c4,
  phc_disj c1 c3 ->
  phc_disj c2 c4 ->
  phc_disj (phc_add c1 c3) (phc_add c2 c4) ->
  phc_disj (phc_add c1 c2) (phc_add c3 c4).
Proof.
  intros c1 c2 c3 c4 H1 H2 H3.
  apply phc_disj_assoc_r.
  rewrite phc_add_comm.
  apply phc_disj_assoc_l; auto.
  symmetry. by apply phc_disj_add_l in H3.
  rewrite phc_add_comm.
  rewrite <- phc_add_assoc.
  apply phc_disj_assoc_l; auto.
  by rewrite phc_add_comm with c4 c2.
Qed.

Lemma phc_add_swap_l :
  forall c1 c2 c3,
  phc_add c1 (phc_add c2 c3) =
  phc_add c2 (phc_add c1 c3).
Proof.
  intros c1 c2 c3.
  rewrite phc_add_assoc.
  rewrite phc_add_comm with c1 c2.
  by rewrite phc_add_assoc.
Qed.

Lemma phc_add_swap_r :
  forall c1 c2 c3,
  phc_add (phc_add c1 c2) c3 =
  phc_add (phc_add c1 c3) c2.
Proof.
  intros c1 c2 c3.
  rewrite phc_add_comm.
  rewrite phc_add_swap_l.
  by rewrite phc_add_assoc.
Qed.

Lemma phc_add_compat :
  forall c1 c2 c3 c4,
  phc_add (phc_add c1 c3) (phc_add c2 c4) =
  phc_add (phc_add c1 c2) (phc_add c3 c4).
Proof.
  intros c1 c2 c3 c4. rewrite phc_add_swap_l.
  repeat rewrite phc_add_assoc.
  by rewrite phc_add_comm with c2 c1.
Qed.

Lemma phc_iden_split :
  forall c1 c2,
  phc_add c1 c2 = PHCfree ->
  c1 = PHCfree /\ c2 = PHCfree.
Proof.
  intros c1 c2 H. unfold phc_add in H. desf.
Qed.

Lemma phc_add_not_free :
  forall c1 c2,
  phc_add c1 c2 <> PHCfree <->
  c1 <> PHCfree \/ c2 <> PHCfree.
Proof.
  intros c1 c2. split; intro H.
  - unfold phc_add in H. desf; vauto.
  - unfold phc_add. desf; vauto.
Qed.

(** **** Less-than ordering *)

Definition phc_lt (c1 c2: PermHeapCell): Prop :=
  match c1, c2 with
    | PHCfree, PHCfree => False
    | PHCfree, _ => True
    | PHCcell q1 v1, PHCcell q2 v2 => q1 < q2 /\ v1 = v2
    | _, _ => False
  end.

Lemma phc_lt_irrefl :
  forall c, ~ phc_lt c c.
Proof.
  intros c H. unfold phc_lt in H.
  repeat desf. by apply Qclt_irrefl with q.
Qed.

Instance phc_lt_trans :
  Transitive phc_lt.
Proof.
  red. intros c1 c2 c3 H1 H2.
  unfold phc_lt in *.
  repeat desf; intuition vauto.
  by apply Qclt_trans with q1.
Qed.

Lemma phc_lt_asymm :
  forall c1 c2,
  phc_lt c1 c2 -> ~ phc_lt c2 c1.
Proof.
  intros c1 c2 H1 H2.
  assert (H3: phc_lt c1 c1) by (by transitivity c2).
  by apply phc_lt_irrefl in H3.
Qed.

Lemma phc_lt_mono_pos :
  forall c1 c2,
  phc_disj c1 c2 ->
  phc_lt PHCfree c2 ->
  phc_lt c1 (phc_add c1 c2).
Proof.
  intros c1 c2 H1 H2.
  unfold phc_disj, phc_valid in H1.
  unfold phc_lt in *. unfold phc_add.
  repeat desf; simpls; intuition vauto.
  apply Qclt_mono_pos. apply perm_disj_valid_r in H1. auto.
Qed.

Lemma phc_lt_mono_l :
  forall c1 c2 c3,
  phc_disj c3 c2 ->
  phc_lt c1 c2 ->
  phc_lt (phc_add c3 c1) (phc_add c3 c2).
Proof.
  intros c1 c2 c3 H1 H2. destruct c3; vauto.
  - by repeat rewrite phc_add_iden_r.
  - unfold phc_disj, phc_add, phc_lt in *.
    repeat desf; intuition.
    + apply Qclt_mono_pos.
      apply perm_disj_valid_r in H1. auto.
    + by apply Qcplus_lt_mono_l.
Qed.

Lemma phc_lt_mono_r :
  forall c1 c2 c3,
  phc_disj c2 c3 ->
  phc_lt c1 c2 ->
  phc_lt (phc_add c1 c3) (phc_add c2 c3).
Proof.
  intros c1 c2 c3 H1 H2.
  rewrite phc_add_comm with c1 c3.
  rewrite phc_add_comm with c2 c3.
  apply phc_lt_mono_l; auto.
Qed.

Lemma phc_lt_diff :
  forall c1 c2,
  phc_valid c1 ->
  phc_valid c2 ->
  phc_lt c1 c2 ->
  exists c3, phc_disj c1 c3 /\ phc_add c1 c3 = c2.
Proof.
  intros c1 c2 H1 H2 H3.
  unfold phc_valid in H1, H2.
  unfold phc_lt in H3. repeat desf; vauto.
  - exists (PHCcell q v). vauto.
  - apply perm_lt_diff in H3; auto.
    destruct H3 as (q' & H3 & H4); vauto.
    exists (PHCcell q' v0). intuition vauto.
    unfold phc_add. desf.
Qed.

Lemma phc_disj_lt :
  forall c1 c2 c3,
  phc_valid c1 ->
  phc_disj c2 c3 ->
  phc_lt c1 c2 ->
  phc_disj c1 c3.
Proof.
  intros c1 c2 c3 H1 H2 H3.
  generalize H2. intros H4.
  apply phc_disj_valid in H4.
  destruct H4 as (H4 & H5).
  unfold phc_lt in H3.
  unfold phc_disj, phc_valid in *.
  repeat desf; intuition vauto.
  by apply perm_disj_lt with q1.
Qed.

(** **** Less-than-or-equal-to ordering *)

Definition phc_leq (c1 c2 : PermHeapCell) : Prop :=
  match c1, c2 with
    | PHCfree, _ => True
    | PHCcell q1 v1, PHCcell q2 v2 => q1 <= q2 /\ v1 = v2
    | PHCinv, PHCinv => True
    | _, _ => False
  end.

Lemma phc_lt_leq_weak :
  forall c1 c2,
  phc_lt c1 c2 -> phc_leq c1 c2.
Proof.
  intros c1 c2 H.
  unfold phc_lt in H.
  unfold phc_leq. repeat desf; intuition vauto.
  by apply Qclt_le_weak.
Qed.

Instance phc_leq_refl :
  Reflexive phc_leq.
Proof.
  red. intro c. red.
  repeat desf; intuition vauto; by apply Qcle_refl.
Qed.
Hint Resolve phc_leq_refl.

Lemma phc_leq_lt_or_eq :
  forall c1 c2,
  phc_leq c1 c2 <->
  c1 = c2 \/ phc_lt c1 c2.
Proof.
  intros c1 c2. split; intro H.
  - unfold phc_leq in H. repeat desf; vauto.
    + destruct c2; vauto.
    + apply Qcle_lt_or_eq in H. desf; vauto.
  - destruct H as [H | H]; vauto.
    by apply phc_lt_leq_weak.
Qed.

Lemma phc_leq_antisym :
  forall c1 c2,
  phc_leq c1 c2 -> phc_leq c2 c1 -> c1 = c2.
Proof.
  intros c1 c2 H1 H2.
  apply phc_leq_lt_or_eq in H1.
  apply phc_leq_lt_or_eq in H2.
  destruct H1 as [H1 | H1], H2 as [H2 | H2]; vauto.
  by apply phc_lt_asymm in H1.
Qed.

Instance phc_leq_trans :
  Transitive phc_leq.
Proof.
  red. intros c1 c2 c3 H1 H2.
  apply phc_leq_lt_or_eq in H1.
  apply phc_leq_lt_or_eq in H2.
  destruct H1 as [H1 | H1], H2 as [H2 | H2]; vauto.
  - by apply phc_lt_leq_weak.
  - by apply phc_lt_leq_weak.
  - apply phc_lt_leq_weak.
    by transitivity c2.
Qed.

Lemma phc_leq_valid : forall c, phc_leq PHCfree c.
Proof. ins. Qed.

Lemma phc_leq_lt_trans :
  forall c1 c2 c3, phc_leq c1 c2 -> phc_lt c2 c3 -> phc_lt c1 c3.
Proof.
  intros c1 c2 c3 H1 H2.
  apply phc_leq_lt_or_eq in H1.
  destruct H1 as [H1 | H1]; vauto.
  by transitivity c2.
Qed.

Lemma phc_lt_leq_trans :
  forall c1 c2 c3, phc_lt c1 c2 -> phc_leq c2 c3 -> phc_lt c1 c3.
Proof.
  intros c1 c2 c3 H1 H2.
  apply phc_leq_lt_or_eq in H2.
  destruct H2 as [H2 | H2]; vauto.
  by transitivity c2.
Qed.

Lemma phc_lt_weaken :
  forall c1 c2 c3,
  phc_disj c2 c3 ->
  phc_lt c1 c2 ->
  phc_lt c1 (phc_add c2 c3).
Proof.
  intros c1 c2 c3 H1 H2.
  apply phc_lt_leq_trans with c2; auto.
  assert (H3: PHCfree = c3 \/ phc_lt PHCfree c3)
    by (apply phc_leq_lt_or_eq, phc_leq_valid).
  destruct H3 as [H3 | H3].
  - clarify. by rewrite phc_add_iden_l.
  - rewrite phc_leq_lt_or_eq. right.
    by apply phc_lt_mono_pos.
Qed.

Lemma phc_leq_weaken :
  forall c1 c2 c3,
  phc_disj c2 c3 -> phc_leq c1 c2 -> phc_leq c1 (phc_add c2 c3).
Proof.
  intros c1 c2 c3 H1 H2.
  apply phc_leq_lt_or_eq in H2.
  destruct H2 as [H2 | H2]; vauto.
  - assert (H2: PHCfree = c3 \/ phc_lt PHCfree c3)
      by (apply phc_leq_lt_or_eq, phc_leq_valid).
    destruct H2 as [H2 | H2].
    + clarify. by rewrite phc_add_iden_l.
    + apply phc_lt_leq_weak. by apply phc_lt_mono_pos.
  - by apply phc_lt_leq_weak, phc_lt_weaken.
Qed.

Lemma phc_leq_mono_l :
  forall c1 c2 c3,
  phc_disj c3 c2 -> phc_leq c1 c2 -> phc_leq (phc_add c3 c1) (phc_add c3 c2).
Proof.
  intros c1 c2 c3 H1 H2.
  apply phc_leq_lt_or_eq in H2.
  destruct H2 as [H2 | H2]; vauto.
  apply phc_lt_leq_weak.
  by apply phc_lt_mono_l.
Qed.

Lemma phc_leq_mono_r :
  forall c1 c2 c3,
  phc_disj c2 c3 -> phc_leq c1 c2 -> phc_leq (phc_add c1 c3) (phc_add c2 c3).
Proof.
  intros c1 c2 c3 H1 H2.
  rewrite phc_add_comm with c1 c3.
  rewrite phc_add_comm with c2 c3.
  apply phc_leq_mono_l; auto.
Qed.

Lemma phc_leq_mono_pos :
  forall c1 c2, phc_disj c1 c2 -> phc_leq c1 (phc_add c1 c2).
Proof.
  intros c1 c2 H1. transitivity (phc_add c1 PHCfree).
  - by rewrite phc_add_iden_l.
  - apply phc_leq_mono_l; vauto.
Qed.

Lemma phc_leq_compat :
  forall c1 c2 c3 c4,
  phc_disj c1 c4 ->
  phc_disj c3 c4 ->
  phc_leq c1 c3 ->
  phc_leq c2 c4 ->
  phc_leq (phc_add c1 c2) (phc_add c3 c4).
Proof.
  intros c1 c2 c3 c4.
  transitivity (phc_add c1 c4).
  apply phc_leq_mono_l; auto.
  apply phc_leq_mono_r; auto.
Qed.

Lemma phc_leq_diff :
  forall c1 c2,
  phc_valid c1 ->
  phc_valid c2 ->
  phc_leq c1 c2 ->
  exists c3, phc_disj c1 c3 /\ phc_add c1 c3 = c2.
Proof.
  intros c1 c2 H1 H2 H3.
  apply phc_leq_lt_or_eq in H3.
  destruct H3 as [H3 | H3]; clarify.
  - exists PHCfree. split.
    + by apply phc_disj_iden_l.
    + by rewrite phc_add_iden_l.
  - apply phc_lt_diff in H3; auto.
Qed.

Lemma phc_disj_leq :
  forall c1 c2 c3,
  phc_valid c1 ->
  phc_disj c2 c3 ->
  phc_leq c1 c2 ->
  phc_disj c1 c3.
Proof.
  intros c1 c2 c3 H1 H2 H3.
  apply phc_leq_lt_or_eq in H3.
  destruct H3 as [H3 | H3]; vauto.
  by apply phc_disj_lt with c2.
Qed.

(** **** Concretisation *)

Definition phc_concr (c: PermHeapCell): option Val :=
  match c with
    | PHCfree
    | PHCinv => None
    | PHCcell _ v => Some v
  end.

Lemma phc_concr_lt_none :
  forall c1 c2,
  phc_lt c1 c2 -> phc_concr c2 = None -> phc_concr c1 = None.
Proof.
  intros c1 c2 H1 H2.
  unfold phc_concr in *. desf.
Qed.

Lemma phc_concr_leq_none :
  forall c1 c2,
  phc_leq c1 c2 -> phc_concr c2 = None -> phc_concr c1 = None.
Proof.
  intros c1 c2 H1 H2.
  apply phc_leq_lt_or_eq in H1.
  destruct H1 as [H1 | H1]; vauto.
  by apply phc_concr_lt_none in H1.
Qed.

Lemma phc_concr_lt_some :
  forall c1 c2 v,
  phc_lt c1 c2 ->
  phc_concr c1 = Some v ->
  phc_concr c2 = Some v.
Proof.
  intros c1 c2 v H1 H2.
  unfold phc_concr in *.
  desf; simpls; desf.
Qed.

Lemma phc_concr_leq_some :
  forall c1 c2 v,
  phc_leq c1 c2 -> phc_concr c1 = Some v -> phc_concr c2 = Some v.
Proof.
  intros c1 c2 v H1 H2.
  apply phc_leq_lt_or_eq in H1.
  destruct H1 as [H1 | H1]; vauto.
  by apply phc_concr_lt_some with (v := v) in H1.
Qed.

Lemma phc_concr_none_free :
  forall c,
  phc_valid c -> phc_concr c = None -> c = PHCfree.
Proof.
  intros c H1 H2. unfold phc_valid in H1.
  unfold phc_concr in H2. desf.
Qed.

Lemma phc_concr_add :
  forall c1 c2 v,
  phc_disj c1 c2 ->
  phc_concr c1 = Some v ->
  phc_concr (phc_add c1 c2) = Some v.
Proof.
  intros c1 c2 v H1 H2.
  apply phc_concr_leq_some with c1; vauto.
  by apply phc_leq_mono_pos.
Qed.

Lemma phc_concr_compat :
  forall c1 c2 c3 c4,
  phc_disj c1 c2 ->
  phc_disj c3 c4 ->
  phc_concr c1 = phc_concr c3 ->
  phc_concr c2 = phc_concr c4 ->
  phc_concr (phc_add c1 c2) = phc_concr (phc_add c3 c4).
Proof.
  intros c1 c2 c3 c4 D1 D2 H1 H2.
  unfold phc_disj, phc_add in *. repeat desf; vauto.
Qed.

Lemma phc_concr_disj_add_l :
  forall c1 c2 c3,
  phc_disj c1 c3 ->
  phc_disj c2 c3 ->
  phc_concr c1 = phc_concr c2 ->
  phc_concr (phc_add c1 c3) = phc_concr (phc_add c2 c3).
Proof.
  intros c1 c2 c3 H1 H2 H3.
  apply phc_concr_compat; vauto.
Qed.

Lemma phc_concr_disj_add_r :
  forall c1 c2 c3,
  phc_disj c1 c3 ->
  phc_disj c2 c3 ->
  phc_concr c1 = phc_concr c2 ->
  phc_concr (phc_add c3 c1) = phc_concr (phc_add c3 c2).
Proof.
  intros c1 c2 c3 H1 H2 H3.
  rewrite phc_add_comm with c3 c1.
  rewrite phc_add_comm with c3 c2.
  apply phc_concr_disj_add_l; auto.
Qed.

(** *** Permission heaps *)

Definition PermHeap := Val -> PermHeapCell.
Definition permheap_iden: PermHeap := fun _ => PHCfree.
Definition update_permheap (h: PermHeap) l c := update val_eq_dec h l c.

(** **** Validity *)

Definition permheap_valid (ph: PermHeap): Prop :=
  forall l: Val, phc_valid (ph l).

Lemma permheap_valid_iden : permheap_valid permheap_iden.
Proof. red. ins. Qed.
Hint Resolve permheap_valid_iden.

Lemma permheap_valid_upd :
  forall ph c l,
  permheap_valid ph ->
  phc_valid c ->
  permheap_valid (update_permheap ph l c).
Proof.
  intros ??????. unfold update_permheap, update. desf.
Qed.

(** **** Disjointness *)

Definition permheap_disj (ph1 ph2: PermHeap): Prop :=
  forall l: Val, phc_disj (ph1 l) (ph2 l).

Instance permheap_disj_symm : Symmetric permheap_disj.
Proof. intros ????. by symmetry. Qed.
Hint Resolve permheap_disj_symm.

Lemma permheap_disj_valid_l :
  forall ph1 ph2, permheap_disj ph1 ph2 -> permheap_valid ph1.
Proof.
  intros ? ph ? l.
  by apply phc_disj_valid_l with (ph l).
Qed.

Lemma permheap_disj_valid_r :
  forall ph1 ph2, permheap_disj ph1 ph2 -> permheap_valid ph2.
Proof.
  intros ph ?? l.
  by apply phc_disj_valid_r with (ph l).
Qed.

Lemma permheap_disj_valid :
  forall ph1 ph2,
  permheap_disj ph1 ph2 -> permheap_valid ph1 /\ permheap_valid ph2.
Proof.
  intros ph1 ph2 H. intuition.
  by apply permheap_disj_valid_l with ph2.
  by apply permheap_disj_valid_r with ph1.
Qed.

Lemma permheap_disj_iden_l :
  forall ph, permheap_valid ph -> permheap_disj ph permheap_iden.
Proof.
  unfold permheap_valid, permheap_iden.
  intros ???. by apply phc_disj_iden_l.
Qed.
Lemma permheap_disj_iden_r :
  forall ph, permheap_valid ph -> permheap_disj permheap_iden ph.
Proof.
  unfold permheap_valid, permheap_iden.
  intros ???. by apply phc_disj_iden_r.
Qed.

Hint Resolve permheap_disj_iden_l permheap_disj_iden_r.

Lemma permheap_disj_upd :
  forall ph1 ph2 c1 c2 l,
  phc_disj c1 c2 ->
  permheap_disj ph1 ph2 ->
  permheap_disj (update_permheap ph1 l c1) (update_permheap ph2 l c2).
Proof.
  unfold permheap_disj, update_permheap, update.
  intros ????????. desf.
Qed.

(** **** Addition *)

Definition permheap_add (ph1 ph2: PermHeap): PermHeap :=
  fun l => phc_add (ph1 l) (ph2 l).

Lemma permheap_add_iden_l :
  forall ph, permheap_add ph permheap_iden = ph.
Proof.
  intro ph. extensionality l.
  unfold permheap_add, permheap_iden.
  apply phc_add_iden_l.
Qed.

Lemma permheap_add_iden_r :
  forall ph, permheap_add permheap_iden ph = ph.
Proof.
  intro ph. extensionality l.
  unfold permheap_add, permheap_iden.
  apply phc_add_iden_r.
Qed.

Hint Rewrite permheap_add_iden_l permheap_add_iden_r.

Lemma permheap_add_assoc :
  forall ph1 ph2 ph3,
  permheap_add (permheap_add ph1 ph2) ph3 =
  permheap_add ph1 (permheap_add ph2 ph3).
Proof.
  intros ???. extensionality l.
  unfold permheap_add.
  by rewrite phc_add_assoc.
Qed.

Lemma permheap_add_comm :
  forall ph1 ph2,
  permheap_add ph1 ph2 = permheap_add ph2 ph1.
Proof.
  intros ??. extensionality l.
  by apply phc_add_comm.
Qed.

Lemma permheap_add_valid :
  forall ph1 ph2,
  permheap_disj ph1 ph2 -> permheap_valid (permheap_add ph1 ph2).
Proof.
  unfold permheap_add. intros ????.
  by apply phc_add_valid.
Qed.

Hint Resolve permheap_add_valid.

Lemma permheap_disj_add_l :
  forall ph1 ph2 ph3,
  permheap_disj ph1 ph2 ->
  permheap_disj (permheap_add ph1 ph2) ph3 ->
  permheap_disj ph2 ph3.
Proof.
  intros ph1 ph2 ph3 H1 H2 l.
  apply phc_disj_add_l with (ph1 l); auto.
  by apply H2.
Qed.

Lemma permheap_disj_add_r :
  forall ph1 ph2 ph3,
  permheap_disj ph2 ph3 ->
  permheap_disj ph1 (permheap_add ph2 ph3) ->
  permheap_disj ph1 ph2.
Proof.
  intros ph1 ph2 ph3 H1 H2 l.
  apply phc_disj_add_r with (ph3 l); auto.
  by apply H2.
Qed.

Lemma permheap_disj_assoc_l :
  forall ph1 ph2 ph3,
  permheap_disj ph1 ph2 ->
  permheap_disj (permheap_add ph1 ph2) ph3 ->
  permheap_disj ph1 (permheap_add ph2 ph3).
Proof.
  intros ???? H ?.
  apply phc_disj_assoc_l. auto. apply H.
Qed.

Lemma permheap_disj_assoc_r :
  forall ph1 ph2 ph3,
  permheap_disj ph2 ph3 ->
  permheap_disj ph1 (permheap_add ph2 ph3) ->
  permheap_disj (permheap_add ph1 ph2) ph3.
Proof.
  intros ???? H ?.
  apply phc_disj_assoc_r. auto. apply H.
Qed.

Lemma permheap_add_upd :
  forall ph1 ph2 c1 c2 l,
  update_permheap (permheap_add ph1 ph2) l (phc_add c1 c2) =
  permheap_add (update_permheap ph1 l c1) (update_permheap ph2 l c2).
Proof.
  ins. extensionality l'.
  unfold permheap_add, update_permheap, update. desf.
Qed.

Lemma permheap_add_cell :
  forall ph1 ph2 l, phc_add (ph1 l) (ph2 l) = permheap_add ph1 ph2 l.
Proof. ins. Qed.

Lemma permheap_disj_middle :
  forall ph1 ph2 ph3 ph4,
  permheap_disj ph1 ph2 ->
  permheap_disj ph3 ph4 ->
  permheap_disj (permheap_add ph1 ph2) (permheap_add ph3 ph4) ->
  permheap_disj ph2 ph3.
Proof.
  intros ph1 ph2 ph3 ph4 H1 H2 H3.
  apply permheap_disj_add_l with ph1; auto.
  by apply permheap_disj_add_r with ph4.
Qed.

Lemma permheap_disj_compat :
  forall ph1 ph2 ph3 ph4,
  permheap_disj ph1 ph3 ->
  permheap_disj ph2 ph4 ->
  permheap_disj (permheap_add ph1 ph3) (permheap_add ph2 ph4) ->
  permheap_disj (permheap_add ph1 ph2) (permheap_add ph3 ph4).
Proof.
  intros ph1 ph2 ph3 ph4 H1 H2 H3.
  apply permheap_disj_assoc_r.
  rewrite permheap_add_comm.
  apply permheap_disj_assoc_l; auto.
  symmetry. by apply permheap_disj_add_l in H3.
  rewrite permheap_add_comm.
  rewrite permheap_add_assoc.
  apply permheap_disj_assoc_l; auto.
  by rewrite permheap_add_comm with ph4 ph2.
Qed.

Lemma permheap_add_swap_l :
  forall ph1 ph2 ph3,
  permheap_add ph1 (permheap_add ph2 ph3) =
  permheap_add ph2 (permheap_add ph1 ph3).
Proof.
  intros ph1 ph2 ph3.
  rewrite <- permheap_add_assoc.
  rewrite permheap_add_comm with ph1 ph2.
  by rewrite permheap_add_assoc.
Qed.

Lemma permheap_add_swap_r :
  forall ph1 ph2 ph3,
  permheap_add (permheap_add ph1 ph2) ph3 =
  permheap_add (permheap_add ph1 ph3) ph2.
Proof.
  intros ph1 ph2 ph3.
  rewrite permheap_add_comm.
  rewrite permheap_add_swap_l.
  by rewrite permheap_add_assoc.
Qed.

Lemma permheap_add_compat :
  forall ph1 ph2 ph3 ph4,
  permheap_add (permheap_add ph1 ph3) (permheap_add ph2 ph4) =
  permheap_add (permheap_add ph1 ph2) (permheap_add ph3 ph4).
Proof.
  intros ph1 ph2 ph3 ph4.
  rewrite permheap_add_swap_l.
  repeat rewrite <- permheap_add_assoc.
  by rewrite permheap_add_comm with ph2 ph1.
Qed.

Lemma permheap_add_upd_free :
  forall ph1 ph2 c l,
  ph2 l = PHCfree ->
  permheap_add (update_permheap ph1 l c) ph2 =
  update_permheap (permheap_add ph1 ph2) l c.
Proof.
  intros ph1 ph2 phc l H1.
  extensionality l'.
  unfold update_permheap, update, permheap_add. desf.
  by rewrite H1, phc_add_iden_l.
Qed.

(** **** Concretisation *)

Definition permheap_concr (ph: PermHeap): Heap :=
  fun l => phc_concr (ph l).

Lemma permheap_concr_upd :
  forall ph l c,
  permheap_concr (update_permheap ph l c) =
  updateheap (permheap_concr ph) l (phc_concr c).
Proof.
  intros ph l c. extensionality l'.
  unfold permheap_concr, updateheap, update_permheap, update. desf.
Qed.

Lemma permheap_concr_disj_add_l :
  forall ph1 ph2 ph3,
  permheap_disj ph1 ph3 ->
  permheap_disj ph2 ph3 ->
  permheap_concr ph1 = permheap_concr ph2 ->
  permheap_concr (permheap_add ph1 ph3) = permheap_concr (permheap_add ph2 ph3).
Proof.
  intros ph1 ph2 ph3 H1 H2 H3.
  extensionality l. unfold permheap_concr.
  repeat rewrite <- permheap_add_cell.
  apply phc_concr_disj_add_l; vauto.
  by apply equal_f with l in H3.
Qed.

Lemma permheap_concr_disj_add_r :
  forall ph1 ph2 ph3,
  permheap_disj ph1 ph3 ->
  permheap_disj ph2 ph3 ->
  permheap_concr ph1 = permheap_concr ph2 ->
  permheap_concr (permheap_add ph3 ph1) = permheap_concr (permheap_add ph3 ph2).
Proof.
  intros ph1 ph2 ph3 H1 H2 H3.
  rewrite permheap_add_comm with ph3 ph1.
  rewrite permheap_add_comm with ph3 ph2.
  apply permheap_concr_disj_add_l; auto.
Qed.

(** **** Finiteness *)

Definition permheap_finite (ph: PermHeap): Prop :=
  exists xs, forall l, ph l <> PHCfree -> In l xs.

Lemma permheap_finite_free :
  forall ph, permheap_finite ph -> exists l, ph l = PHCfree.
Proof.
  intros ph (xs & FIN).
  assert (H: exists l, ~ In l xs) by apply val_inf.
  destruct H as (l & H). specialize FIN with l.
  exists l. tauto.
Qed.

Lemma permheap_finite_upd :
  forall ph l c,
  permheap_finite ph ->
  permheap_finite (update_permheap ph l c).
Proof.
  intros ph l c (xs & FIN).
  assert (H1 : c = PHCfree \/ ~ c = PHCfree) by apply classic.
  destruct H1 as [H1 | H1].
  - exists xs. intros l' H2. apply FIN.
    unfold update_permheap, update in H2. desf.
  - exists (l :: xs). intros l' H2.
    specialize FIN with l'. simpls.
    unfold update_permheap, update in H2.
    destruct (val_eq_dec l l') as [|H3]; vauto.
    right. by apply FIN.
Qed.

Lemma permheap_finite_add :
  forall ph1 ph2,
  permheap_finite (permheap_add ph1 ph2) <->
  permheap_finite ph1 /\ permheap_finite ph2.
Proof.
  intros ph1 ph2. split.
  - intros (xs & FIN).
    unfold permheap_finite. split.
    + exists xs. intros l H1.
      apply FIN. intro H2.
      apply phc_add_not_free in H2; vauto.
    + exists xs. intros l H1.
      apply FIN. intro H2.
      apply phc_add_not_free in H2; vauto.
  - intro FIN.
    destruct FIN as ((xs1 & FIN1) & (xs2 & FIN2)).
    unfold permheap_finite.
    exists (xs1 ++ xs2). intros l H1.
    apply in_or_app.
    unfold permheap_add in H1.
    apply phc_add_not_free in H1.
    destruct H1 as [H1 | H1].
    + left. by apply FIN1.
    + right. by apply FIN2.
Qed.

Lemma permheap_finite_concr :
  forall ph,
  permheap_valid ph ->
  permheap_finite ph <->
  heap_finite (permheap_concr ph).
Proof.
  intros ph H1. split.
  - intros (xs & FIN).
    exists xs. intros l H2. apply FIN.
    unfold permheap_concr, phc_concr in H2. desf.
  - intros (xs & FIN).
    exists xs. intros l H2. apply FIN.
    unfold permheap_valid in H1.
    specialize H1 with l.
    unfold phc_valid in H1.
    unfold permheap_concr, phc_concr. desf.
Qed.

End Heaps.
