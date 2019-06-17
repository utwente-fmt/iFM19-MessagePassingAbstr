Require Import HahnBase.
Require Import Prelude.
Require Import QArith.
Require Import Qcanon.
Require Import Utf8.

Open Scope Qc_scope.

(** * Permissions *)

(** ** Prerequisites *)

Lemma Q2Qc_correct :
  forall q : Q, Q2Qc q == q.
Proof.
  intros. apply Qred_correct.
Qed.

Lemma Qcplus_lt_compat :
  forall x y z t : Qc,
  x < y -> z < t -> x + z < y + t.
Proof.
  ins. unfold Qcplus, Qclt.
  repeat rewrite Q2Qc_correct.
  apply Qplus_lt_le_compat. easy.
  now apply Qlt_le_weak.
Qed.

Lemma Qcplus_le_mono_l :
  forall x y z : Qc, x <= y <-> z + x <= z + y.
Proof.
  split; intros.
  - apply Qcplus_le_compat. apply Qcle_refl. exact H.
  - replace x with ((0 - z) + (z + x)) by ring.
    replace y with ((0 - z) + (z + y)) by ring.
    apply Qcplus_le_compat; intuition. apply Qcle_refl.
Qed.

Lemma Qcplus_le_mono_r :
  forall x y z : Qc, x <= y <-> x + z <= y + z.
Proof.
  ins. intuition.
  rewrite Qcplus_comm with x z.
  rewrite Qcplus_comm with y z.
  by apply Qcplus_le_mono_l.
  apply Qcplus_le_mono_l with z.
  rewrite Qcplus_comm with z x.
  by rewrite Qcplus_comm with z y.
Qed.

Lemma Qclt_nge :
  forall x y : Qc, x < y <-> ~ y <= x.
Proof.
  split; auto using Qclt_not_le, Qcnot_le_lt.
Qed.

Lemma Qclt_irrefl :
  forall q : Qc, ~ q < q.
Proof.
  ins. apply Qcle_not_lt, Qcle_refl.
Qed.

Lemma Qclt_asymm :
  forall q1 q2 : Qc,
  q1 < q2 -> ~ q2 < q1.
Proof.
  intros q1 q2 H1 H2.
  assert (q1 < q1). { by apply Qclt_trans with q2. }
  by apply Qclt_irrefl with q1.
Qed.

Lemma Qcplus_lt_mono_l :
  forall x y z : Qc, x < y <-> z + x < z + y.
Proof.
  ins. rewrite !Qclt_nge.
  by rewrite <- Qcplus_le_mono_l.
Qed.

Lemma Qcplus_lt_mono_r :
  forall x y z : Qc, x < y <-> x + z < y + z.
Proof.
  ins. rewrite !Qclt_nge.
  by rewrite <- Qcplus_le_mono_r.
Qed.

Lemma Qcplus_lt_compat_le_l :
  forall x y z t : Qc,
  x <= y -> z < t -> x + z < y + t.
Proof.
  intros x y z t H1 H2.
  apply Qcle_lt_or_eq in H1.
  destruct H1 as [H1 | H1].
  - by apply Qcplus_lt_compat.
  - clarify. by apply Qcplus_lt_mono_l.
Qed.

Lemma Qcplus_lt_compat_le_r :
  forall x y z t : Qc,
  x < y -> z <= t -> x + z < y + t.
Proof.
  intros x y z t H1 H2.
  apply Qcle_lt_or_eq in H2.
  destruct H2 as [H2 | H2].
  - by apply Qcplus_lt_compat.
  - clarify. by apply Qcplus_lt_mono_r.
Qed.

Lemma Qcplus_pos_nonneg :
  forall p q : Qc, 0 < p -> 0 <= q -> 0 < p + q.
Proof.
  intros p q Hp Hq.
  apply Qclt_le_trans with (p + 0).
  by rewrite Qcplus_0_r.
  by apply Qcplus_le_mono_l.
Qed.

Lemma Qcplus_swap_l :
  forall q1 q2 q3 : Qc, q1 + (q2 + q3) = q2 + (q1 + q3).
Proof.
  intros q1 q2 q3.
  rewrite Qcplus_comm, <- Qcplus_assoc.
  by rewrite Qcplus_comm with q1 q3.
Qed.

Lemma Qcplus_swap_r :
  forall q1 q2 q3 : Qc, q1 + (q2 + q3) = q3 + (q2 + q1).
Proof.
  ins. rewrite Qcplus_comm.
  rewrite <- Qcplus_assoc.
  apply Qcplus_swap_l.
Qed.

Lemma Qcplus_pos_le_elim :
  forall q1 q2 q : Qc, q1 + q2 <= q -> 0 <= q2 -> q1 <= q.
Proof.
  intros q1 q2 q H1 H2.
  replace q1 with (q1 + 0).
  apply Qcle_trans with (q1 + q2); auto.
  by rewrite <- Qcplus_le_mono_l.
  apply Qcplus_0_r.
Qed.

Lemma Qcplus_pos_lt_elim :
  forall q1 q2 q : Qc, q1 + q2 < q -> 0 <= q2 -> q1 < q.
Proof.
  intros q1 q2 q H1 H2.
  replace q1 with (q1 + 0).
  apply Qcle_lt_trans with (q1 + q2); auto.
  by rewrite <- Qcplus_le_mono_l.
  apply Qcplus_0_r.
Qed.

Lemma Qcplus_le_weaken :
  forall q1 q2 q : Qc, 0 < q -> q1 <= q2 -> q1 <= q2 + q.
Proof.
  intros q1 q2 q H1 H2.
  rewrite Qcplus_comm.
  replace q1 with (0 + q1).
  apply Qcplus_le_compat; auto.
  by apply Qclt_le_weak in H1.
  apply Qcplus_0_l.
Qed.

Lemma Qcplus_lt_weaken :
  forall q1 q2 q : Qc,
  0 < q -> q1 <= q2 -> q1 < q2 + q.
Proof.
  intros q1 q2 q H1 H2.
  apply Qcle_lt_or_eq in H2.
  destruct H2 as [H2 | H2].
  (* [q1] is less than [q2] *)
  - rewrite Qcplus_comm.
    replace q1 with (0 + q1).
    apply Qcplus_lt_compat; auto.
    apply Qcplus_0_l.
  (* [q1] is equal to [q2] *)
  - clarify.
    apply Qclt_minus_iff.
    rewrite <- Qcplus_assoc.
    rewrite Qcplus_comm.
    rewrite <- Qcplus_assoc.
    rewrite Qcplus_comm with (- q2) q2.
    by rewrite Qcplus_opp_r, Qcplus_0_r.
Qed.

Lemma Qcle_diff :
  forall q1 q2 : Qc, q1 <= q2 -> exists q, q2 = q1 + q.
Proof.
  intros q1 q2 H.
  apply Qcle_minus_iff in H.
  exists (q2 + (- q1)).
  rewrite Qcplus_comm.
  rewrite <- Qcplus_assoc.
  rewrite Qcplus_comm with (-q1) q1.
  rewrite Qcplus_opp_r.
  by rewrite Qcplus_0_r.
Qed.

Lemma Qclt_diff :
  forall q1 q2 : Qc, q1 < q2 -> exists q, q2 = q + q1.
Proof.
  intros q1 q2 H.
  apply Qclt_minus_iff in H.
  exists (q2 + (- q1)).
  rewrite <- Qcplus_assoc.
  rewrite Qcplus_comm with (-q1) q1.
  rewrite Qcplus_opp_r.
  by rewrite Qcplus_0_r.
Qed.

Lemma Qclt_mono_pos :
  forall q1 q2 : Qc, 0 < q1 -> q2 < q2 + q1.
Proof.
  intros q1 q2 H.
  replace (q2 < q2 + q1) with (q2 + 0 < q2 + q1).
  by apply Qcplus_lt_mono_l.
  by rewrite Qcplus_0_r.
Qed.

Lemma Qcle_plus_elim :
  forall q1 q2 q3 : Qc, 0 <= q1 -> 0 <= q2 -> q1 + q2 <= q3 -> q1 <= q3.
Proof.
  intros q1 q2 q3 H1 H2 H3.
  apply Qcle_trans with (q1 + q2); auto.
  replace (q1 <= q1 + q2) with (q1 + 0 <= q1 + q2).
  by apply Qcplus_le_mono_l.
  by rewrite Qcplus_0_r.
Qed.

Lemma Qcle_weaken :
  forall q1 q2 : Qc, q1 = q2 -> q1 <= q2.
Proof.
  intros ?? H. rewrite H.
  apply Qcle_refl.
Qed.

Lemma Qcplus_canc_l :
  forall q1 q2 q : Qc, q + q1 = q + q2 -> q1 = q2.
Proof.
  intros q1 q2 q H.
  apply Qcle_antisym.
  apply Qcplus_le_mono_l with q.
  by apply Qcle_weaken.
  apply Qcplus_le_mono_l with q.
  by apply Qcle_weaken.
Qed.

Lemma Qcplus_canc_r :
  forall q1 q2 q : Qc, q1 + q = q2 + q -> q1 = q2.
Proof.
  intros q1 q2 q H.
  apply Qcplus_canc_l with q.
  rewrite Qcplus_comm with q q1.
  by rewrite Qcplus_comm with q q2.
Qed.

Lemma Qcplus_neg_dist :
  forall q1 q2 : Qc, -(q1 + q2) = (-q1) + (-q2).
Proof.
  intros q1 q2.
  apply Qcplus_canc_r with (q1 + q2).
  rewrite Qcplus_comm.
  rewrite Qcplus_opp_r.
  rewrite Qcplus_comm with q1 q2.
  rewrite <- Qcplus_assoc.
  rewrite Qcplus_comm.
  repeat rewrite <- Qcplus_assoc.
  rewrite Qcplus_opp_r.
  rewrite Qcplus_0_r.
  rewrite <- Qcplus_comm.
  rewrite Qcplus_opp_r.
  reflexivity.
Qed.

Lemma Qcplus_pos_le :
  forall q1 q2 : Qc, 0 < q2 -> q1 <= q1 + q2.
Proof.
  intros q1 q2 H.
  rewrite <- Qcplus_0_r with q1.
  rewrite <- Qcplus_assoc.
  rewrite <- Qcplus_le_mono_l.
  rewrite Qcplus_0_l.
  by apply Qclt_le_weak.
Qed.

(** ** Fractional permissions *)

(** Fractional permissions are rational numbers in the range (0..1]. *)

Definition perm_full := 1%Qc.

(** *** Validity *)

(** The predicate [perm_valid] determines whether a rational number is a
    fractional permission (i.e. is within the proper range). *)

Definition perm_valid (q : Qc) : Prop :=
  0 < q /\ q <= 1.

Lemma perm_valid_mono :
  forall q1 q2 : Qc,
  perm_valid q1 -> q2 < q1 + q2.
Proof.
  intros q1 q2 H.
  unfold perm_valid in H. intuition.
  replace q2 with (0 + q2) at 1.
  by rewrite <- Qcplus_lt_mono_r.
  by rewrite Qcplus_0_l.
Qed.

Lemma perm_valid_pos :
  forall q : Qc, perm_valid q -> 0 < q.
Proof.
  unfold perm_valid. ins. desf.
Qed.

Hint Resolve perm_valid_pos.

Lemma perm_valid_full_neg :
  forall q : Qc,
  perm_valid q -> ~ perm_full < q.
Proof.
  intros q H1 H2.
  unfold perm_valid in H1.
  destruct H1 as (H1 & H3).
  unfold perm_full in H2.
  apply Qcle_lt_or_eq in H3.
  destruct H3 as [H3 | H3]; vauto.
  by apply Qclt_asymm in H2.
Qed.

Lemma perm_valid_full :
  forall q : Qc,
  perm_valid q ->
  perm_full <= q ->
  q = perm_full.
Proof.
  intros q H1 H2.
  apply Qcle_lt_or_eq in H2.
  destruct H2 as [H2 | H2]; auto.
  by apply perm_valid_full_neg in H2.
Qed.

(** *** Disjointness *)

(** Two permissions are _disjoint_ if they are both positive and their sum does not exceed 1. *)

Definition perm_disj (q1 q2 : Qc) : Prop :=
  0 < q1 /\ 0 < q2 /\ q1 + q2 <= 1.

Instance perm_disj_symm :
  Symmetric perm_disj.
Proof.
  unfold perm_disj. red. intuition.
  by rewrite Qcplus_comm.
Qed.

Hint Resolve perm_disj_symm.

Lemma perm_disj_valid_l :
  forall q1 q2 : Qc, perm_disj q1 q2 -> perm_valid q1.
Proof.
  unfold perm_disj, perm_valid. intuition.
  apply Qcplus_pos_le_elim in H2. auto.
  by apply Qclt_le_weak in H.
Qed.

Lemma perm_disj_valid_r :
  forall q1 q2 : Qc, perm_disj q1 q2 -> perm_valid q2.
Proof.
  intros ?? H. symmetry in H.
  by apply perm_disj_valid_l in H.
Qed.

Lemma perm_disj_valid :
  forall q1 q2 : Qc, perm_disj q1 q2 -> perm_valid q1 /\ perm_valid q2.
Proof.
  intros ?? H. split.
  by apply perm_disj_valid_l in H.
  by apply perm_disj_valid_r in H.
Qed.

Lemma perm_disj_add_l :
  forall q1 q2 q3 : Qc,
  perm_disj q1 q2 -> perm_disj (q1 + q2) q3 -> perm_disj q2 q3.
Proof.
  unfold perm_disj.
  intros q1 q2 q3. intuition.
  apply Qcplus_pos_le_elim with (q2 := q1).
  by rewrite <- Qcplus_comm, Qcplus_assoc.
  by apply Qclt_le_weak.
Qed.

Lemma perm_disj_add_r :
  forall q1 q2 q3 : Qc,
  perm_disj q2 q3 -> perm_disj q1 (q2 + q3) -> perm_disj q1 q2.
Proof.
  unfold perm_disj.
  intros q1 q2 q3. intuition.
  apply Qcplus_pos_le_elim with (q2 := q3).
  by rewrite <- Qcplus_assoc.
  now apply Qclt_le_weak.
Qed.

Lemma perm_disj_assoc_l :
  forall q1 q2 q3 : Qc,
  perm_disj q1 q2 -> perm_disj (q1 + q2) q3 -> perm_disj q1 (q2 + q3).
Proof.
  unfold perm_disj. intuition.
  apply Qcplus_pos_nonneg; auto.
  by apply Qclt_le_weak.
  by rewrite Qcplus_assoc.
Qed.

Lemma perm_disj_assoc_r :
  forall q1 q2 q3 : Qc,
  perm_disj q2 q3 -> perm_disj q1 (q2 + q3) -> perm_disj (q1 + q2) q3.
Proof.
  unfold perm_disj. intuition.
  apply Qcplus_pos_nonneg; auto.
  by apply Qclt_le_weak.
  by rewrite <- Qcplus_assoc.
Qed.

Lemma perm_add_valid :
  forall q1 q2 : Qc, perm_disj q1 q2 -> perm_valid (q1 + q2).
Proof.
  unfold perm_disj, perm_valid.
  intros ?? H. intuition.
  apply Qcplus_pos_nonneg. auto.
  by apply Qclt_le_weak in H.
Qed.

Lemma perm_lt_weaken :
  forall q q1 q2 : Qc,
  perm_disj q1 q2 -> q < q1 -> q < q1 + q2.
Proof.
  intros q q1 q2 H1 H2.
  unfold perm_disj in H1. desf.
  apply Qcplus_lt_weaken; auto.
  by apply Qclt_le_weak.
Qed.

Lemma perm_le_weaken :
  forall q q1 q2 : Qc,
  perm_disj q1 q2 -> q <= q1 -> q <= q1 + q2.
Proof.
  intros q q1 q2 H1 H2.
  unfold perm_disj in H1. desf.
  by apply Qcplus_le_weaken.
Qed.

Lemma perm_disj_full_neg_l :
  forall q : Qc, ~ perm_disj q perm_full.
Proof.
  intros q H.
  unfold perm_disj in H.
  intuition desf.
  assert (perm_full < q + perm_full).
  unfold perm_full in *.
  rewrite Qcplus_comm.
  by apply Qclt_mono_pos.
  unfold perm_full in *.
  by apply Qclt_not_le in H1.
Qed.

Lemma perm_disj_full_neg_r :
  forall q : Qc, ~ perm_disj perm_full q.
Proof.
  intros q H. symmetry in H.
  by apply perm_disj_full_neg_l in H.
Qed.

Lemma perm_lt_diff :
  forall q1 q2 : Qc,
  perm_valid q1 ->
  perm_valid q2 ->
  q1 < q2 ->
  exists q3, perm_disj q1 q3 /\ q1 + q3 = q2.
Proof.
  intros q1 q2 H1 H2 H3.
  apply Qclt_minus_iff in H3.
  exists (q2 + (- q1)). split; auto.
  (* left part of conjunction *)
  - red. intuition auto.
    rewrite Qcplus_comm.
    rewrite <- Qcplus_assoc.
    rewrite Qcplus_comm with (-q1) q1.
    rewrite Qcplus_opp_r.
    rewrite Qcplus_0_r.
    unfold perm_valid in H2. desf.
  (* right part of conjunction *)
  - rewrite Qcplus_comm.
    rewrite <- Qcplus_assoc.
    rewrite Qcplus_comm with (-q1) q1.
    rewrite Qcplus_opp_r.
    by rewrite Qcplus_0_r.
Qed.

Lemma perm_disj_lt :
  forall q1 q2 q3,
  perm_valid q1 ->
  perm_disj q2 q3 ->
  q1 < q2 ->
  perm_disj q1 q3.
Proof.
  intros q1 q2 q3 H1 H2 H3.
  unfold perm_valid in H1.
  destruct H1 as (H1 & H4).
  unfold perm_disj in *.
  destruct H2 as (H2 & H5 & H6).
  intuition.
  apply Qcle_trans with (q2 + q3); auto.
  apply Qcplus_le_mono_r.
  by apply Qclt_le_weak.
Qed.

Lemma perm_disj_le :
  forall q1 q2 q3,
  perm_valid q1 ->
  perm_disj q2 q3 ->
  q1 <= q2 ->
  perm_disj q1 q3.
Proof.
  intros q1 q2 q3 H1 H2 H3.
  apply Qcle_lt_or_eq in H3.
  destruct H3 as [H3 | H3]; vauto.
  by apply perm_disj_lt with q2.
Qed.
