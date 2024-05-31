(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Axis-angels in 3D
  author    : ZhengPu Shi
  date      : 2023.04.01

 *)

Require Export MathBase.
Import V3Notations.


(* ########################################################################### *)
(** * Preliminary math *)


(* ########################################################################### *)
(** * Axis-angle representation *)

(* https://en.wikipedia.org/wiki/Rodrigues%27_rotation_formula *)

(** Rotate one vector a in R^3 by an axis described with a unit vector n and an
    angle θ according to right handle rule, we got the rotated vector as follows.
    This formula is known as Rodrigues formula. *)
Definition rotaa (θ : R) (n : vec 3) (a : vec 3) : vec 3 :=
  ((cos θ) \.* (a - <a,n> \.* n) + (sin θ) \.* (n \x a) + <a,n> \.* n)%V.

(** The correctness of `rotaa` by geometry *)
Theorem rotaa_spec : forall (θ : R) (n : vec 3) (a : vec 3),
    let a_para : vec 3 := vproj a n in
    let a_perp : vec 3 := vperp a n in
    let b : vec 3 := n \x a_perp in
    let a_perp' : vec 3 := ((cos θ) \.* a_perp + (sin θ) \.* b)%V in
    let a' : vec 3 := (a_perp' + a_para)%V in
    vunit n -> a' = rotaa θ n a.
Proof.
  intros. unfold rotaa.
  assert (a_para = <a,n> \.* n)%V as H1.
  { unfold a_para. unfold vproj, Vector.vproj. unfold vunit, Vector.vunit in H.
    rewrite H. unfold vcmul. f_equal. unfold vdot. autounfold with A. field. }
  assert (a_perp = (a - <a,n> \.* n)%V) as H2.
  { unfold a_perp. rewrite <- H1. auto. }
  assert (b = n \x a) as H3.
  { unfold b. rewrite H2.
    rewrite v3cross_add_distr_r. rewrite v3cross_vopp_r.
    rewrite v3cross_vcmul_assoc_r. rewrite v3cross_self. rewrite vcmul_0_r.
    rewrite vopp_vzero. rewrite vadd_0_r. auto. }
  unfold a'. unfold a_perp'. rewrite H1. rewrite H2. rewrite H3. auto.
Qed.

(** Another form of the formula *)
Lemma rotaa_form1 : forall (θ : R) (n : vec 3) (a : vec 3),
    rotaa θ n a =
      ((cos θ) \.* a + (sin θ) \.* (n \x a) + (<a,n> * (1 - cos θ))%R \.* n)%V.
Proof.
  pose proof (vadd_AGroup 3) as HAGroup.
  intros. unfold rotaa. rewrite vcmul_vsub. agroup.
  unfold Rminus. rewrite Rmult_plus_distr_l. rewrite identityRight at 1.
  rewrite vcmul_add. agroup. rewrite vcmul_assoc.
  rewrite <- vcmul_opp. f_equal. autounfold with A. ring.
Qed.

(* Give any rotation axis n̂, rotation angle θ and any vector a.
   If a rotated along n̂ by θ reached a', then: a' = R(n̂,θ) * a *)

(** Matrix formula of roation with axis-angle *)
Definition aa2mat (θ : R) (n : vec 3) : smat 3 :=
  let K := skew3 n in
  mat1 + (sin θ) \.* K + (1 - cos θ)%R \.* (K * K).

(** `aa2mat` has the same behavior as `rotaa` *)
Lemma aa2mat_spec : forall (θ : R) (n : vec 3) (a : vec 3),
    vunit n -> aa2mat θ n *v a = rotaa θ n a.
Proof.
  pose proof (vadd_AGroup 3) as HAGroup.
  intros. rewrite rotaa_form1. unfold aa2mat.
  rewrite !mmulv_madd. rewrite mmulv_1_l.
  rewrite !mmulv_mcmul. rewrite mmulv_assoc.
  rewrite <- !v3cross_eq_skew_mul_vec.
  move2h (sin θ \.* (n \x a))%V. symmetry. move2h (sin θ \.* (n \x a))%V. agroup.
  rewrite (commutative (<a,n>)). rewrite <- vcmul_assoc.
  rewrite v3cross_a_ab_eq_minus.
  rewrite H. rewrite vdot_comm.
  rewrite vcmul_vadd. agroup. unfold Rminus.
  rewrite vcmul_add. rewrite !vcmul_1_l.
  rewrite vcmul_opp, vcmul_vopp. rewrite group_opp_opp at 1.
  agroup.
Qed.

(** The direct form of aa2mat. *)
Definition aa2matM (θ : R) (n : vec 3) : mat 3 3 :=
  let x := n.1 in
  let y := n.2 in
  let z := n.3 in
  let C := cos θ in
  let S := sin θ in
  l2m
    [[C + x * x * (1 - C); x * y * (1 - C) - z * S; x * z * (1 - C) + y * S];
     [y * x * (1 - C) + z * S; C + y * y * (1 - C); y * z * (1 - C) - x * S];
     [z * x * (1 - C) - y * S; z * y * (1 - C) + x * S; C + z * z * (1 - C)]]%R.

(** `aa2matM` is equal to `aa2mat` *)
Theorem aa2matM_eq_aa2mat : forall (θ : R) (n : vec 3),
    vunit n -> aa2matM θ n = aa2mat θ n.
Proof.
  intros. meq; rewrite <- !nth_v2f; ra.
  - pose proof (v3unit_sqr_x n H).
    cbv in H0; rewrite <- !nth_v2f in H0; rewrite H0; ra.
  - pose proof (v3unit_sqr_y n H).
    cbv in H0; rewrite <- !nth_v2f in H0; rewrite H0; ra.
  - pose proof (v3unit_sqr_z n H).
    cbv in H0; rewrite <- !nth_v2f in H0; rewrite H0; ra.
Qed.

(** `aa2matM` is orthogonal matrix *)
Lemma aa2matM_orth : forall (θ : R) (n : vec 3), vunit n -> morth (aa2matM θ n).
Proof.
  intros.
  pose proof (v3unit_sqr_x n H).
  pose proof (v3unit_sqr_y n H).
  pose proof (v3unit_sqr_z n H). cbv in H0,H1,H2.
  ring_simplify in H0.
  ring_simplify in H1.
  ring_simplify in H2.
  meq.
  all: ring_simplify; simp_pow; try (rewrite H0; rewrite sin2'; lra).
Qed.

(** det (`aa2matM`) = 1 *)
Lemma aa2matM_det1 : forall (θ : R) (n : vec 3),
    vunit n -> mdet (aa2matM θ n) = 1.
Proof.
  intros.
  pose proof (v3unit_sqr_x n H).
  pose proof (v3unit_sqr_y n H).
  pose proof (v3unit_sqr_z n H). cbv in H0,H1,H2.
  ring_simplify in H0.
  ring_simplify in H1.
  ring_simplify in H2.
  cbv.
  ring_simplify. simp_pow. rewrite H0. rewrite sin2'. lra.
Qed.

(** `aa2matM` satisfying SO3 *)
Lemma aa2matM_SOnP (θ : R) (n : vec 3) (H : vunit n) : SOnP (aa2matM θ n).
Proof. hnf. split. apply aa2matM_orth; auto. apply aa2matM_det1; auto. Qed.

(** `aa2matM` is SO3 *)
Definition aa2matM_SO3 (θ : R) (n : vec 3) (H : vunit n) : SO3 :=
  mkSOn (aa2matM θ n) (aa2matM_SOnP θ n H).

(** R(-θ) = R(θ)\T *)
Lemma aa2mat_neg_eq_trans : forall (θ : R) (n : vec 3), aa2mat (-θ) n = (aa2mat θ n)\T.
Proof. intros. meq; req. Qed.

(** R(θ) * R(θ)\T = I *)
Lemma aa2mat_mul_aa2mat_trans : forall (θ : R) (n : vec 3),
    vunit n -> aa2mat θ n * (aa2mat θ n)\T = mat1.
Proof.
  intros. rewrite <- aa2matM_eq_aa2mat; auto.
  apply (SOn_mul_trans_r_eq1 (aa2matM_SO3 θ n H)).
Qed.
