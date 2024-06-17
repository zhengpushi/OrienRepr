(*
  Copyright 2023 ZhengPu Shi
  This file is part of OrienRepr. It is distributed under the MIT
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

(** Axis-Angle parameter. (aa: means Axis-Angle) *)
Record AxisAngle := mkAA {aaAngle : R; aaAxis : vec 3}.

(** Rotate one vector a in R^3 by an axis described with a unit vector n and an
    angle θ according to right handle rule, we got the rotated vector as follows.
    This formula is known as Rodrigues formula. *)
Definition rotaa (aa : AxisAngle) (a : vec 3) : vec 3 :=
   let (θ, n) := aa in
  ((cos θ) c* (a - <a,n> c* n) + (sin θ) c* (n \x a) + <a,n> c* n)%V.

(** The correctness of `rotaa` by geometry *)
Theorem rotaa_spec : forall (aa : AxisAngle) (a : vec 3),
    let (θ, n) := aa in
    let a_para : vec 3 := vproj a n in
    let a_perp : vec 3 := vperp a n in
    let b : vec 3 := n \x a_perp in
    let a_perp' : vec 3 := ((cos θ) c* a_perp + (sin θ) c* b)%V in
    let a' : vec 3 := (a_perp' + a_para)%V in
    vunit n -> a' = rotaa aa a.
Proof.
  intros. destruct aa as [θ n]; intros; simpl in *.
  assert (a_para = <a,n> c* n)%V as H1.
  { unfold a_para, vproj, Vector.vproj. unfold vunit, Vector.vunit in H.
    rewrite H. unfold vcmul. f_equal. unfold vdot. autounfold with tA. field. }
  assert (a_perp = (a - <a,n> c* n)%V) as H2.
  { unfold a_perp. rewrite <- H1. auto. }
  assert (b = n \x a) as H3.
  { unfold b. rewrite H2.
    rewrite v3cross_add_distr_r. rewrite v3cross_vopp_r.
    rewrite v3cross_vcmul_assoc_r. rewrite v3cross_self. rewrite vcmul_0_r.
    rewrite vopp_vzero. rewrite vadd_0_r. auto. }
  unfold a'. unfold a_perp'. rewrite H1. rewrite H2. rewrite H3. auto.
Qed.

(** Another form of the formula *)
Lemma rotaa_form1 : forall (aa : AxisAngle) (a : vec 3),
    let (θ, n) := aa in
    rotaa aa a =
      ((cos θ) c* a + (sin θ) c* (n \x a) + (<a,n> * (1 - cos θ))%R c* n)%V.
Proof.
  pose proof (vadd_AGroup 3) as HAGroup.
  intros. destruct aa as [θ n]. unfold rotaa. rewrite vcmul_vsub. agroup.
  unfold Rminus. rewrite Rmult_plus_distr_l. rewrite identityRight at 1.
  rewrite vcmul_add. agroup. rewrite vcmul_assoc.
  rewrite <- vcmul_opp. f_equal. autounfold with tA. ring.
Qed.

(* Give any rotation axis n̂, rotation angle θ and any vector a.
   If a rotated along n̂ by θ reached a', then: a' = R(n̂,θ) * a
   
   绕任意轴 n̂ 旋转 θ 角度的矩阵 R(n̂,θ)，使得 a' = R(n̂,θ) * a *)

(** Matrix formula of roation with axis-angle *)
Definition aa2mat (aa : AxisAngle) : smat 3 :=
  let (θ, n) := aa in
  let K := skew3 n in
  mat1 + (sin θ) c* K + (1 - cos θ)%R c* (K * K).

(** `aa2mat` has the same behavior as `rotaa` *)
Lemma aa2mat_spec : forall (aa : AxisAngle) (a : vec 3),
  let (θ, n) := aa in
  vunit n -> (aa2mat aa) *v a = rotaa aa a.
Proof.
  pose proof (vadd_AGroup 3) as HAGroup.
  intros. pose proof (rotaa_form1 aa a).
  destruct aa as [θ n]. intros. rewrite H; simpl in *.
  rewrite !mmulv_madd. rewrite mmulv_1_l.
  rewrite !mmulv_mcmul. rewrite mmulv_assoc.
  rewrite <- !v3cross_eq_skew_mul_vec.
  move2h (sin θ c* (n \x a))%V. symmetry. move2h (sin θ c* (n \x a))%V. agroup.
  rewrite (commutative (<a,n>)). rewrite <- vcmul_assoc.
  rewrite v3cross_a_ab_eq_minus. rewrite vdot_comm.
  rewrite vcmul_vsub. agroup.
  rewrite vunit_vdotR; auto.
  unfold Rminus. rewrite vcmul_add. rewrite !vcmul_1_l. agroup.
  rewrite vcmul_opp. agroup.
Qed.

(** The direct form of aa2mat. *)
Definition aa2matM (aa : AxisAngle) : mat 3 3 :=
  let (θ, n) := aa in
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
Theorem aa2matM_eq_aa2mat : forall (aa : AxisAngle),
    vunit (aaAxis aa) -> aa2matM aa = aa2mat aa.
Proof.
  intros. destruct aa as [θ n]; intros; simpl in *.
  pose proof (v3unit_sqr_x n H).
  v2e n. rewrite H0 in *. cbv in H0. meq; ra; rewrite H0; ra.
Qed.

(** `aa2matM` is orthogonal matrix *)
Lemma aa2matM_orth : forall (aa : AxisAngle),
    vunit (aaAxis aa) -> morth (aa2matM aa).
Proof.
  intros. destruct aa as [θ n]; intros; simpl in *.
  pose proof (v3unit_sqr_x n H).
  v2e n. rewrite H0 in *. cbv in H0. rewrite !xx_Rsqr in *.
  meq; ring_simplify; simp_pow; rewrite sin2.
  all: rewrite H0; ra.
Qed.

(** det (`aa2matM`) = 1 *)
Lemma aa2matM_det1 : forall (aa : AxisAngle),
    vunit (aaAxis aa) -> mdet (aa2matM aa) = 1.
Proof.
  intros. destruct aa as [θ n]; intros; simpl in *.
  pose proof (v3unit_sqr_x n H).
  v2e n. rewrite H0 in *. cbv in *.
  ring_simplify. ra. rewrite sin2. rewrite H0. ra.
Qed.

(** `aa2matM` satisfying SO3 *)
Lemma aa2matM_SOnP (aa : AxisAngle) (H : vunit (aaAxis aa)) : SOnP (aa2matM aa).
Proof. hnf. split. apply aa2matM_orth; auto. apply aa2matM_det1; auto. Qed.

(** `aa2matM` is SO3 *)
Definition aa2matM_SO3 (aa : AxisAngle) (H : vunit (aaAxis aa)) : SO3 :=
  mkSOn (aa2matM aa) (aa2matM_SOnP aa H).

(** R(-θ) = R(θ)\T *)
Lemma aa2mat_neg_eq_trans : forall (aa : AxisAngle),
    let (θ, n) := aa in
    aa2mat (mkAA (-θ) n) = (aa2mat aa)\T.
Proof.
  intros. destruct aa as [θ n]. simpl.
  pose proof (madd_AGroup 3 3) as HAGroup. agroup.
  rewrite !mtrans_madd.
  rewrite !mtrans_mcmul.
  rewrite mtrans_mmul.
  rewrite mtrans_mat1.
  rewrite !mtrans_skew3, !skew3_vopp.
  ra. rewrite mcmul_mopp. rewrite mcmul_opp.
  rewrite <- mmul_mopp_l. rewrite <- mmul_mopp_r. agroup.
Qed.

(** R(θ) * R(θ)\T = I *)
Lemma aa2mat_mul_aa2mat_trans : forall (aa : AxisAngle),
    vunit (aaAxis aa) -> aa2mat aa * (aa2mat aa)\T = mat1.
Proof.
  intros.
  rewrite <- aa2matM_eq_aa2mat; auto.
  apply (SOn_mul_trans_r_eq1 (aa2matM_SO3 aa H)).
Qed.
