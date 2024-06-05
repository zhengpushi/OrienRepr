(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Orientation in 3D
  author    : ZhengPu Shi
  date      : 2023.04.01

 *)

Require Export MathBase.
Require Export AxisAngle EulerAngle.
Import V3Notations.


(* ########################################################################### *)
(** * Preliminary math *)


(* ########################################################################### *)
(** * 3D rotation operations *)

(* ======================================================================= *)
(** ** Definition of 3D rotation operations *)

(* (* 手性：左手定则，右手定则 *) *)
(* Inductive HandRule := HRLeft | HRRight. *)

(* (* 变换类型：主动变换、被动变换 *) *)
(* Inductive Transformation := TActive | TPassive. *)

(* (* 旋转轴类型：绕机体轴的内旋、绕固定轴的外旋 *) *)
(* Inductive RotateMode := RMIntrinsic | RMExtrinsic. *)


(** *** Specifications for 3D basic rotation operations *)

(** v' = R(θ) * v *)
Lemma Rx_spec1 : forall (v : vec 3) (θ : R), rotaa (mkAA θ v3i) v = (Rx θ) *v v.
Proof. intros; veq; ra. Qed.

Lemma Ry_spec1 : forall (v : vec 3) (θ : R), rotaa (mkAA θ v3j) v = (Ry θ) *v v.
Proof. intros; veq; ra. Qed.

Lemma Rz_spec1 : forall (v : vec 3) (θ : R), rotaa (mkAA θ v3k) v = (Rz θ) *v v.
Proof. intros; veq; ra. Qed.

(** v = R(-θ) * v' *)
Lemma Rx_spec2 : forall (v : vec 3) (θ : R), v = Rx (-θ) *v (rotaa (mkAA θ v3i) v).
Proof.
  intros. rewrite Rx_spec1.
  rewrite <- mmulv_assoc, Rx_neg_mul_Rx, mmulv_1_l; auto.
Qed.

Lemma Ry_spec2 : forall (v : vec 3) (θ : R), v = Ry (-θ) *v (rotaa (mkAA θ v3j) v).
Proof.
  intros. rewrite Ry_spec1.
  rewrite <- mmulv_assoc, Ry_neg_mul_Ry, mmulv_1_l; auto.
Qed.

Lemma Rz_spec2 : forall (v : vec 3) (θ : R), v = Rz (-θ) *v (rotaa (mkAA θ v3k) v).
Proof.
  intros. rewrite Rz_spec1.
  rewrite <- mmulv_assoc, Rz_neg_mul_Rz, mmulv_1_l; auto.
Qed.

(** v = R(θ)\T * v' *)
Lemma Rx_spec3 : forall (v : vec 3) (θ : R), v = (Rx θ)\T *v (rotaa (mkAA θ v3i) v).
Proof. intros. rewrite <- Rx_neg_eq_trans, <- Rx_spec2; auto. Qed.

Lemma Ry_spec3 : forall (v : vec 3) (θ : R), v = (Ry θ)\T *v (rotaa (mkAA θ v3j) v).
Proof. intros. rewrite <- Ry_neg_eq_trans, <- Ry_spec2; auto. Qed.

Lemma Rz_spec3 : forall (v : vec 3) (θ : R), v = (Rz θ)\T *v (rotaa (mkAA θ v3k) v).
Proof. intros. rewrite <- Rz_neg_eq_trans, <- Rz_spec2; auto. Qed.

(** The equivalence of Pre-/Post- multiplication, i.e.,
    u1 ~ u2 -> R * u1 ~ u2 * R\T *)
Lemma Rx_spec4 : forall (u : vec 3) (θ : R), (Rx θ) *v u = u v* ((Rx θ)\T).
Proof. intros. veq; ra.  Qed.

Lemma Ry_spec4 : forall (u : vec 3) (θ : R), (Ry θ) *v u = u v* ((Ry θ)\T).
Proof. intros. veq; ra.  Qed.

Lemma Rz_spec4 : forall (u : vec 3) (θ : R), (Rz θ) *v u = u v* ((Rz θ)\T).
Proof. intros. veq; ra.  Qed.


(** *** Specifications for 3D rotation operations *)

(* 方法一：模仿 Pose2D 中的做法，暂未进行。 *)

(* 3D向量绕x轴旋转的转换矩阵。
   已知向量oa=[a1 a2 a3]^T，其绕x轴旋转到达ob=[b1 b2 b3]，此时x坐标不变，
   而y,z坐标等价于将其投影到yz平面上进行逆时针旋转。
   求出旋转矩阵A(beta),B(beta)，使得：
   [b1 b2 b3]^T=A(beta)[a1 a2 a3]^T，
   [a1 a2 a3]^T=B(beta)[b1 b2 b3]^T
 *)

(* 方法二：使用 rotaa 来验证 *)

