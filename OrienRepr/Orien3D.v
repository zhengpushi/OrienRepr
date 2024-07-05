(*
  Copyright 2023 Zhengpu Shi
  This file is part of OrienRepr. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Orientation in 3D
  author    : Zhengpu Shi
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
(** ** Basic 3D rotation operations *)

(* (* 手性：左手定则，右手定则 *) *)
(* Inductive HandRule := HRLeft | HRRight. *)

(* (* 变换类型：主动变换、被动变换 *) *)
(* Inductive Transformation := TActive | TPassive. *)

(* (* 旋转轴类型：绕机体轴的内旋、绕固定轴的外旋 *) *)
(* Inductive RotateMode := RMIntrinsic | RMExtrinsic. *)


(** *** Definitions for 3D basic rotation operations *)

(* Check Rx. *)
(* Check Ry. *)
(* Check Rz. *)


(** *** Specifications for 3D basic rotation operations *)

(** v' = R(θ) * v *)
Lemma Rx_spec : forall (v : vec 3) (θ : R), rotaa (mkAA θ v3i) v = (Rx θ) *v v.
Proof. intros; veq; ra. Qed.

Lemma Ry_spec : forall (v : vec 3) (θ : R), rotaa (mkAA θ v3j) v = (Ry θ) *v v.
Proof. intros; veq; ra. Qed.

Lemma Rz_spec : forall (v : vec 3) (θ : R), rotaa (mkAA θ v3k) v = (Rz θ) *v v.
Proof. intros; veq; ra. Qed.

(** v = R(-θ) * v' *)
Lemma Rx_neg_spec : forall (v : vec 3) (θ : R), v = Rx (-θ) *v (rotaa (mkAA θ v3i) v).
Proof.
  intros. rewrite Rx_spec.
  rewrite <- mmulv_assoc, Rx_neg_mul_Rx, mmulv_1_l; auto.
Qed.

Lemma Ry_neg_spec : forall (v : vec 3) (θ : R), v = Ry (-θ) *v (rotaa (mkAA θ v3j) v).
Proof.
  intros. rewrite Ry_spec.
  rewrite <- mmulv_assoc, Ry_neg_mul_Ry, mmulv_1_l; auto.
Qed.

Lemma Rz_neg_spec : forall (v : vec 3) (θ : R), v = Rz (-θ) *v (rotaa (mkAA θ v3k) v).
Proof.
  intros. rewrite Rz_spec.
  rewrite <- mmulv_assoc, Rz_neg_mul_Rz, mmulv_1_l; auto.
Qed.

(** v = R(θ)\T * v' *)
Lemma Rx_trans_spec : forall (v : vec 3) (θ : R),
    v = (Rx θ)\T *v (rotaa (mkAA θ v3i) v).
Proof. intros. rewrite <- Rx_neg_eq_trans, <- Rx_neg_spec; auto. Qed.

Lemma Ry_trans_spec : forall (v : vec 3) (θ : R),
    v = (Ry θ)\T *v (rotaa (mkAA θ v3j) v).
Proof. intros. rewrite <- Ry_neg_eq_trans, <- Ry_neg_spec; auto. Qed.

Lemma Rz_trans_spec : forall (v : vec 3) (θ : R),
    v = (Rz θ)\T *v (rotaa (mkAA θ v3k) v).
Proof. intros. rewrite <- Rz_neg_eq_trans, <- Rz_neg_spec; auto. Qed.

(** The equivalence of Pre-/Post- multiplication, i.e.,
    R *v u = u v* (R\T) *)
Lemma Rx_mmulv_eq_mvmul : forall (u : vec 3) (θ : R), (Rx θ) *v u = u v* ((Rx θ)\T).
Proof. intros. veq; ra.  Qed.

Lemma Ry_mmulv_eq_mvmul : forall (u : vec 3) (θ : R), (Ry θ) *v u = u v* ((Ry θ)\T).
Proof. intros. veq; ra.  Qed.

Lemma Rz_mmulv_eq_mvmul : forall (u : vec 3) (θ : R), (Rz θ) *v u = u v* ((Rz θ)\T).
Proof. intros. veq; ra.  Qed.


(* ======================================================================= *)
(** ** 3D rotation operations *)

(** *** Definitions for 3D rotation operations *)

(* According to different definitions of Euler angles, there are 24 
   rotation conventions*)
(* Check B123. *)
(* Check B132. *)

(** *** Specifications for 3D rotation operations *)

(* All rotation matrices are orthogonal matrices, thus theare are many
   useful properties *)

(* Search morth. *)
(*
Check morth_minvtble. 
(* forall {n : nat} (M : smat n), morth M -> minvtble M *)
Check morth_minv. 
(* forall {n : nat} (M : smat n), morth M -> morth (M\-1) *)
Check morth_mtrans. 
(* forall {n : nat} (M : smat n), morth M -> morth (M\T) *)
Check morth_mmul.
(* forall {n : nat} (M N : smat n), morth M -> morth N -> morth (M * N) *)
Check morth_mdet.
(* forall {n : nat} (M : smat n), morth M -> |M| = Aone \/ |M| = (- Aone)%A *)
Check morth_keep_dot.
(* forall {n : nat} (M : smat n) (a b : vec n), morth M -> <M *v a,M *v b> = <a,b> *)
Check morth_keep_norm.
(* forall {n : nat} (M : smat n) (a : vec n), morth M -> vnorm (M *v a) = M *v vnorm a *)
Check morth_keep_length.
(* forall {n : nat} (M : smat n) (a : vec n), morth M -> ||M *v a|| = ||a|| *)
Check morth_keep_nonzero.
(* forall {n : nat} (M : smat n) (a : vec n), a <> vzero -> morth M -> M *v a <> vzero *)
Check morth_keep_angle.
(* forall {n : nat} (M : smat n) (a b : vec n), morth M -> M *v a /_ M *v b = a /_ b *)
Check morth_keep_v3cross_det1.
(* forall (M : smat 3) (a b : vec 3), morth M -> |M| = 1 -> M *v a \x M *v b = M *v (a \x b) *)
Check morth_keep_v3cross_detNeg1.
(* forall (M : smat 3) (a b : vec 3), morth M -> |M| = -1 -> M *v a \x M *v b = (- M *v (a \x b))%V *)
Check morth_iff_mul_trans_l.
(* forall {n : nat} (M : smat n), morth M <-> M\T * M = mat1 *)
Check morth_iff_mul_trans_r.
(* forall {n : nat} (M : smat n), morth M <-> M * M\T = mat1 *)
Check minv_eq_trans_imply_morth.
(* forall {n : nat} (M : smat n), minvtble M -> M\-1 = M\T -> morth M *)
Check morth_imply_col_neq0.
(* forall {n : nat} (M : smat n) (i : 'I_n), morth M -> mcol M i <> vzero *)
Check morth_imply_minv_eq_trans.
(* forall {n : nat} (M : smat n), morth M -> M\-1 = M\T *)
Check morth_imply_vlen_row.
(* forall {n : nat} (M : smat n) (i : 'I_n), morth M -> ||mrow M i|| = 1 *)
Check morth_imply_vlen_col.
(* forall {n : nat} (M : smat n) (i : 'I_n), morth M -> ||mcol M i|| = 1 *)
Check morth_imply_orth_cols_diff.
(* forall {n : nat} (M : smat n) (i j : 'I_n), morth M -> i <> j -> mcol M i _|_ mcol M j *)
Check morth_imply_vdot_cols_diff.
(* forall {n : nat} (M : smat n) (i j : 'I_n), morth M -> i <> j -> <mcol M i,mcol M j> = 0 *)
Check morth_imply_sin_vangle_cols_diff.
(* forall {n : nat} (M : smat n) (i j : 'I_n), morth M -> i <> j -> sin (mcol M i /_ mcol M j) = 1 *)
Check morth_imply_vangle_cols_diff.
(* forall {n : nat} (M : smat n) (i j : 'I_n), morth M -> i <> j -> mcol M i /_ mcol M j = PI / 2 *)
Check morth_imply_vlen_v3cross_cols_diff.
(* forall (M : smat 3) (i j : 'I_3), morth M -> i <> j -> ||mcol M i \x mcol M j|| = 1 *)
 *)





(* 方法一：模仿 Pose2D 中的做法，暂未进行。 *)

(* 3D向量绕x轴旋转的转换矩阵。
   已知向量oa=[a1 a2 a3]^T，其绕x轴旋转到达ob=[b1 b2 b3]，此时x坐标不变，
   而y,z坐标等价于将其投影到yz平面上进行逆时针旋转。
   求出旋转矩阵A(beta),B(beta)，使得：
   [b1 b2 b3]^T=A(beta)[a1 a2 a3]^T，
   [a1 a2 a3]^T=B(beta)[b1 b2 b3]^T
 *)

(* 方法二：使用 rotaa 来验证 *)

