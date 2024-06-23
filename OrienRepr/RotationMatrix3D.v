(*
  Copyright 2023 Zhengpu Shi
  This file is part of OrienRepr. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Rotation Matrices in 3D
  author    : Zhengpu Shi
  date      : 2023.04.01
  
  reference :
  1. Peter Corke, Robotics Vision and Control. page34.
  2. https://en.wikipedia.org/wiki/Euler_angles
  3. https://krasjet.github.io/quaternion
  4. https://zhuanlan.zhihu.com/p/98320567
  5. Carlos M. Roithmayr and Deway H. Hodges, Dynamics: Theory and Application of 
     Kane's Method. page22, page484.
  6. James Diebel, Representing Attitude: Euler Angles, Unit Quaternions, and 
     Rotation Vectors.

  remark    :

  1. Understanding Rotation.
  (1). 右手定则与左手定则(right- or left-handed rule)，可用于决定旋转角的符号
     右手和左手参考系( .. coordinates)，按照x->y->z的顺序，可用于决定第三个轴的方向。
  (2). 主动和被动旋转 (Alibi or alias, 也称 active or passive)，
     主动是旋转物体（刚体、表示刚体的向量），被动是旋转坐标系
  (3). 内部和外部旋转 (intrinsic or extrinsic rotation)，
     内部是绕物体自身的坐标系，旋转轴对于物体不变，但对于外部参考系在变化；
     外部是绕固定的参考坐标系，旋转轴对于外部参考系不变，但对于物体在变化。
  (4). 预乘和后乘 (pre- or post-multiplication)
     同一个点P，可以被表示为列向量v或行向量w。
     旋转矩阵能被预乘以列向量 Rv，或者后乘以行向量 wR。
     然而，Rv产生的旋转与wR的是反向的。
     为了得到相同的旋转（即，P点相同的最终坐标），等价的行向量必须后乘以R的转置（即，wR\T）

  2. Rotation matrices.
  (1) There are two explanations for coordinate transformation:
   i. The vector is static, and the coordinate system is changing from one to another.
    reference: {Dibel - Representing}
    We define the rotation matrix that encodes the attitude of a rigid body to be 
    the matrix that when pre-multiplied by a vector expressed in the body-fixed 
    coordinates yields the same vector expressed in the word coordinates.
    That is, if v\in R^3 is a vector in the body-fixed coordinates and v'\in R^3 is 
    the same vector expressed in the word coordinates, then the following relations 
    hold:
            v' = R * v
            v = R\T * v'
    These expression apply to {vectors}, relative quantities lacking a position in 
    space. To transform a {point} from one coordinate system to other we must 
    subtract the offset to the origin of the target coordinate system before 
    applying the rotation matrix.
  ii. There is only one coordinate system, the vector is chaning.
    Orthogormal rotation matrices for rotation of θ aobout the x-,y- and z- axes.
    Notes:
    1>. Give a column-vector v1 respect to this coordinate, when actively rotate it 
        about the x-axes, we could get a new vector v1' respect to this coordinate by
        this formula:
             v1' = Rx(θ) v1
    2>. If give a row-vector v2, ..., v2' ...
             v2' = v2 (Rx(θ))\T

  (2) Note the following relations:
    1. v' = R v 表示v经过R旋转到达v'，对应的， R' v' = v 表示v'经过R'旋转到达v。 
    2. R\T 就是 R^(-1)，也写作 R'，它表示一个逆的旋转
    3. 旋转矩阵R表示向量旋转一个正角度(逆时针)，R\T则表示向量旋转一个负角度（顺时针）。
    4. 向量旋转正角度，相当于坐标系旋转负角度
    5. v' = (RxRyRz) v 表示对向量 v 按z,y,x轴的顺序进行旋转得到 v'，
         而需要由 v' 计算 v 时，令 v' W = v，则 W = (RxRyRz)' = Rz'Ry'Rx'
  (3) 任意朝向都能分解为从已知的标准朝向开始的三个基本旋转。
     等价的，任意旋转矩阵R能被分解为三个基本旋转矩阵的乘积。
     例如 R = X(α)Y(β)Z(γ) 是一个旋转矩阵，可表示关于 z,y,x轴的外部旋转的复合，
     或是关于 x,y',z''轴的内部旋转的复合。

  3. Linearization:
  (1). 小角度变化经常被用来近似描述系统的动态特性，此时系统的响应可通过线性模型来预测和控制。
  (2). 角度变化很小(通常认为10度以内)时，可线性化处理，
     sin(α)->α, cos(α)->1, 高阶项sin(α)*sin(β)->0
*)

Require Export MathBase.
Require Import AxisAngle.


(* ########################################################################### *)
(** * Basic Rotation Matrics *)

(* ======================================================================= *)
(** ** Definitions of 3D basic rotation matrices *)

(** Give a column-vector v respect to this coordinate, when actively rotate it about
    the x-axes and reached v' respect to this coordinate, then: v' = Rx(θ) * v *)
Definition Rx (θ : R) : mat 3 3 :=
  l2m
    [[1; 0; 0];
     [0; cos θ; - sin θ];
     [0; sin θ; cos θ]]%R.

(** Give a column-vector v respect to this coordinate, when actively rotate it about
    the y-axes and reached v' respect to this coordinate, then: v' = Ry(θ) * v *)
Definition Ry (θ : R) : mat 3 3 :=
  l2m
    [[cos θ; 0; sin θ];
     [0; 1; 0];
     [- sin θ; 0; cos θ]]%R.

(** Give a column-vector v respect to this coordinate, when actively rotate it about
    the z-axes and reached v' respect to this coordinate, then: v' = Rz(θ) * v *)
Definition Rz (θ : R) : mat 3 3 :=
  l2m
    [[cos θ; - sin θ; 0];
     [sin θ; cos θ; 0];
     [0; 0; 1]]%R.


(* ======================================================================= *)
(** ** Properties of 3D basic rotation matrices *)

(** Rx,Ry,Rz are the special case of aa2mat. *)
Theorem aa2mat_eq_Rx : forall θ : R, aa2mat (mkAA θ v3i) = Rx θ.
Proof. intros; meq; ra. Qed.

Theorem aa2mat_eq_Ry : forall θ : R, aa2mat (mkAA θ v3j) = Ry θ.
Proof. intros; meq; ra. Qed.

Theorem aa2mat_eq_Rz : forall θ : R, aa2mat (mkAA θ v3k) = Rz θ.
Proof. intros; meq; ra. Qed.

(** Rx,Ry,Rz are orthogonal matrix *)
Lemma Rx_orth : forall (θ : R), morth (Rx θ).
Proof. intros; meq; ra. Qed.

Lemma Ry_orth : forall (θ : R), morth (Ry θ).
Proof. intros; meq; ra. Qed.

Lemma Rz_orth : forall (θ : R), morth (Rz θ).
Proof. intros; meq; ra. Qed.

(** Rx,Ry,Rz are invertible matrix *)
Lemma Rx_minvtble : forall (θ : R), minvtble (Rx θ).
Proof. intros. apply morth_minvtble. apply Rx_orth. Qed.

Lemma Ry_minvtble : forall (θ : R), minvtble (Ry θ).
Proof. intros. apply morth_minvtble. apply Ry_orth. Qed.

Lemma Rz_minvtble : forall (θ : R), minvtble (Rz θ).
Proof. intros. apply morth_minvtble. apply Rz_orth. Qed.

(** The determinant of Rx,Ry,Rz are 1 *)
Lemma Rx_det1 : forall (θ : R), mdet (Rx θ) = 1.
Proof. intros; cbv; ra. Qed.

Lemma Ry_det1 : forall (θ : R), mdet (Ry θ) = 1.
Proof. intros; cbv; autorewrite with R; auto. Qed.

Lemma Rz_det1 : forall (θ : R), mdet (Rz θ) = 1.
Proof. intros; cbv; autorewrite with R; auto. Qed.

(** Rx,Ry,Rz are member of SO3 *)
Lemma Rx_SOnP : forall θ : R, SOnP (Rx θ).
Proof. intros. hnf. split. apply Rx_orth. apply Rx_det1. Qed.
Lemma Ry_SOnP : forall θ : R, SOnP (Ry θ).
Proof. intros. hnf. split. apply Ry_orth. apply Ry_det1. Qed.
Lemma Rz_SOnP : forall θ : R, SOnP (Rz θ).
Proof. intros. hnf. split. apply Rz_orth. apply Rz_det1. Qed.

Definition Rx_SO3 (θ : R) : SO3 := mkSOn (Rx θ) (Rx_SOnP θ).
Definition Ry_SO3 (θ : R) : SO3 := mkSOn (Ry θ) (Ry_SOnP θ).
Definition Rz_SO3 (θ : R) : SO3 := mkSOn (Rz θ) (Rz_SOnP θ).

(** 使用群 SOn 可以直接证明逆矩阵、旋转矩阵等有关的性质，并且比计算式证明的速度快 *)

(** R(θ)⁻¹ = R(θ)\T *)

Lemma Rx_inv_eq_trans : forall θ : R, (Rx θ)\-1 = (Rx θ)\T.
Proof.
  (* method 1 : prove by computing (too slow, 0.4s) *)
  (* because the computation "determinant <> 0" prevents the computation,
     we should use minvNoCheck. Maybe we should use it as default method *)
  (* intros.
     unfold minv. unfold OrthAM.AM.MinvCore_inst.minv.
     rewrite <- minvNoCheck_spec.
     meq; ra; field_simplify_eq. *)
  (* method 2 : prove by reasoning *)
  intros. apply (SOn_minv_eq_trans (Rx_SO3 θ)).
Qed.

Lemma Ry_inv_eq_trans : forall θ : R, (Ry θ)\-1 = (Ry θ)\T.
Proof. intros; apply (SOn_minv_eq_trans (Ry_SO3 θ)). Qed.

Lemma Rz_inv_eq_trans : forall θ : R, (Rz θ)\-1 = (Rz θ)\T.
Proof. intros; apply (SOn_minv_eq_trans (Rz_SO3 θ)). Qed.

(** R(-θ) = R(θ)\T *)
Lemma Rx_neg_eq_trans : forall θ : R, Rx (-θ) = (Rx θ)\T.
Proof. intros; meq; ra. Qed.

Lemma Ry_neg_eq_trans : forall θ : R, Ry (-θ) = (Ry θ)\T.
Proof. intros; meq; ra. Qed.

Lemma Rz_neg_eq_trans : forall θ : R, Rz (-θ) = (Rz θ)\T.
Proof. intros; meq; ra. Qed.

(** R(-θ) * R(θ) = I *)
Lemma Rx_neg_mul_Rx : forall θ : R, Rx (- θ) * Rx θ = mat1.
Proof.
  (* intros; meq; ra. Qed. *)
  intros; rewrite Rx_neg_eq_trans, <- Rx_inv_eq_trans, mmul_minvAM_l; auto.
  apply Rx_minvtble.
Qed.

Lemma Ry_neg_mul_Ry : forall θ : R, Ry (- θ) * Ry θ = mat1.
Proof.
  intros; rewrite Ry_neg_eq_trans, <- Ry_inv_eq_trans, mmul_minvAM_l; auto.
  apply Ry_minvtble.
Qed.

Lemma Rz_neg_mul_Rz : forall θ : R, Rz (- θ) * Rz θ = mat1.
Proof.
  intros; rewrite Rz_neg_eq_trans, <- Rz_inv_eq_trans, mmul_minvAM_l; auto.
  apply Rz_minvtble.
Qed.

(** R(θ) * R(-θ) = I *)
Lemma Rx_mul_Rx_neg : forall θ : R, Rx θ * Rx (- θ) = mat1.
Proof.
  intros; rewrite Rx_neg_eq_trans, <- Rx_inv_eq_trans, mmul_minvAM_r; auto.
  apply Rx_minvtble.
Qed.

Lemma Ry_mul_Ry_neg : forall θ : R, Ry θ * Ry (- θ) = mat1.
Proof.
  intros; rewrite Ry_neg_eq_trans, <- Ry_inv_eq_trans, mmul_minvAM_r; auto.
  apply Ry_minvtble.
Qed.

Lemma Rz_mul_Rz_neg : forall θ : R, Rz θ * Rz (- θ) = mat1.
Proof.
  intros; rewrite Rz_neg_eq_trans, <- Rz_inv_eq_trans, mmul_minvAM_r; auto.
  apply Rz_minvtble.
Qed.
