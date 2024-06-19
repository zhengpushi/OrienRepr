(*
  Copyright 2023 ZhengPu Shi
  This file is part of OrienRepr. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Pose in 3D (with Frame)
  author    : ZhengPu Shi
  date      : 2024.06.12

  reference :
  1. 机器人学：建模、控制与视觉

  remark    :
  1. 将“点的坐标”、“姿态”、“位姿”设计成了依赖类型，依赖于坐标系，从而避免一部分错误。
  2. 借助于“类型”来避免出错的思想在解决安全性问题时是有用的，但不是完全有用。
     因为同样的类型可能有无数个对象，具体用哪一个还需要用户根据业务逻辑来选择，
     而这种选择是可能会出错的。
     例如，“自然数加法”完全有可能写错，这不是类型层面可以避免的，而需要一些性质来辅助论证。
     再比如，对电阻电路中的电流和电压进行计算的算法中，即使提供了不同物理量的类型系统，
     用户完全有可能写错，需要使用电路分析中的原理来加以验证。
  3. 此处对坐标、姿态、位姿等概念使用依赖类型，有一定的作用。
     而且，在一般的上下文中，这些概念对应的值是唯一的，所以更加有用。
 *)


(* Require Import AxisAngle. *)
(* Require Import EulerAngle. *)
(* Require Import Quaternion. *)
Require Export RotationMatrix3D.


(* ########################################################################### *)
(** * Pose representation of rigid-body 刚体位姿描述 *)

(* ======================================================================= *)
(** ** 坐标系的描述 *)

(** 用自然数来表示不同的坐标系 *)
Definition Frame := nat.

(** 任意一点在坐标系{A}中的位置矢量 *)
Record Point (A : Frame) :=
  mkPoint {
      pointVec :> vec 3
    }.
Arguments mkPoint {A}.
Arguments pointVec {A}.

(** 坐标系{B}相对于{A}的姿态 *)
Record Orien (A B : Frame) :=
  mkOrien {
      orienMat :> smat 3;
      orienSO3 :> SOnP orienMat
    }.
Arguments mkOrien {A B}.
Arguments orienMat {A B}.
Arguments orienSO3 {A B}.

(** orienMat o1 = orienMat o2 -> o1 = o2 *)
Lemma orien_eq_if : forall A B (o1 o2 : Orien A B), orienMat o1 = orienMat o2 -> o1 = o2.
Proof.
  intros. destruct o1 as [o1Mat o1SO3], o2 as [o2Mat o2SO3]. simpl in *.
  subst. f_equal. apply proof_irrelevance.
Qed.


(** 坐标系{B}相对于坐标系{A}的位姿，由两部分组成：
   1. 坐标系{B}相对于{A}的姿态 R : smat 3
   2. 坐标系{B}的原点相对于{A}的平移矢量 p : vec 3 *)
Record Pose (A B : Frame) :=
  mkPose {
      poseOrien :> Orien A B;
      poseOffset :> Point A
    }.
Arguments mkPose {A B}.
Arguments poseOrien {A B}.
Arguments poseOffset {A B}.

(** orienMat p1 = orienMat p2 -> poseOffset p1 = poseOffset p2 -> p1 = p2 *)
Lemma pose_eq_if : forall A B (p1 p2 : Pose A B),
    orienMat p1 = orienMat p2 -> poseOffset p1 = poseOffset p2 -> p1 = p2.
Proof.
  intros. destruct p1 as [p1Orien p1Offset], p2 as [p2Orien p2Offset]. simpl in *.
  subst. f_equal. apply orien_eq_if; auto.
Qed.


(* ======================================================================= *)
(** ** 坐标变换 *)

(** 坐标平移(translate)，或称平移映射：
    设坐标系{B}和{A}具有相同的方位，但是原点不重合，用平移矢量offsetB2A描述
    {B}相对于{A}的位置，则任意点p在{A}中的坐标pA可由p在{B}中的坐标pB得到 *)
Definition transl {A B} (offsetB2A : Point A) (pB : Point B)
  : Point A :=
  mkPoint (pB + offsetB2A)%V.

(** 坐标旋转(rotation)，或称旋转映射：
    设坐标系{B}和{A}由共同的坐标原点，但两者的姿态不同，用旋转矩阵orienB2A描述
    {B}相对于{A}的姿态，则任意点p在{A}中的坐标pA可由p在{B}中的坐标pB得到 *)
Definition rotate {A B} (orienB2A : Orien A B) (pB : Point B)
  : Point A :=
  mkPoint (orienB2A *v pB).

(** 一般刚体变换(transformation)：
    设坐标系{B}和{A}不但原点不重合，而且姿态也不相同，用位姿poseB2A描述
    {B}相对于{A}的位姿，则任意点p在{A}中的坐标pA可由p在{B}中的坐标pB得到 *)
Definition trans {A B} (poseB2A : Pose A B) (pB : Point B)
  : Point A :=
  mkPoint (poseB2A *v pB + poseOffset poseB2A)%V.

(** 一般刚体变换的公式可以借由一个过渡坐标系{B}来得到 *)

(** 首先，分步骤进行详细推导 *)
Section trans_spec1.
  (* 假设有两个坐标系{A}和{B}，并且{B}相对于{A}的位姿是poseB2A，
    任意点p在{A}和{B}中的坐标分别为pA和pB *)
  Variable A B : Frame.
  Variable poseB2A : Pose A B.
  Variable pA : Point A.
  Variable pB : Point B.

  (* 再假设有一个过渡坐标系{C}，使{C}的坐标原点与{B}的重合，而姿态与{A}的相同 *)
  Variable C : Frame.
  Let poseB2C : Pose C B := mkPose (mkOrien poseB2A poseB2A) (mkPoint vzero).
  Let poseC2A : Pose A C := mkPose (mkOrien mat1 mat1_SOnP) (poseOffset poseB2A).

  (* 再设 p在{C}中的坐标为pC *)
  Variable pC : Point C.

  (* 显然，如下关系式成立：
     1. pC可由对pB进行坐标旋转得到
     2. pA可由pC进行坐标平移得到 *)
  Hypotheses pC_eq_rotate : pC = rotate poseB2C pB.
  Hypotheses pA_eq_transl : pA = transl poseC2A pC.

  (* 证明 trans 函数的定义是合理的 *)
  Goal pA = trans poseB2A pB.
  Proof.
    rewrite pA_eq_transl. rewrite pC_eq_rotate.
    unfold transl, rotate, trans. simpl. auto.
  Qed.
End trans_spec1.

(* 写成一个引理 *)
Lemma trans_spec1 : forall (A B C : Frame) (poseB2A : Pose A B)
                      (pA : Point A) (pB : Point B) (pC : Point C),
    let poseB2C : Pose C B := mkPose (mkOrien poseB2A poseB2A) (mkPoint vzero) in
    let poseC2A : Pose A C := mkPose (mkOrien mat1 mat1_SOnP) (poseOffset poseB2A) in
    pC = rotate poseB2C pB ->
    pA = transl poseC2A pC ->
    pA = trans poseB2A pB.
Proof.
  intros. rewrite H0. rewrite H.
  unfold transl, rotate, trans. simpl. auto.
Qed.

(** 当姿态为零时，一般刚体变换等价于坐标平移 *)
Lemma trans_eq_transl : forall A B (poseB2A : Pose A B) (pB : Point B),
    poseOrien poseB2A = mkOrien mat1 mat1_SOnP ->
    trans poseB2A pB = transl (poseOffset poseB2A) pB.
Proof.
  intros. destruct poseB2A as [orien offset]. simpl in *.
  destruct orien as [orienB2A]. inv H.
  unfold trans, transl. simpl. rewrite mmulv_1_l. auto.
Qed.

(** 当原点相同时，一般刚体变换等价于坐标旋转 *)
Lemma trans_eq_rotate : forall A B (poseB2A : Pose A B) (pB : Point B),
    poseOffset poseB2A = mkPoint vzero ->
    trans poseB2A pB = rotate (poseOrien poseB2A) pB.
Proof.
  intros. destruct poseB2A as [orien offset]. simpl in *.
  destruct offset as [offsetB2A]. inv H.
  unfold trans, rotate. simpl. rewrite vadd_0_r. auto.
Qed.


(** Example 3.1 (page 39) *)
Module ex_3_1.

  Section ex_3_1.
    (* 两个坐标系{A}和{B}，刚开始{B}和{A}重合，然后{B}绕{A}的z轴转30度，
     然后沿{A}的x轴移动10个单位，并沿{A}的y轴移动5个单位。*)
    Variable A B : Frame.

    (* 求{B}相对于{A}的位置向量和旋转矩阵（ *)
    Example offsetB2A : Point A := mkPoint (l2v [10;5;0]).
    Example orienB2A : Orien A B := mkOrien (Rz (deg2rad 30)) (Rz_SOnP _).
    (* 进而得到{B}相对于{A}的位姿 *)
    Example poseB2A : Pose A B := mkPose orienB2A offsetB2A.

    (* 假设p点在{B}中的坐标 *)
    Example pB : Point B := mkPoint (l2v [3;7;0]).

    (* 求p点在{A}中的坐标 *)
    Example pA : Point A := trans poseB2A pB.

    (* 验证这些结果与教材上一致 *)

    (* 1. 先验证旋转矩阵的结果 *)
    Lemma orienB2A_eq :
      (orienB2A : smat 3) =
        l2m [[(sqrt 3)/2; -1/2; 0]; [1/2; (sqrt 3)/2; 0]; [0; 0; 1]].
    Proof.
      cbn. replace (deg2rad 30) with (PI/6) by (cbv; ra).
      meq.
      (* Tips: 如何让 
       cos (PI * / ((R1 + R1) * (R1 + (R1 + R1)))) 
       自动化简称 cos (PI/6)，
       以便使用重写，从而自动证明 *)
      (* 目前只好先手动进行 *)
      pose proof cos_PI6. cbv in H. auto.
      pose proof sin_PI6. cbv in H. ra.
      pose proof sin_PI6. cbv in H. ra.
      pose proof cos_PI6. cbv in H. auto.
    Qed.

  End ex_3_1.

  (* 2. 对于pA的值，教材上给的近似值，所以，我们可以在OCaml中计算看看 *)
  Example pA_value : list R := v2l (pA O O).

  (* 首先抽取代码 *)
  (* Extraction "ocaml_test_pose_ex_3_1.ml" pA_value. *)
  
(* 运行结果如下，与教材一致：
     utop[4]> Coq_ex_3_1.pA_value;;
     - : float list = [9.09807621135331601; 12.5621778264910713; 0.]  *)
  
End ex_3_1.



(* ########################################################################### *)
(** * Homogeneous coordinates and homogeneous transformation 齐次坐标和齐次变换 *)

(* ======================================================================= *)
(** ** Homogeneous coordinates *)

(* 
   1. 空间一点p的直角坐标为p=[x y z]^T，则它的齐次坐标可表示为 p=[x y z 1]^T。
   2. 齐次坐标的表示不唯一，将其各元素同乘一非零因子ω后，仍然代表同一点p，即
      p = [x y z 1] = [a b c ω]，其中：a=ωx, b=ωy, c=ωz
   3. [0 0 0 0]^T没有意义
   4. 一些规定：
      (1) 列矢量[a b c 0]^T (其中a^2+b^2+c^2<>0) 表示空间的无穷远点。把包括了无穷远点的
          空间称为扩大空间，把第4个元素为非零的点称为非无穷远点。
      (2) 无穷远点[a b c 0]^T的三元素a,b,c称为该点的方向数。例如[1 0 0 0]代表x轴上的
          无穷远点，可表示x轴的方向。
      (3) 非无穷远点[0 0 0 1]^T代表坐标原点。
      (4) 于是，利用齐次坐标不仅可表示点的位置，还可规定矢量的方向。
          当第4个元素非零时，齐次坐标代表点的位置；为零时，代表方向。
          利用该性质，可赋予齐次变换矩阵另一个物理解释：齐次变换矩阵poseHomB2A描述了
          坐标系{B}相对于{A}的位置和姿态，前三个列矢量分别代表{B}的三个坐标轴相对于{A}
          的方向，第四个列矢量{}^Ap_{B_0}描述{B}的坐标原点相对于{A}的位置。*)

(** Convert Euclidean coordinates to homogeneous coordinates *)
Definition e2h (v : vec 3) : vec 4 := l2v [v.1; v.2; v.3; 1].

(** Convert homogeneous coordinates to Euclidean coordinates *)
Definition h2e (v : vec 4) : vec 3 := l2v [v.1/v.4; v.2/v.4; v.3/v.4].

Lemma h2e_e2h : forall (v : vec 3), h2e (e2h v) = v.
Proof. intros. v2e v. veq; ra. Qed.

Lemma e2h_h2e : forall (v : vec 4), v.4 = 1 -> e2h (h2e v) = v.
Proof. intros. v2e v. cbv in H. rewrite H. veq; ra. Qed.

(** 任意一点在坐标系{A}中的齐次坐标 *)
Record PointHom (A : Frame) :=
  mkPointHom {
      pointHomVec :> vec 4;
    }.
Arguments mkPointHom {A}.
Arguments pointHomVec {A}.


(* ======================================================================= *)
(** ** Homogeneous transformation *)

(** Homogeneous transformation matrix of frame {B} respect to {A}, also means the 
    relative pose of frame {B} respect ot {A} *)
Record PoseHom (A B : Frame) :=
  mkPoseHom {
      poseHomMat :> smat 4;
      poseHomSO3 : SOnP (mremovecT (mremoverT poseHomMat));
      poseHomRow4 : poseHomMat.4 = vconsT vzero 1
    }.
Arguments mkPoseHom {A B}.
Arguments poseHomMat {A B}.
Arguments poseHomSO3 {A B}.
Arguments poseHomRow4 {A B}.

(** orienMat p1 = orienMat p2 -> poseOffset p1 = poseOffset p2 -> p1 = p2 *)
Lemma poseHom_eq_if : forall A B (p1 p2 : PoseHom A B),
    poseHomMat p1 = poseHomMat p2 -> p1 = p2.
Proof.
  intros. destruct p1 as [poseHomMat_1 poseHomSO3_1 poseHomRow4Zero_1].
  destruct p2 as [poseHomMat_2 poseHomSO3_2 poseHomRow4Zero_2].
  simpl in *. subst. f_equal. all: apply proof_irrelevance.
Qed.

(** Convert Pose to PoseHom *)
Definition pose2poseHom {A B} (poseB2A : Pose A B) : PoseHom A B.
  pose (poseB2A : smat 3) as R.
  pose (poseOffset poseB2A : vec 3) as p.
  pose (orienSO3 poseB2A) as R_SO3.
  pose (mconscT R p : mat 3 4) as m34.
  pose (vconsT vzero 1 : vec 4) as p4.
  pose (mconsrT m34 p4 : smat 4) as m44.
  refine (mkPoseHom m44 _ _); auto.
  unfold m44,m34,p4.
  rewrite mremoverT_mconsrT. rewrite mremovecT_mconscT. auto.
Defined.

(** Convert Pose to PoseHom *)
Definition poseHom2pose {A B} (poseHomB2A : PoseHom A B) : Pose A B.
  pose (poseHomMat poseHomB2A) as m44.
  pose (mremovecT (mremoverT poseHomB2A)) as m33.
  pose (poseHomSO3 m44) as m33_SO3.
  pose (vremoveT (mtailc m44)) as p3.
  apply (mkPose (mkOrien m33 m33_SO3) (mkPoint p3)).
Defined.

(** poseHom2pose (pose2poseHom poseB2A) = poseB2A *)
Lemma poseHom2pose_pose2poseHom : forall A B (poseB2A : Pose A B),
    poseHom2pose (pose2poseHom poseB2A) = poseB2A.
Proof.
  intros. unfold poseHom2pose, pose2poseHom; simpl.
  destruct poseB2A as [[orienMatB2A orienSO3B2A] [offsetB2A]]; simpl.
  apply pose_eq_if; simpl.
  - rewrite mremoverT_mconsrT. rewrite mremovecT_mconscT. auto.
  - f_equal. rewrite mtailc_mconsrT_mconscT_vconsT. rewrite vremoveT_vconsT. auto.
Qed.
  
Lemma pose2poseHom_poseHom2pose : forall A B (poseHomB2A : PoseHom A B),
    pose2poseHom (poseHom2pose poseHomB2A) = poseHomB2A.
Proof.
  intros. unfold poseHom2pose, pose2poseHom; simpl.
  destruct poseHomB2A as [poseHomMat poseHomSO3 poseHomRow4Zero]; simpl.
  apply poseHom_eq_if. simpl.
  rewrite meq_mconsrT_mremoverT_mtailr. f_equal; auto_vec.
  rewrite meq_mconscT_mremovecT_mtailc. auto.
Qed.

(** Translation transformation matrix for frame {B} respect to {A}, where p is the 
    origin point p of {B} respect to {A}. We denoted it with Trans(p) *)
Definition translMat4 {A} (offsetB2A : Point A) : smat 4 :=
  mconsrT (mconscT mat1 offsetB2A) (vconsT vzero 1).

(** Rotation transformation matrix for frame {B} respect to {A}, where orienB2A is the 
    orientation of {B} respect to {A}. We denoted it with Rot(k,θ), it means a 
    rotation operator that represents the rotation angle θ of axis k around the 
    origin. *)
Definition rotMat4 {A B} (orienB2A : Orien A B) : smat 4 :=
  mconsrT (mconscT orienB2A vzero) (vconsT vzero 1).

(** pose2poseHom has following relation:
    [R p] = [I p][R 0]
    [0 1]   [0 1][0 1], denoted as T = Trans(p) ⋅ Rot(k,θ) *)
Lemma pose2poseHom_eq_mmul_translMat4_rotMat4 : forall A B (poseB2A : Pose A B),
    let T : smat 4 := pose2poseHom poseB2A in
    let Transl : smat 4 := translMat4 (poseOffset poseB2A) in
    let Rot : smat 4 := rotMat4 poseB2A in
    T = Transl * Rot.
Proof.
  intros. unfold T,Transl,Rot. clear.
  destruct poseB2A as [[orienMatB2A orienSO3B2A] [offsetB2A]]. simpl.
  v2eALL orienMatB2A. subst. meq; try lra.
Qed.
