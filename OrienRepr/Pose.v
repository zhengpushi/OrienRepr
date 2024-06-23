(*
  Copyright 2023 Zhengpu Shi
  This file is part of OrienRepr. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Pose in 3D
  author    : Zhengpu Shi
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


Require Import AxisAngle.
Require Import EulerAngle.
(* Require Import Quaternion. *)
Require Export RotationMatrix3D.

Local Notation "a .x" := (a.1) (at level 25) : vec_scope.
Local Notation "a .y" := (a.2) (at level 25) : vec_scope.
Local Notation "a .z" := (a.3) (at level 25) : vec_scope.


(* ########################################################################### *)
(** * Pose representation of rigid-body 刚体位姿描述 *)

(** 坐标系{B}相对于坐标系{A}的位姿，由两部分组成：
   1. 坐标系{B}相对于{A}的姿态 R : smat 3
   2. 坐标系{B}的原点相对于{A}的平移矢量 p : vec 3 *)
Record Pose :=
  mkPose {
      poseOrien : smat 3;
      poseOffset : vec 3;
    }.

(** The condition of a Pose, i.e., it is well-defined  *)
Definition poseWd (pose : Pose) := SOnP (poseOrien pose).

Lemma poseOrien_inv_eq_trans : forall (pose : Pose),
    poseWd pose -> poseOrien pose\-1 = poseOrien pose\T.
Proof.
  intros. apply morth_imply_minv_eq_trans; auto.
  hnf in H. destruct H as [H1 H2]. auto.
Qed.

(* ======================================================================= *)
(** ** 坐标变换 *)

(** 坐标平移(translateate)，或称平移映射：
    设坐标系{B}和{A}具有相同的方位，但是原点不重合，用平移矢量offsetB2A描述
    {B}相对于{A}的位置，则任意点p在{A}中的坐标pA可由p在{B}中的坐标pB得到 *)
Definition translate (offsetB2A : vec 3) (pB : vec 3) : vec 3 := (pB + offsetB2A)%V.

(** 坐标旋转(rotation)，或称旋转映射：
    设坐标系{B}和{A}由共同的坐标原点，但两者的姿态不同，用旋转矩阵orienB2A描述
    {B}相对于{A}的姿态，则任意点p在{A}中的坐标pA可由p在{B}中的坐标pB得到 *)
Definition rotate (orienB2A : smat 3) (pB : vec 3) : vec 3 := orienB2A *v pB.

(** 一般刚体变换(transformation)：
    设坐标系{B}和{A}不但原点不重合，而且姿态也不相同，用位姿poseB2A描述
    {B}相对于{A}的位姿，则任意点p在{A}中的坐标pA可由p在{B}中的坐标pB得到 *)
Definition transform (poseB2A : Pose) (pB : vec 3) : vec 3 :=
  (poseOrien poseB2A *v pB + poseOffset poseB2A)%V.

(** 一般刚体变换的公式可以借由一个过渡坐标系{B}来得到 *)

(** 首先，分步骤进行详细推导 *)
Section transform_spec1.
  (* 假设有两个坐标系{A}和{B}，并且{B}相对于{A}的位姿是poseB2A，
    任意点p在{A}和{B}中的坐标分别为pA和pB *)
  Variable poseB2A : Pose.
  Variable pA pB : vec 3.

  (* 再假设有一个过渡坐标系{C}，使{C}的坐标原点与{B}的重合，而姿态与{A}的相同 *)
  Let poseB2C : Pose := mkPose (poseOrien poseB2A) vzero.
  Let poseC2A : Pose := mkPose mat1 (poseOffset poseB2A).

  (* 再设 p在{C}中的坐标为pC *)
  Variable pC : vec 3.

  (* 显然，如下关系式成立：
     1. pC可由对pB进行坐标旋转得到
     2. pA可由pC进行坐标平移得到 *)
  Hypotheses pC_eq_rotate : pC = rotate (poseOrien poseB2C) pB.
  Hypotheses pA_eq_translate : pA = translate (poseOffset poseC2A) pC.

  (* 证明 transform 函数的定义是合理的 *)
  Goal pA = transform poseB2A pB.
  Proof.
    rewrite pA_eq_translate. rewrite pC_eq_rotate.
    unfold translate, rotate, transform. simpl. auto.
  Qed.
End transform_spec1.

(* 写成一个引理 *)
Lemma transform_spec1 : forall (poseB2A : Pose) (pA pB pC : vec 3),
    let poseB2C : Pose := mkPose (poseOrien poseB2A) vzero in
    let poseC2A : Pose := mkPose mat1 (poseOffset poseB2A) in
    pC = rotate (poseOrien poseB2C) pB ->
    pA = translate (poseOffset poseC2A) pC ->
    pA = transform poseB2A pB.
Proof.
  intros. rewrite H0. rewrite H.
  unfold translate, rotate, transform. simpl. auto.
Qed.

(** 当姿态为零时，一般刚体变换等价于坐标平移 *)
Lemma transform_eq_translate : forall (poseB2A : Pose) (pB : vec 3),
    poseOrien poseB2A = mat1 ->
    transform poseB2A pB = translate (poseOffset poseB2A) pB.
Proof.
  intros. destruct poseB2A as [orien offset]. simpl in *. subst.
  unfold transform, translate. simpl. rewrite mmulv_1_l. auto.
Qed.

(** 当原点相同时，一般刚体变换等价于坐标旋转 *)
Lemma transform_eq_rotate : forall (poseB2A : Pose) (pB : vec 3),
    poseOffset poseB2A = vzero ->
    transform poseB2A pB = rotate (poseOrien poseB2A) pB.
Proof.
  intros. destruct poseB2A as [orien offset]. simpl in *. subst.
  unfold transform, rotate. simpl. rewrite vadd_0_r. auto.
Qed.


(** Example 3.1 (page 39) *)
Module ex_3_1.

  (* 两个坐标系{A}和{B}，刚开始{B}和{A}重合，然后{B}绕{A}的z轴转30度，
     然后沿{A}的x轴移动10个单位，并沿{A}的y轴移动5个单位。
     求{B}相对于{A}的位置向量和旋转矩阵 *)

  (* 定义{B}相对于{A}的位姿 *)
  Example orienB2A : smat 3 := Rz (deg2rad 30).
  Example offsetB2A : vec 3 := l2v [10;5;0].
  Example poseB2A : Pose := mkPose orienB2A offsetB2A.

  (* 假设p点在{B}中的坐标 *)
  Example pB : vec 3 := l2v [3;7;0].

  (* 求p点在{A}中的坐标 *)
  Example pA : vec 3 := transform poseB2A pB.

  (* 验证这些结果与教材上一致 *)

  (* 1. 先验证旋转矩阵的结果 *)
  Lemma orienB2A_eq :
    orienB2A =
      l2m [[(sqrt 3)/2; -1/2; 0]; [1/2; (sqrt 3)/2; 0]; [0; 0; 1]].
  Proof.
    cbn. replace (deg2rad 30) with (PI/6) by (cbv; ra).
    meq.
    (* Tips: 如何让 
       cos (PI * / ((R1 + R1) * (R1 + (R1 + R1)))) 
       自动化简为 cos (PI/6)，以便使用重写，从而自动证明 *)
    (* 目前只好先手动进行 *)
    - pose proof cos_PI6. cbv in H. rewrite <- H. f_equal. field.
    - pose proof sin_PI6. cbv in H.
      rewrite <- Ropp_mult_distr_l. rewrite <- H. f_equal. f_equal. field.
    - pose proof sin_PI6. cbv in H. rewrite <- H. f_equal. field.
    - pose proof cos_PI6. cbv in H. rewrite <- H. f_equal. field.
  Qed.

  (* 2. 对于pA的值，教材上给的是浮点数近似值，我们可以在OCaml中计算来比较 *)
  Example pA_value : list R := v2l pA.

  (* 首先抽取代码 *)
  Extraction "ocaml_test_pose_ex_3_1.ml" pA_value.
  
(* 运行结果如下，与教材一致：
   utop[1]> Coq_ex_3_1.pA_value;;
   - : float list = [9.09807621135331601; 12.5621778264910713; 0.] *)
  
End ex_3_1.

(** 三个坐标轴 *)
Inductive Axis := AxisX | AxisY | AxisZ.

(** Rotate around axis k by θ angle *)
Definition rotateByAxis (k : Axis) (theta : R) : smat 3 :=
  match k with
  | AxisX => Rx theta
  | AxisY => Ry theta
  | AxisZ => Rz theta
  end.


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


(* ======================================================================= *)
(** ** Homogeneous transformation *)

(** Homogeneous transformation matrix is a 4×4 matrix *)

(** The condition of a hom-trans-mat, i.e., it is well-defined  *)
Definition hommatWd (A : smat 4) :=
  (* the left-top 3×3 matrix belongs to SO(3) *)
  let Rmat := mremovecT (mremoverT A) in
  (* the bottom row is [0 0 0 1] *)
  let row4 := mtailr A in
  SOnP Rmat /\ row4 = vconsT vzero 1.

(** hommatWd A -> |A| = 1, i.e.,
        [r11 r12 r13 | v1]       [r11 r12 r13]
    det [r21 r22 r23 | v2] = det [r21 r22 r23]
        [r31 r32 r33 | v3]       [r31 r32 r33]
        [  0   0   0 |  1] *)
Lemma hommatWd_mdet_eq1 : forall (A : smat 4), hommatWd A -> |A| = 1.
Proof.
  intros. hnf in H. destruct H as [[Horth Hdet1] H2].
  assert (A = mconsrT (mremoverT A) (vconsT vzero 1)).
  { rewrite (meq_mconsrT_mremoverT_mtailr A). f_equal; auto. auto_vec. }
  rewrite H.
  assert (|mconsrT (mremoverT A) (vconsT vzero 1)| = |mremovecT (mremoverT A)|).
  rewrite mdet_mconsrT_vconsT_vzero_1_eq. auto.
  rewrite H0. unfold mdet. auto.
Qed.

(** hommatWd A -> minvtble A *)
Lemma hommatWd_minvtble : forall (A : smat 4), hommatWd A -> minvtble A.
Proof.
  intros. apply minvtble_iff_mdet_neq0. rewrite hommatWd_mdet_eq1; auto.
Qed.

(** Convert Pose to Hom-trans-mat, where poseB2A is pose of {B} respect to {A} *)
Definition pose2hommat (poseB2A : Pose) : smat 4 :=
  mconsrT (mconscT (poseOrien poseB2A) (poseOffset poseB2A)) (vconsT vzero 1).

(** Convert Hom-trans-mat to Pose, where hommatB2A is hom-trans-mat of {B} respect
    to {A} *)
Definition hommat2pose (hommatB2A : smat 4) : Pose :=
  mkPose
    (mremovecT (mremoverT hommatB2A))
    (vremoveT (mtailc hommatB2A)).

(** hommat2pose (pose2hommat poseB2A) = poseB2A *)
Lemma hommat2pose_pose2hommat : forall (poseB2A : Pose),
    hommat2pose (pose2hommat poseB2A) = poseB2A.
Proof.
  intros. unfold hommat2pose, pose2hommat; simpl.
  destruct poseB2A as [poseOrienB2A poseOffsetB2A]; simpl. f_equal.
  - rewrite mremoverT_mconsrT. rewrite mremovecT_mconscT. auto.
  - rewrite mtailc_mconsrT_mconscT_vconsT. rewrite vremoveT_vconsT. auto.
Qed.

Lemma pose2hommat_hommat2pose : forall (hommatB2A : smat 4),
    hommatWd hommatB2A ->
    pose2hommat (hommat2pose hommatB2A) = hommatB2A.
Proof.
  intros. unfold hommat2pose, pose2hommat; simpl.
  rewrite meq_mconsrT_mremoverT_mtailr. f_equal; auto.
  rewrite meq_mconscT_mremovecT_mtailc. auto.
  hnf in H. destruct H. rewrite H0. veq.
Qed.

Lemma pose2hommat_keep_wd : forall (pose : Pose),
    poseWd pose -> hommatWd (pose2hommat pose).
Proof.
  intros. unfold hommatWd, poseWd, pose2hommat in *. auto_vec.
Qed.

Lemma hommat2pose_keep_wd : forall (T : smat 4),
    hommatWd T -> poseWd (hommat2pose T).
Proof.
  intros. unfold hommatWd, poseWd, hommat2pose in *. simpl. tauto.
Qed.

  
(** 齐次变换矩阵表示了坐标平移与坐标旋转的复合，可将其分解为两个矩阵的乘积 *)
Section hommat_eq.
  
  (** Translation transformation matrix for frame {B} respect to {A}, where offsetB2A
      is the origin point p of {B} respect to {A} *)
  Definition translMat (offsetB2A : vec 3) : smat 4 :=
    mconsrT (mconscT mat1 offsetB2A) (vconsT vzero 1).

  (** Rotation transformation matrix for frame {B} respect to {A}, where orienB2A is 
      the orientation of {B} respect to {A}. We denoted it with Rot(k,θ), it means a 
      rotation operator that represents the rotation angle θ of axis k around the 
      origin. *)
  Definition rotateMat (orienB2A : smat 3) : smat 4 :=
    mconsrT (mconscT orienB2A vzero) (vconsT vzero 1).

  (** Hom-trans-mat satisfy the following equation:
    [R p] = [I p][R 0]
    [0 1]   [0 1][0 1], denoted as T = Trans(p) ⋅ Rot(k,θ) *)
  Lemma hommat_eq_mmul_translMat_rotMat : forall (poseB2A : Pose),
      let T : smat 4 := pose2hommat poseB2A in
      let Transl : smat 4 := translMat (poseOffset poseB2A) in
      let Rot : smat 4 := rotateMat (poseOrien poseB2A) in
      T = Transl * Rot.
  Proof.
    intros. unfold T,Transl,Rot. clear.
    destruct poseB2A as [poseOrienB2A poseOffsetB2A]. simpl.
    v2eALL poseOrienB2A. meq; try lra.
  Qed.
End hommat_eq.


(* ########################################################################### *)
(** * 运动算子 *)

(* 齐次变换矩阵 ${}^A_B T$ 有多种作用：
   1. 表示同一点在两个坐标系{B}和{A}中的映射关系：${}^A p = {}^A_B T {}^B p$，见(3-16)
   2. 描述坐标系{B}相对于另一个坐标系{A}的位姿，见例3.3
   3. 还可用来作为点的运动算子 *)

(* 在坐标系{A}中，点的初始位置是 ${}^Ap_1$，经平移或旋转后到达位置 ${}^Ap_2$。
   下面讨论从 ${}^Ap_1$ 到 ${}^Ap_2$ 的运动算子。*)

(* ======================================================================= *)
(** ** 平移算子 *)

(** 在一个坐标系{A}中，移动矢量${}^Ap$，其对应的平移算子 Transl(p) 为 *)
Definition Transl (p : vec 3) : smat 4 :=
  mconsrT (mconscT mat1 p) (vconsT vzero 1).

(* 平移算子的使用: p_2 = Transl(p) * p_1 *)

(* ======================================================================= *)
(** ** 旋转算子 *)

(* 有两种表示方法：
   1. 用 3×3 的旋转矩阵R表示
      将旋转矩阵 R 作为旋转算子，于是
      p_2 = R * p_1，此处点的坐标是3维的。
      注意，旋转矩阵R作为算子来解释时，不带上下标，因为是在同一个坐标系下。
   2. 用 4×4 的齐次变换矩阵 Rot(k,θ) 表示
      用Rot(k,θ)作为旋转算子，明确的给出旋转轴k和转角θ, 于是 
      p_2 = Rot(k,θ) * p_1，此处点的坐标是4维的。
*)
Section rotate_operator.

  (** 绕k轴旋转θ角的齐次旋转矩阵，或旋转算子 *)
  Definition RotAxis (k : Axis) (theta : R) : smat 4 :=
    mconsrT (mconscT (rotateByAxis k theta) vzero) (vconsT vzero 1).
End rotate_operator.

(* ======================================================================= *)
(** ** 运动算子的一般形式 *)

(* 在坐标系{A}中，点p经过转动和平移，令其前、后的位置为${}^Ap_1$和${}^Ap_2$，则两者的
   关系可用齐次变换T来表示：
   {}^Ap_2 = T {}^Ap_1
   当齐次变换T作为算子使用时，不带上下标。*)

(* 质点p在坐标系中的运动轨迹为时间t的函数 ${}^Ap(t)$，初始位置为${}^Ap(0)$，则质点p在
   坐标系{A}中的运动轨迹可用齐次变换 T(t)来表示：
   {}^Ap(t) = T(t) {}^Ap(0) *)

(* 例3.4：在{A}中，点p的运动轨迹如下：初始位置 ${}^Ap_1=[3 7 0]^T$，绕z轴旋转30度，
   沿x轴平移10，沿y轴平移5。求运动后的位置${}^Ap_2$。*)
Module ex_3_4.
  Example p1 : vec 3 := l2v [3;7;0].
  Example p2 :=
    let T1 := RotAxis AxisZ (deg2rad 30) in
    let T2 := Transl (l2v [10;0;0]) in
    let T3 := Transl (l2v [0;5;0]) in
    (T3 * T2 * T1) *v (e2h p1).

    (* 对于p2的值，教材上给的是浮点数近似值，我们可以在OCaml中计算来比较 *)
  Example p2_value : list R := v2l p2.

  (* 首先抽取代码 *)
  Extraction "ocaml_test_pose_ex_3_4.ml" p2_value.
  
(* 运行结果如下，与教材一致：
   utop[1]> Coq_ex_3_4.p2_value;;
   - : float list = [9.09807621135331601; 12.5621778264910713; 0.; 1.] *)
End ex_3_4.


(* ########################################################################### *)
(** * 变换矩阵的运算 *)

(* ======================================================================= *)
(** ** 变换矩阵相乘 *)

(** 根据{B}相对于{A}的变换transB2A，以及{C}相对于{B}的变换transC2B，计算{C}相对于{A}
    的复合变换矩阵 transC2A *)
Definition transComp (transB2A transC2B : smat 4) : smat 4 := transB2A * transC2B.

(** transComp的外延性，即，它变换了一个点在不同坐标系下的坐标 *)
Lemma transComp_spec : forall (transB2A transC2B : smat 4) (pA pB pC : vec 4),
    pA = transB2A *v pB ->
    pB = transC2B *v pC -> 
    pA = (transComp transB2A transC2B) *v pC.
Proof.
  intros. rewrite H,H0. unfold transComp. rewrite mmulv_assoc. auto.
Qed.

(** 复合变换矩阵的分解形式
    {}^A_CT = {}^A_BT{}^B_CT = [{}^A_BR{}^B_CR  {}^A_BR{}^Bp_{C_0} + {}^Ap_{B_0}]
                               [0               1                               ] *)
Definition transComp2 (transB2A transC2B : smat 4) : smat 4 :=
  let poseB2A := hommat2pose transB2A in
  let poseC2B := hommat2pose transC2B in
  let R_B2A := poseOrien poseB2A in
  let R_C2B := poseOrien poseC2B in
  let p_B2A := poseOffset poseB2A in
  let p_C2B := poseOffset poseC2B in
  mconsrT
    (mconscT (R_B2A * R_C2B) (R_B2A *v p_C2B + p_B2A)%V)
    (vconsT vzero 1).

(** transComp2与transComp相等 *)
Lemma transComp2_eq : forall (transB2A transC2B : smat 4),
    hommatWd transB2A -> hommatWd transC2B ->
    transComp2 transB2A transC2B = transComp transB2A transC2B.
Proof.
  intros.
  unfold transComp2, transComp.
  v2eALL transB2A. v2eALL transC2B. apply m2l_inj; cbv.
  destruct H as [H1 H2]. destruct H0 as [H3 H4].
  apply v2l_eq in H2. cbv in H2. inv H2.
  apply v2l_eq in H4. cbv in H4. inv H4.
  list_eq; try lra.
Qed.

(* 相对于固定参考系vs运动坐标系，左乘vs右乘？
   1. 变换顺序是从右至左时，运动是相对固定参考系而言的（左乘规则）
   2. 变换顺序是从左至右时，运动是相对运动参考系而言的（右乘规则）
   此处的“从左到右，从右到左”是指如何安排各次旋转对应的矩阵。*)

(* 例如：在例3.3中，
   先{B}绕{A}的zA轴转90度，即Rot(z,pi/2)，
   再绕{A}的yA轴转90度，即Rot(y,pi/2)，
   再相对{A}平移[1 -3 4]^T，记 Transl(1 -3 4)。*)
Section ex_3_3.
  Let Tr := Transl (l2v [1;-3;4]).
  Let Roty := RotAxis AxisY (deg2rad 90).
  Let Rotz := RotAxis AxisZ (deg2rad 90).

  (* 求{B}相对于{A}的位姿tBA *)
 
 (* 1. 按照绕固定参考坐标系{A}来理解，则使用左乘从右到左的逐个使用 Rotz, Roty, Tr。 *)
  Let tBA := Tr * Roty * Rotz.
  
  (* 2. 按照绕运动参考系{B}来理解，
     首先{B}与{A}是重合的，从左到右依次进行以下变换：
     首先{B}相对于{A}移动 1i-3j+4k，然后绕yB转90度，然后绕zB转90度。
     此时，使用右乘，从左到右的逐个使用 Tr, Roty, Rotz *)
  Let tBA' := Tr * Roty * Rotz.
  
End ex_3_3.

(* ======================================================================= *)
(** ** 变换矩阵求逆 *)

(* 已知{B}相对于{A}的齐次变换矩阵 ${}^A_BT$，求{A}相对于{B}的齐次变换矩阵${}^B_AT$。
   这是变换矩阵求逆的问题。
   一种方法是直接对4×4矩阵求逆；另一种是利用性质先推导出一个简便的公式。*)

Definition transInv (transB2A : smat 4) : smat 4 :=
  let poseB2A := hommat2pose transB2A in
  let R := poseOrien poseB2A in
  let p := poseOffset poseB2A in
  mconsrT
    (mconscT (R\T) (- (R\T) *v p)%V)
    (vconsT vzero 1).

Module transInv_spec_manual.
  Section transInv_spec.
    Variable transB2A : smat 4.
    Let transA2B := transInv transB2A.
    Hypotheses transB2A_hom : hommatWd transB2A.
    Let poseB2A : Pose := hommat2pose transB2A.
    Let R_B2A : smat 3 := poseOrien poseB2A.
    Let p_B2A : vec 3 := poseOffset poseB2A.
    Let R_A2B : smat 3 := R_B2A\-1.
    Variable p_A2B : vec 3.
    Hypotheses p_B2B_zero : transform (mkPose R_A2B p_A2B) p_B2A = vzero.

    Lemma poseB2A_wd : poseWd poseB2A.
    Proof. unfold poseB2A. apply hommat2pose_keep_wd. apply transB2A_hom. Qed.
    
    Goal transA2B = pose2hommat (mkPose R_A2B p_A2B).
    Proof.
      unfold transA2B, transInv, pose2hommat. f_equal. f_equal.
      - unfold R_A2B. replace (R_B2A\-1) with (R_B2A\T); auto.
        unfold R_B2A. rewrite poseOrien_inv_eq_trans; auto. apply poseB2A_wd.
      - simpl.
        assert (p_A2B = - R_A2B *v p_B2A)%V.
        { pose proof p_B2B_zero. unfold transform in H. simpl in H.
          apply vadd_eq0_imply_vopp_l in H. auto. }
        rewrite H. f_equal. f_equal. unfold R_A2B. unfold R_B2A.
        rewrite poseOrien_inv_eq_trans; auto. apply poseB2A_wd.
    Qed.
  End transInv_spec.
End transInv_spec_manual.

Lemma transInv_eq_inv : forall transB2A : smat 4,
    hommatWd transB2A ->
    transInv transB2A = transB2A \-1.
Proof.
  intros. symmetry. apply mmul_eq1_imply_minvAM_l.
  unfold transInv, hommatWd in *. destruct H as [[Horth Hdet1] Htail].
  replace transB2A with
    (mconsrT
       (mconscT (mremoverT (mremovecT transB2A)) (vremoveT (mtailc transB2A)))
       (vconsT (vremoveT (mtailr transB2A)) (vtail (mtailr transB2A)))) at 1.
  all: rewrite Htail.
  rewrite mmul_mconsrT_mconscT_vconsT.
  - apply mconsrT_mconscT_vconsT_imply_mat1; simpl; auto_vec.
    + apply morth_iff_mul_trans_r; auto.
    + rewrite mmulv_vopp. rewrite <- mmulv_assoc.
      rewrite mremoverT_mremovecT_eq_mremovecT_mremoverT.
      rewrite morth_iff_mul_trans_r in Horth. rewrite Horth. auto_vec.
    + ring.
  - auto_vec.
    symmetry. rewrite meq_mconsrT_mremoverT_mtailr at 1. f_equal; auto.
    rewrite mremoverT_mremovecT_eq_mremovecT_mremoverT.
    rewrite meq_mconscT_mremovecT_mtailc at 1. auto.
Qed.

Lemma transInv_spec : forall (transB2A : smat 4) (pA pB : vec 4),
    hommatWd transB2A ->
    pA = transB2A *v pB ->
    pB = transInv transB2A *v pA.
Proof.
  intros. rewrite H0. rewrite transInv_eq_inv; auto.
  rewrite <- mmulv_assoc. rewrite mmul_minvAM_l. rewrite mmulv_1_l. auto.
  apply hommatWd_minvtble; auto.
Qed.

Module ex_3_5.
  (* 两个坐标系{A}和{B}，用transB2A表示：{B}绕zA转30度，再沿xA移动4，沿yA移动3,
     求transA2B，并说明它表示的变换 *)
  Example transB2A := Transl (l2v [4;3;0]) * RotAxis AxisZ (deg2rad 30).
  Example transA2B := transInv transB2A.

  (* 等价的变换：表示坐标系首先反向平移，然后反向旋转 *)
  Example transA2B' := RotAxis AxisZ (deg2rad (-30)) * Transl (l2v [-4;-3;0]).

  Example transB2A_value := m2l transB2A.
  Example transA2B_value := m2l transA2B.
  Example transA2B'_value := m2l transA2B'.
  Extraction "ocaml_test_pose_ex_3_5.ml"
    transB2A_value transA2B_value transA2B'_value.
  (* 
utop[1]> Coq_ex_3_5.transB2A_value;;
- : float list list =
[[0.866025403784438708; -0.499999999999999944; 0.; 4.];
 [0.499999999999999944; 0.866025403784438708; 0.; 3.]; 
 [0.; 0.; 1.; 0.];
 [0.; 0.; 0.; 1.]]

utop[2]> Coq_ex_3_5.transA2B_value;;
- : float list list =
[[0.866025403784438708; 0.499999999999999944; 0.; -4.96410161513775439];
 [-0.499999999999999944; 0.866025403784438708; 0.; -0.598076211353316234];
 [0.; 0.; 1.; 0.]; 
 [0.; 0.; 0.; 1.]] 

utop[3]> Coq_ex_3_5.transA2B'_value;;
- : float list list =
[[0.866025403784438708; 0.499999999999999944; 0.; -4.96410161513775439];
 [-0.499999999999999944; 0.866025403784438708; 0.; -0.598076211353316234];
 [0.; 0.; 1.; 0.]; [0.; 0.; 0.; 1.]]
*)
End ex_3_5.

(* ======================================================================= *)
(** ** 变换方程 *)

Section trans_equation.
  (* {B} 基座坐标系（又称基座框） base
     {W} 腕坐标系     wrist
     {T} 工作坐标系   tool
     {S} 工作站坐标系 station
     {G} 目标坐标系   goal *)

  Variable tSB : smat 4.        (* {S}相对于{B}的位姿 *)
  Variable tGS : smat 4.
  Variable tWB : smat 4.
  Variable tTW : smat 4.
  Variable tTG : smat 4.

  (* 已知4个位姿时，可计算 tTG *)
  Hypotheses H1 : tTG = tGS\-1 * tSB\-1 * tWB * tTW.
  (* 根据空间尺寸链形式，可得变换方程 *)
  Hypotheses H2 : tWB * tTW = tSB * tGS * tTG.

  (* 变换方程中的任一变换矩阵都可用其余的变换矩阵来表示 *)
  Goal hommatWd tTW ->
       tWB = tSB * tGS * tTG * (tTW\-1).
  Proof.
    intros. rewrite <- H2. rewrite mmul_assoc.
    rewrite mmul_minvAM_r, mmul_1_r; auto.
    apply hommatWd_minvtble; auto.
  Qed.
End trans_equation.

(* ======================================================================= *)
(** ** 刚体变换群 *)

(* 变换矩阵T完全由位置矢量p和旋转矩阵R所决定，
   因此，任一刚体的位姿由 (p,R): p∈R^3, R∈SO(3) 所决定。
   由矩阵乘法可定义刚体变换群SE(3) *)

(* 定义：刚体变换群SE(3)定义为乘积空间 R^3 × SO(3)，即
   SE(3) = {(p,R): p∈R^3, R∈SO(3)} = R^3 × SO(3)
   也称SE(3)为三维空间的特殊欧式群(special euclidean group)。
   可证明它满足群公理。 *)

(* 刚体变换群SE(3)和旋转群SO(3)都是光滑流形，且矩阵乘法运算和求逆运算都是光滑映射，
   都构成李群，均为不可交换李群。推广到n维空间中，则有：
   SE(n) = {(p,R): p∈R^n, R∈SO(n)} = R^n × SO(n)
   当n=3时，SE(3)表示空间运动，用齐次变换矩阵表示，单位元为I4；
   当n=2时，SE(2)表示刚体平面运动，单位元为I3。 *)

(* SE(3)的子群还包含圆柱运动群。略 *)


(* ########################################################################### *)
(** * 欧拉角与RPY角 *)

(* 下面介绍欧拉角和RPY角方法，将旋转矩阵用3个独立的参数表示 *)

(* ======================================================================= *)
(** ** 绕固定轴x-y-z旋转（RPY角） *)

(* RPY角是描述船舶在海上航行时姿态的一种方法。
   船的行驶方向取为z轴的方向，绕z轴的旋转称为回转(roll)，记为α角；
   船右侧为y轴的方向，绕y轴的...俯仰(pitch)，记为β角；
   指向天空的是x轴的方向，绕x轴的...偏转(yaw)，记为γ角。
   在机器人、飞行器上，有类似的规定方法。习惯上，称这种方法为RPY角方法。 *)

(* 绕固定轴x-y-z旋转的RPY角法，描述坐标系{B}的方法的规则如下：
   {B}的初始方位与参考系{A}重合。首先将{B}绕xA转γ角，再绕yA转β角，再绕zA转α角。
   因为三次旋转都是相对固定坐标系{A}的，按照“从右到左”的原则，则相应的旋转矩阵
   R_xyz(γ,β,α) = Rz(α)Ry(β)Rx(γ) *)
Section RPY.
  Variable α β γ : R.
  Notation sα := (sin α). Notation cα := (cos α).
  Notation sβ := (sin β). Notation cβ := (cos β).
  Notation sγ := (sin γ). Notation cγ := (cos γ).

  (* 记作 Space-x-y-z（注意，需要从右到左的作用，即 Rz*Ry*Rz) *)
  Let Sxyz : smat 3 :=
        l2m [[cα * cβ; cα * sβ * sγ - sα * cγ; cα * sβ * cγ + sα * sγ];
             [sα * cβ; sα * sβ * sγ + cα * cγ; sα * sβ * cγ - cα * sγ];
             [- sβ; cβ * sγ; cβ * cγ]]%R.

  (* RPY，等于 S123，即绕 xA,yA,zA 轴旋转 γ,β,α角，等于从右到左的乘积 Rz*Ry*Rx *)
  Goal Sxyz = S123 γ β α.
  Proof. meq; ring. Qed.

  (* RPY，等于B321，即绕 zB,yB,xB 轴旋转 α,β,γ角，等于从左到右的乘积 Rz*Ry*Rx *)
  Goal Sxyz = B321 α β γ.
  Proof. meq; ring. Qed.
End RPY.

(* RPY角的反解，略 *)

(* ======================================================================= *)
(** ** z-y-x的欧拉角 *)

(* 注，所有的欧拉角都是绕运动轴的 *)

(* z-y-x欧拉角法，描述坐标系{B}的方位的规则为：
   {B}的初始方位与参考系{A}重合。首先将{B}绕zB轴转α角，在绕yB轴转β角，再绕xB角转γ角。
   因为所有的转动都是相对运动坐标系进行，根据“从左到右”的原则来安排歌词旋转对应的矩阵
   R_zyx(α,β,γ) = Rz(α)Ry(β)Rx(γ) *)
Section zyx.
  Let Bzyx (α β γ : R) : smat 3 := Rz α * Ry β * Rx γ.

  (* 这一结果与绕固定轴x-y-z旋转的结果完全相同。这是因为：
     若绕固定轴旋转的顺序与绕运动轴旋转的顺序相反，并且旋转的角度也对应相对，则所得到的
     变换矩阵是相同的。*)

  Goal forall α β γ, Bzyx α β γ = B321 α β γ.
  Proof. intros; meq; ring. Qed.
End zyx.

(* ======================================================================= *)
(** ** z-y-z的欧拉角 *)

Section zyz.
  Let Bzyz (α β γ : R) : smat 3 := Rz α * Ry β * Rz γ.

  Goal forall α β γ, Bzyz α β γ = B323 α β γ.
  Proof. intros; meq; ring. Qed.
End zyz.

(* 总结：
   1. RPY角方法中是相对固定坐标系旋转的，而欧拉角方法中是相对运动坐标系旋转的。
   2. 总共有24种排列，其中12种为绕固定轴RPY设定法，12种为欧拉角设定法。
   3. 因为RPY角与欧拉角对偶，实际上只有12种不同的旋转矩阵。*)


(* ########################################################################### *)
(** * 旋转变换通式 *)

(* 讨论绕过原点的任意轴k旋转θ角的变换矩阵 *)

(* ======================================================================= *)
(** ** 旋转变换通式，即轴角公式 *)

(** 绕任意轴的旋转公式 *)
Definition Rot (k : vec 3) (θ : R) : smat 3 :=
  let s := sin θ in
  let c := cos θ in
  let vc := (1 - c)%R in
  l2m [[k.x * k.x * vc + c; k.y * k.x * vc - k.z * s; k.z * k.x * vc + k.y * s];
       [k.x * k.y * vc + k.z * s; k.y * k.y * vc + c; k.z * k.y * vc - k.x * s];
       [k.x * k.z * vc - k.y * s; k.y * k.z * vc + k.x * s; k.z * k.z * vc + c]]%R.

Lemma Rot_eq_Rx : forall θ, Rot (l2v [1;0;0]) θ = Rx θ.
Proof. intros. meq; ring. Qed.

Lemma Rot_eq_Ry : forall θ, Rot (l2v [0;1;0]) θ = Ry θ.
Proof. intros. meq; ring. Qed.

Lemma Rot_eq_Rz : forall θ, Rot (l2v [0;0;1]) θ = Rz θ.
Proof. intros. meq; ring. Qed.

(** Rot 等于 aa2matM（这是在 AxisAngle 中推导得到的结果） *)
Lemma Rot_eq_aa2matM : forall k θ, Rot k θ = aa2matM (mkAA θ k).
Proof. intros. v2e k. meq; ra. Qed.

(** 当k单位向量时，Rot 等于 aa2mat (罗德里格斯公式)，计算更高效 *)
Lemma Rot_eq_aa2mat : forall k θ, vunit k -> Rot k θ = aa2mat (mkAA θ k).
Proof.
  intros. pose proof (v3unit_sqr_x k H).
  v2e k. cbv in H0. meq; ra. all: rewrite H0; ra.
Qed.

Example ex_3_6 := m2l (Rot (l2v [1/sqrt 3; 1/sqrt 3; 1/sqrt 3]) (deg2rad 120)).
Extraction "ocaml_test_pose_ex_3_6.ml" ex_3_6.
(* val ex_3_6 : float list list =
  [[3.33066907387546962e-16; 0.; 1.00000000000000022];
   [1.00000000000000022; 3.33066907387546962e-16; 0.];
   [0.; 1.00000000000000022; 3.33066907387546962e-16]] *)

(* Rot的推导 *)
Section Rot_spec.
  (* 任给过原点的单位矢量 k 作为旋转轴，以及转角θ，求旋转矩阵 R(k,θ) *)
  Variable k : vec 3.
  Variable θ : R.

  (* 即，求{B}相对于{A}的姿态。
     定义辅助坐标系{A'}和{B'}，分别与{A}和{B}固连，
     但是，{A'}与{B'}的z轴与k重合，并且旋转之前{B'}与{A'}重合。因此：
     tA'A = tB'B = ..
 *)
End Rot_spec.

(* ======================================================================= *)
(** ** 等效转轴和等效转角 *)

(* 反向问题是，根据旋转矩阵求等效转轴 k 与等效转角 θ *)

(* 给定旋转矩阵
       [nx ox ax]
   R = [ny oy ay]
       [nz oz az]，使其等于Rot矩阵，则
   1. 将矩阵主对角线元素相加，得
      nx+oy+nz = (kx^2+ky^2+kz^2)Versθ + 3cosθ = 1 + 2 * cosθ
      于是，cosθ = 1/2 (nx + oy + az - 1)
   2. 再将方程两边矩阵的非对角线元素成对相减得
      oz - ay = 2 * kx * sinθ
      ax - nz = 2 * ky * sinθ
      ny - ox = 2 * kz * sinθ
      若将以上方程两边平方后相加，的
      (oz-ay)^2 + (ay-nz)^2 + (ny-ox)^2 = 4*(sinθ)^2
      可解得 
             sinθ = ±(1/2) sqrt((oz-ay)^2 + (ax-nz)^2 + (ny-ox)^2)
             tanθ = ±\frac{sqrt((oz-ay)^2 + (ax-nz)^2 + (ny-ox)^2)}{nx+oy+ax-1}
      另外，k可直接由上面的方程组得到
        kx=(oz-ay)/(2*sinθ), ky=(ax-nz)/(2*sinθ), kz=(ny-ox)/(2*sinθ) *)

(** cosθ of rotation matrix A *)
Definition getRotAngleCos (A : smat 3) : R :=
  (1/2) * (A.11 + A.22 + A.33 - 1).

(** sinθ of rotation matrix A *)
Definition getRotAngleSin (A : smat 3) : R :=
  let n := A&1 in
  let o := A&2 in
  let a := A&3 in
  (1/2) * sqrt ((o.z-a.y)² + (a.x-n.z)² + (n.y-o.x)²).

(** tanθ of rotation matrix A *)
Definition getRotAngleTan (A : smat 3) : R :=
  let n := A&1 in
  let o := A&2 in
  let a := A&3 in
  (sqrt ((o.z-a.y)² + (a.x-n.z)² + (n.y-o.x)²)) / (n.x+o.y+a.z-1).

(** Rotation axis of rotation matrix A *)
Definition getRotAxis (A : smat 3) (θ : R) : vec 3 :=
  let n := A&1 in
  let o := A&2 in
  let a := A&3 in
  let s2 := (2 * sin θ)%R in
  l2v [(o.z-a.y)/s2; (a.x-n.z)/s2; (n.y-o.x)/s2].


(* 计算转轴和转角时的注意事项：
   1. 多值性：k和θ的值不是唯一的。例如(-k,-θ)和(k,θ)对应了同样的矩阵。
      另外，(k,θ+n*2π) (其中n为整数) 和(k,θ)也对应了同一个旋转矩阵。
      因此，一般选择θ在[0,π)之间。
   2. 病态情况：当θ很小时，计算k的公式中的分子和分母都很小，转轴难以确定。
      当θ接近0度和180度时，转轴完全不能确定。需要寻求另外的方法求解。*)

Module ex_3_7.
  Example tBA := Ry (deg2rad 90) * Rz (deg2rad 90).
  
  Example cosTheta := getRotAngleCos tBA.
  Example sinTheta := getRotAngleSin tBA.
  Example tanTheta := getRotAngleTan tBA.

  Example theta1 := acos cosTheta.
  Example theta2 := asin sinTheta.
  Example theta3 := atan tanTheta.

  Example axis1 := v2l (getRotAxis tBA theta1).
  Example axis2 := v2l (getRotAxis tBA theta2).
  Example axis3 := v2l (getRotAxis tBA theta3).
End ex_3_7.
Extraction "ocaml_test_pose_ex_3_7.ml" ex_3_7.


(* ======================================================================= *)
(** ** 齐次变换通式 *)

(* 可以证明，任何一组绕过原点的轴线的复合转动总是等价于绕某一过原点的轴线的转动
   R(k,θ)，这是欧拉定理 *)
