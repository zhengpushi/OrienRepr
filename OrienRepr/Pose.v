(*
  Copyright 2023 ZhengPu Shi
  This file is part of OrienRepr. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Pose in 3D
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

  Section ex_3_1.
    (* 两个坐标系{A}和{B}，刚开始{B}和{A}重合，然后{B}绕{A}的z轴转30度，
     然后沿{A}的x轴移动10个单位，并沿{A}的y轴移动5个单位。
     求{B}相对于{A}的位置向量和旋转矩阵 *)

    (* 定义{B}相对于{A}的位姿 *)
    Let orienB2A : smat 3 := Rz (deg2rad 30).
    Let offsetB2A : vec 3 := l2v [10;5;0].
    Let poseB2A : Pose := mkPose orienB2A offsetB2A.

    (* 假设p点在{B}中的坐标 *)
    Let pB : vec 3 := l2v [3;7;0].

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

  End ex_3_1.

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

(** ** 平移算子 *)

(** 在一个坐标系{A}中，移动矢量${}^Ap$，其对应的平移算子 Transl(p) 为 *)
Definition Transl (p : vec 3) : smat 4 :=
  mconsrT (mconscT mat1 p) (vconsT vzero 1).

(* 平移算子的使用: p_2 = Transl(p) * p_1 *)

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
  Definition Rot (k : Axis) (theta : R) : smat 4 :=
    mconsrT (mconscT (rotateByAxis k theta) vzero) (vconsT vzero 1).
End rotate_operator.

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
  Let p1 : vec 3 := l2v [3;7;0].
  Example p2 :=
    let T1 := Rot AxisZ (deg2rad 30) in
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

Section ex_3_3.
  Let T1 := Transl (l2v [1;-3;4]).
  Let T2 := Rot AxisY (deg2rad 90).
  Let T3 := Rot AxisZ (deg2rad 90).

  Goal T2 = l2m [[0;0;1;0];
                 [0;1;0;0];
                 [-1;0;0;0];
                 [0;0;0;1]].
  Proof.
  Abort.
End ex_3_3.


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

(** 齐次变换(transformation)：
    设坐标系{B}和{A}不但原点不重合，而且姿态也不相同，用位姿poseB2A描述
    {B}相对于{A}的位姿，则任意点p在{A}中的坐标pA可由p在{B}中的坐标pB得到 *)
Definition homTrans {A B} (poseB2A : Pose A B) (pB : Point B)
  : Point A :=
  mkPoint (poseB2A *v pB + poseOffset poseB2A)%V.

(** 一般刚体变换的公式可以借由一个过渡坐标系{B}来得到 *)

(* 首先，分步骤进行详细推导 *)
Section trans_spec1.
  (* 假设有两个坐标系{A}和{B}，并且{B}相对于{A}的位姿是poseB2A，
    任意点p在{A}和{B}中的坐标分别为pA和pB *)
  Variable A B : Frame.
  Variable poseB2A : Pose A B.
  Variable pA : Point A.
  Variable pB : Point B.

  (* 再假设有一个过渡坐标系{C}，使{C}的坐标原点与{B}的重合，而姿态与{A}的相同 *)
  Variable C : Frame.
  Let poseB2C : Pose C B := mkPose (mkOrien poseB2A) (mkPoint vzero).
  Let poseC2A : Pose A C := mkPose (mkOrien mat1) (poseOffset poseB2A).

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
    let poseB2C : Pose C B := mkPose (mkOrien poseB2A) (mkPoint vzero) in
    let poseC2A : Pose A C := mkPose (mkOrien mat1) (poseOffset poseB2A) in
    pC = rotate poseB2C pB ->
    pA = transl poseC2A pC ->
    pA = trans poseB2A pB.
Proof.
  intros. rewrite H0. rewrite H.
  unfold transl, rotate, trans. simpl. auto.
Qed.

(** 当姿态为零时，一般刚体变换等价于坐标平移 *)
Lemma trans_eq_transl : forall A B (poseB2A : Pose A B) (pB : Point B),
    poseOrien poseB2A = mkOrien mat1 ->
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

(**   *)
Check h2e.
(* ======================================================================= *)
(** ** Test *)

？

(* --------------------------------------------------------------- *)
(* Definitions of Euler Angles and it's Rotation 
  5.2.1 ~ 5.2.2

  1. We define the Euler Angles according it's most commonly used definition 
    method.
  2. We also show the singularities of Euler Angles at two moments.
    (1). from formula (5.6), we guess that there exist singularity.
    (2). Given different value to θ in formula (5.9), we get different solution 
      directly. A more strong evidence.
  3. We give the final rotation matrix under this definition of Euler Angles.
 *)
Module EA_RotM.

  (* We will use the basic rotaiton matrix here *)
  Import BasicRotMat.

  (** WE DON't USE THE DEFINITIONS WITH TIME, because this is not something 
    that must be done now. And it will increase the complexicity in other 
    related module, like Singularity-Verification below.
    &&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&& **)
  
  (*
  (* Euler angles over time *)
  Parameter f_ψ : R -> R.   (* yaw angle, rotated by X axis *)
  Parameter f_θ : R -> R.   (* pitch angle, rotated by Y axis *)
  Parameter f_φ : R -> R.   (* roll angle, rotated by Z axis *)

  (* Euler angle rates over time *)
  Parameter f_φ' : R -> R.
  Parameter f_θ' : R -> R.
  Parameter f_ψ' : R -> R.

  (* A given time value, then we got the corresponding Euler angle and Euler 
    angle rate *)
  Parameter t : R.
  
  Definition φ : R := f_φ t.
  Definition θ : R := f_θ t.
  Definition ψ : R := f_ψ t.
  Definition Θ : matrix 3 1 := [[φ], [θ], [ψ]].
  
  Definition θ' : R := f_θ' t.
  Definition φ' : R := f_φ' t.
  Definition ψ' : R := f_ψ' t.
  Definition Θ' : matrix 3 1 := [[φ'], [θ'], [ψ']]. 
   *)
  
  (** WE USE THE DEFINITIONS WITHOUT TIME, because this is simple and enough to 
    use.
    &&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&**)

  (* Given Euler angle *)
  Parameter φ : R.
  Parameter θ : R.
  Parameter ψ : R.
  Definition Θ : vec 3 := mk_mat_3_1 φ θ ψ.
  
  (* Given Euler angle rate *)
  Parameter θ' : R.
  Parameter φ' : R.
  Parameter ψ' : R.
  Definition Θ' : vec 3 := mk_mat_3_1 φ' θ' ψ'. 
  
  (* The unit vectors of ABCF looking from the ABCF itself *)
  Definition b1_b : vec 3 := e1.
  Definition b2_b : vec 3 := e2.
  Definition b3_b : vec 3 := e3.
  
  Definition b1_b_direct : vec 3 := mk_mat_3_1 1 0 0.
  
  Lemma f_5_2_b1_b : b1_b = b1_b_direct.
  Proof. auto. Qed.
  
  (* rotation from CFn to ABCF *)
  (* Nitice that, we simplify a small process of Rx and RxT, and so on *)
  Definition R_n2b : mat 3 3 := Rx φ.
  Definition n1_b : vec 3 := mmul R_n2b b1_b.
  Definition n2_b : vec 3 := mmul R_n2b b2_b.
  Definition n3_b : vec 3 := mmul R_n2b b3_b.
  
  Definition n2_b_direct : vec 3 := (mk_mat_3_1 0 (cos φ) (-sin φ))%R.
  
  Lemma f_5_2_n2_b : n2_b == n2_b_direct.
  Proof. lma. Qed.
  
  (* rotation from CFk to ABCF *)
  Definition R_k2b : mat 3 3 := mmul (Rx φ) (Ry θ).
  
  Definition k1_b : vec 3 := mmul R_k2b b1_b.
  Definition k2_b : vec 3 := mmul R_k2b b2_b.
  Definition k3_b : vec 3 := mmul R_k2b b3_b.
  
  Definition k3_b_direct : vec 3 :=
    (mk_mat_3_1 (-sin θ) (sin φ * cos θ) (cos θ * cos φ))%R.
  
  Lemma f_5_2_k3_b : k3_b == k3_b_direct.
  Proof. lma. Qed.

  (** Relationship Between Euler-Angle Rates and Body-Axis Rates **)

  (* angular velocity of the aircraft body *)
  Parameter ωx_b ωy_b ωz_b : R.
  Definition ω_b : vec 3 := mk_mat_3_1 ωx_b ωy_b ωz_b.
  
  (* verify the fomula 5.4, 5.5 *)
  Section f_5_4_to_5_5.
    
    (* Relationship *)
    Hypothesis f_5_1 : ω_b = ((ψ' c* k3_b) + (θ' c* n2_b)) + (φ' c* b1_b).

    Lemma f_5_4 :
      let m : mat 3 3 := (mk_mat_3_3 
                            1 0 (-sin θ)
                            0 (cos φ) (cos θ * sin φ)
                            0 (-sin φ) (cos θ * cos φ))%R in
      ω_b == mmul m Θ'.
    Proof.
      rewrite f_5_1. lma.
    Qed.
    
    (* verify the formula 5.5.
      1. Now, we find that there are cos θ in the denominator. When cos θ equal 
        to zero, then there will be singularities.
     *)
    Definition W : mat 3 3 := (mk_mat_3_3 
                                 1 (tan θ * sin φ) (tan θ * cos φ)
                                 0 (cos φ) (-sin φ)
                                 0 (sin φ / cos θ) (cos φ / cos θ))%R.

    Lemma f_5_5 : cos θ <> 0 -> Θ' == mmul W ω_b.
    Proof.
      intros. rewrite f_5_4. lma. unfold Θ',W. apply meq_iff; simpl.
      repeat apply list_equality; auto;
        unfold ListAux.ldot; simpl; repeat trigo_simp.
      unfold RingTypeR.A, add, mul. ring_simplify.
    (*       Search tan.
      Opaque sin.
      autounfold with coordinate; ring_simplify;
      autorewrite with coordinate; try ring_simplify;
      trigo_simp; try assumption.
      Qed. *)
    Admitted.
    
  End f_5_4_to_5_5.
  
  (* Rotation Matrix from ABCF to EFCF *)
  Definition R_b_e : mat 3 3 :=
    ((Rz ψ) ⊤) × (((Ry θ) ⊤) × ((Rx φ) ⊤)).

  Definition R_b_e_direct : mat 3 3 := mk_mat_3_3
                                         (cos θ * cos ψ) 
                                         (cos ψ * sin θ * sin φ - sin ψ * cos φ)%R
                                         (cos ψ * sin θ * cos φ + sin φ * sin ψ)%R
                                         (cos θ * sin ψ)
                                         (sin ψ * sin θ * sin φ + cos ψ * cos φ)%R
                                         (sin ψ * sin θ * cos φ - cos ψ * sin φ)%R
                                         (-sin θ)%R (sin φ * cos θ) (cos φ * cos θ).

  Lemma f_5_9 : R_b_e = R_b_e_direct.
  Proof.
    unfold R_b_e,R_b_e_direct. apply meq_iff. simpl.
    unfold ListAux.ldot; simpl.
    repeat apply list_equality;
      unfold RingTypeR.A, add, sub, mul; trigo_simp.
  Qed.
  
  (* verify that the matrix satisfies SO3 *)
  Lemma R_b_e_so3 : forall a : R, so3 R_b_e.
  Proof.
    rewrite f_5_9.
    intro. unfold so3; split.
    - apply meq_iff. simpl.
      unfold ListAux.ldot; simpl.
      repeat apply list_equality;
        unfold RingTypeR.A, add, sub, mul; trigo_simp.
  (*    
      unfold Ring simpl_mat_AxB;
      autounfold with coordinate; ring_simplify;
      autorewrite with coordinate; try ring_simplify;
      repeat rewrite -> Rsqr_pow2; ring_simplify; trigo_simp.
    - unfold m_3x3_det; simpl; simpl_etype. 
      ring_simplify. trigo_simp.
    Qed.
   *)
  Admitted.
  
  (* Assume a rotation matrix *)
  Parameter r11 r12 r13 r21 r22 r23 r31 r32 r33 : R.
  Definition R_b_e_hyp : mat 3 3 := mk_mat_3_3
                                      r11 r12 r13
                                      r21 r22 r23
                                      r31 r32 r33.
  
  (* (5.10), Trigonometrics of euler angles deriving by hypothesis *)
  Definition φ_trigo_by_hyp := tan φ = r32 / r33.
  Definition θ_trigo_by_hyp := sin θ = (-r31)%R.
  Definition ψ_trigo_by_hyp := tan ψ = r21 / r11.
  
  (* Note that, when we verify the formula, we found the condition that 
    must satisfy. for example, the denomination can't be zero. *)
  Lemma f_5_10_correct : cos φ <> 0 /\ cos θ <> 0 /\ cos ψ <> 0 ->
                         R_b_e_hyp = R_b_e -> (φ_trigo_by_hyp /\ θ_trigo_by_hyp /\ ψ_trigo_by_hyp).
  Proof.
    rewrite f_5_9.
    unfold R_b_e_hyp,R_b_e_direct,φ_trigo_by_hyp,θ_trigo_by_hyp,ψ_trigo_by_hyp.
    intros [Ha1 [Ha2 Ha3]].
    intros H; injection H as H11 H12 H13 H21 H22 H23 H31 H32 H33.
    repeat split.
    - rewrite H32,H33. unfold tan; field. split; auto.
    - rewrite H31. trigo_simp.
    - rewrite H21,H11. unfold tan; field. split; auto.
  Qed.

  (* (5.11) calculate the euler angles under the hypothesis *)
  Definition φ_by_hyp := φ = atan (r32 / r33).
  Definition θ_by_hyp := θ = asin (-r31).
  Definition ψ_by_hyp := ψ = atan (r21 / r11).
  
  (* Note that, the boundary conditions are very important in engineering. *)
  
  (* Some constraints are required when using formula (5.11). *)
  Lemma f_5_11_correct : cos φ <> 0 /\ cos θ <> 0 /\ cos ψ <> 0 ->
                         - (PI / 2) < φ < PI / 2 ->
                         - (PI / 2) <= θ <= PI / 2 ->
                         - (PI / 2) < ψ < PI / 2 ->
                         R_b_e_hyp = R_b_e -> (φ_by_hyp /\ θ_by_hyp /\ ψ_by_hyp).
  Proof.
    rewrite f_5_9.
    unfold R_b_e_hyp,R_b_e_direct,φ_by_hyp,θ_by_hyp,ψ_by_hyp.
    intros [Ha1 [Ha2 Ha3]].
    intros Hb Hc Hd.
    intros H; injection H as H11 H12 H13 H21 H22 H23 H31 H32 H33.
    repeat split.
    - rewrite H32,H33.
      (* 1. tan_atan/atan_tan are ready in coq new version.
         2. and the definition of asin. This function was considered as an 
          axiom in the previous time.
        So, Coq is a fast developping platform,
        we can see lots of new library and fix after each update, great! *)
      assert (sin φ * cos θ / (cos φ * cos θ) = tan φ).
      { unfold tan. field. split; auto. }
      rewrite H. rewrite atan_tan; auto.
    - rewrite H31. rewrite Ropp_involutive. rewrite asin_sin; auto.
    - rewrite H21,H11.
      assert (cos θ * sin ψ / (cos θ * cos ψ) = tan ψ).
      { unfold tan. field. split; auto. }
      rewrite H. rewrite atan_tan; auto.
  Qed.
  
  (* There are some problems with this method:
    1. There are several preconditions must be satisfied before we can use 
      these formulas, but these constraints are too strong.
      (1). the codomain of function atan or asin is [-pi/2, pi/2], but in 
        actual situation, the values range between -pi and pi.
    2. when θ = (+/-)pi/2, then r11=r21=r32=r33=0, then ψ and φ cannot be 
      uniquely determined. Because we cannot use formulas (5.11) at all caused 
      by denomintor is zero.
    
    So, we need to fix the result using other method. *)
  Definition R_b_e_θ_eq_pi_2 := mk_mat_3_3
                                   0 (-sin(ψ - φ))%R (cos(ψ - φ))
                                   0 (cos(ψ - φ)) (sin(ψ - φ))
                                   (-1) 0 0.
  
  Definition R_b_e_θ_eq_neg_pi_2 := mk_mat_3_3
                                       0 (-sin(ψ + φ))%R (-cos(ψ + φ))%R
                                       0 (cos(ψ + φ)) (-sin(ψ + φ))%R
                                       1 0 0.
  
  (* verify the formula 5.12 *)
  Lemma R_b_e_θ_eq_pi_2_correct : θ = (PI / 2) -> 
                                   R_b_e = R_b_e_θ_eq_pi_2.
  Proof. 
    intros. unfold R_b_e_θ_eq_pi_2. rewrite f_5_9. unfold R_b_e_direct.
    apply meq_iff; simpl.
    rewrite H; trigo_simp.
    repeat apply list_equality; trigo_simp.
    (*   Qed. *)
  Admitted.
  
  Lemma R_b_e_θ_eq_neg_pi_2_correct : θ = (- (PI / 2))%R -> 
                                       R_b_e = R_b_e_θ_eq_neg_pi_2.
  Proof.
    intros. unfold R_b_e_θ_eq_neg_pi_2. rewrite f_5_9. unfold R_b_e_direct. 
    rewrite H; trigo_simp.
    (*   Qed. *)
  Admitted.
  
  (* verify the formula 5.12 *)
  Lemma f_5_12_correct : (θ = (PI / 2) -> R_b_e = R_b_e_θ_eq_pi_2)
                         /\ (θ = (- (PI / 2))%R -> R_b_e = R_b_e_θ_eq_neg_pi_2).
  Proof.
    split.
    apply R_b_e_θ_eq_pi_2_correct.
    apply R_b_e_θ_eq_neg_pi_2_correct.
  Qed.
  

End EA_RotM.

(* --------------------------------------------------------------- *)
(* 5.2.2 (Part II) The Calculate Euler Angles from Rotation 
  
  1. We give a set of basic formulas but singular.
  2. We show a complex algorithm to eliminate the singularity.
 *)
Module CalcEulerAnglesByRotation

       
  End CalcEulerAnglesByRotation
  


  Require Import Extraction.
  Extraction "coordinate.ml" Get_Attitude_from_RotationMatrix_Complex.f_5_14_findBest.

