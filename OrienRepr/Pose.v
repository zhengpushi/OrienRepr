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

(** 坐标系{B}相对于坐标系{A}的位姿，由齐次矩阵构成 *)
Record PoseHom (A B : Frame) :=
  mkPoseHom {
      poseHomMat :> smat 4;
      poseHomSO3 : SOnP (mremovecT (mremoverT poseHomMat));
      poseHomRow4Zero : [poseHomMat.4.1; poseHomMat.4.2; poseHomMat.4.3] = [0;0;0]
    }.
Arguments mkPoseHom {A B}.
Arguments poseHomMat {A B}.
Arguments poseHomSO3 {A B}.
Arguments poseHomRow4Zero {A B}.

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
  rewrite meq_mconsrT_mremoverT_mtailr. f_equal.
  - rewrite meq_mconscT_mremovecT_mtailc. f_equal.
  -
    
    ?

(** 齐次变换(transformation)：
    设坐标系{B}和{A}不但原点不重合，而且姿态也不相同，用位姿poseB2A描述
    {B}相对于{A}的位姿，则任意点p在{A}中的坐标pA可由p在{B}中的坐标pB得到 *)
Definition trans {A B} (poseB2A : Pose A B) (pB : Point B)
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

