(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : 2D中的位姿
  author    : Zhengpu Shi
  date      : Nov, 2023
  
  reference :
  1. Peter Corke, Robotics Vision and Control
     Ch2 Representing Position and Orientation 位置和朝向表示
 *)

Require Import PoseInterface.
From FinMatrix Require Import MatrixR.
From FinMatrix Require Import MyExtrOCamlR.


(** ** two-dimensional orientation (or known rotation) *)
Module Orientation2D <: PoseInterface.

  (* 坐标系，使用自然数来标识 *)
  Definition Frame := nat.

  (* 在某个坐标系下描述的点，约束向量，坐标向量 *)
  Definition Point (B : Frame) := vec 2.

  (* 相对位姿（简称位姿）。例如，${}^A\xi_B$ 表示 B 相对于 A 的位姿 *)
  Definition Pose (B C : Frame) := smat 2.

  (* 位姿的良定义性 *)
  Definition poseWd {A B} (p : Pose A B) := SOnP p.

  (* 位姿参数。用以创建一个位姿。此处是：{旋转角} *)
  Definition PoseParam := R.
  
  (* 使用位姿参数创建位姿 *)
  Definition makePose {A B} (pp : PoseParam) : Pose A B :=
    let theta := pp in 
    l2m [[cos theta; sin theta];
         [- sin theta; cos theta]]%R.

  (* 使用位姿参数创建出的位姿满足位姿良定义性 *)
  Lemma makePose_poseWd : forall A B pp, @poseWd A B (makePose pp).
  Proof.
  Admitted.

  (* 坐标变换 *)
  Definition pointTrans {B C} (p : Pose B C) (v : Point B) : Point C := p *v v.
  Infix "*" := pointTrans.
  
  (* 坐标变换需要满足的性质：确保变换的结果符合几何推理 *)
  Definition PointTransSpec {B C} (p : Pose B C) (vb : Point B) (vc : Point C) :=
    (* 从几何上看，2D坐标变换前后满足如下关系式：
       vc.x = cos θ * vb.x + sin θ * vb.y
       vc.y = - sin θ * vb.x + cos θ * vb.y
       写成矩阵形式
       [vc.x] = [ cos θ; sin θ] * [vb.x]
       [vc.y]   [-sin θ; cos θ]   [vb.y],  记作 vc = R * vb
       此处的性质是为了确保 R 矩阵是根据这个推导过程而得到的
     *)
    vc = p *v vb.
  
  Lemma pointTrans_PointTransSpec : forall B C (p : Pose B C) (vb : Point B),
      PointTransSpec p vb (p * vb).
  Proof. intros. hnf. auto. Qed.

  (* 坐标变换的唯一性 *)
  Axiom pointTrans_uniq : forall B C (p1 p2 : Pose B C) (vb : Point B), p1 * vb = p2 * vb.
  Definition pointTrans {A B} (T : pose A B) (p : point A) : point B := T *v p.

  Definition poseOp {A B C : frame} (T1 : pose A B) (T2 : pose B C) : pose A C :=
    T1 * T2.

  (* 位姿复合 *)
  Parameter poseComp : forall {B C D} (pBC : Pose B C) (pCD : Pose C D), Pose B D.
  Infix "+" := poseComp.
  (* 位姿复合需要满足的性质：确保复合后的位姿与坐标变换一致 *)
  Axiom poseComp_keep_pointTrans :
    forall B C D (pBC : Pose B C) (pCD : Pose C D) (vb : Point B),
      pCD * (pBC * vb) = (pBC + pCD) * vb.

  (* 位姿单位元 *)
  Parameter poseId : forall {B C}, Pose B C.
  Notation "0" := poseId.
  (* 位姿单位元是左单位元 *)
  Axiom poseIdL : forall B C (p : Pose B C), 0 + p = p.
  (* 位姿单位元是右单位元 *)
  Axiom poseIdR : forall B C (p : Pose B C), p + 0 = p.

  (* 位姿逆运算 *)
  Parameter poseInv : forall {B C}, Pose B C -> Pose C B.
  Notation "- p" := (poseInv p).
  Infix "-" := (fun a b => a + - b).
  (* 位姿逆元是左逆元 *)
  Axiom poseInvL : forall B C (p : Pose B C), poseWd p -> - p + p = 0.
  (* 位姿逆元是右逆元 *)
  Axiom poseInvR : forall B C (p : Pose B C), poseWd p -> p + - p = 0.

  ?
  (* Make a pose.*)
  Definition mkPose 
  (* The specification of `mkPose` is come from 
 Note, we left this   *)
  Variable Rotation2D_matrix_valid : smat 2 -> Prop.
    Theorem mkPose_spec : forall A B theta, P (@mkPose A B theta)
  

  
  Definition pose0 {A B : frame} : pose A B := mat1.

  Definition poseN {A B : frame} (T : pose A B) : pose B A := T\T.

  Infix "⊕" := poseOp (at level 50).
  Notation "⊖ p" := (poseN p) (at level 40).
  Notation "0" := pose0.
  Infix "⊖" := (fun p q => p ⊕ (⊖ q)) (at level 50).

  (* pose是唯一的，暂时难以说明 *)
  Axiom poseUniq : forall (A B:frame) (p1 p2 : pose A B), p1 = p2.
  
  (* 逆元等于交换上下标 *)
  Lemma poseN_eq : forall (A B:frame) (T1:pose A B) (T2:pose B A), ⊖ T1 = T2.
  Proof. intros. apply poseUniq. Qed.

  (* 左单位元 *)
  Lemma pose0l : forall (A B:frame) (p:pose A B), p ⊕ 0 = p.
  Proof. intros. apply mmul_1_r. Qed.

  (* 右单位元 *)
  Lemma pose0r : forall (A B:frame) (p:pose A B), 0 ⊕ p = p.
  Proof. intros. apply mmul_1_l. Qed.

  (* 左逆元 *)
  Lemma poseNl : forall (A B:frame) (p:pose A B), poseWd p -> (⊖ p) ⊕ p = 0.
  Proof. intros. destruct H as [H1 H2]. apply morth_iff_mul_trans_l. auto. Qed.

  (* 右逆元 *)
  Lemma poseNr : forall (A B:frame) (p:pose A B), poseWd p -> p ⊕ (⊖ p) = 0.
  Proof. intros. destruct H as [H1 H2]. apply morth_iff_mul_trans_r. auto. Qed.
  
End Orientation2D.

(* Usage of the Orientation2D module *)
Module Orientation2D_example.
  Import Orientation2D.

  (* OCaml extraction *)
  (* Recursive Extraction poseOp. *)

  Section ex1.
    Let G : frame := 1%nat.
    Let B : frame := 2%nat.
    Variable theta : R.
    Let G2B := 
    
  End ex1.
  Locate "⊕".
  Check poseop.

  
End Orientation2D_example.


Module Pose2D <: PoseInterface.

  (* use natural numbers to denote a frame *)
  Definition frame := nat.

  (* 
     [ cos θ, sin θ, x]
     [-sin θ, cos θ, y]
     [0     , 0    , 1]
 *)
  Definition pose := fun A B : frame => smat 3.
  
  Definition point := fun A : frame => vec 3.

  Definition pointTrans {A B} (T : pose A B) (p : point A) : point B := T *v p.

  Definition poseOp {A B C : frame} (T1 : pose A B) (T2 : pose B C) : pose A C.
    Check T1 * T2.
    Eval cbv in T1.
    Compute pose A B.
    Check T1.
    let R1 : mat 2 2 := l2m [[T1.11;T1.12];[T1.21;T1.22]] in
    let R2 : mat 2 2 := l2m [[T2.11;T2.12];[T2.21;T2.22]] in
    let t1 : cvec 2 := l2cv [T1.13; T1.23] in
    let t2 : cvec 2 := l2cv [T2.13; T2.23] in
    let R1R2 := R1 * R2 in
    let t1R1t2 := t1 + R1 * t2 in
    mappr (mappc R1R2 t1R1t2) (l2rv [0;0;1]).
    
    Definition pose0 {A B : frame} : pose A B := mat1.

    Definition poseN {A B : frame} (T : pose A B) : pose B A :=
      let R : mat 2 2 := l2m [[T.11;T.12];[T.21;T.22]] in
      let t : cvec 2 := l2cv [T.13; T.23] in
      let RT := R\T in
      let nRTt := - (R\T * t) in
      mappr (mappc RT nRTt) (l2rv [0;0;1]).

    Infix "⊕" := poseOp (at level 50).
    Notation "⊖ p" := (poseN p) (at level 40).
    Notation "0" := pose0.
    Infix "⊖" := (fun p q => p ⊕ (⊖ q)) (at level 50).


    (* pose是唯一的，暂时难以说明 *)
    Axiom poseUniq : forall (A B:frame) (p1 p2:pose A B), p1 = p2.
    
    (* 逆元等于交换上下标 *)
    Lemma poseN_eq : forall (A B:frame) (T1:pose A B) (T2:pose B A), ⊖ T1 = T2.
    Proof.
      intros.
      (* unfold poseN. *)
      apply poseUniq.
    Admitted.

    (* 左单位元 *)
    Lemma pose0l : forall (A B:frame) (p:pose A B), p ⊕ 0 = p.
    Proof.
      
      intros. unfold poseOp, pose0. simpl. unfold pose in p. cbv.

      (* 右单位元 *)
      Axiom pose0r : forall (A B:frame) (p:pose A B), 0 ⊕ p = p.

      (* 左逆元 *)
      Axiom poseNl : forall (A B:frame) (p:pose A B), (⊖ p) ⊕ p = 0.

      (* 右逆元 *)
      Axiom poseNr : forall (A B:frame) (p:pose A B), p ⊕ (⊖ p) = 0.
      
End Orientation2D.
