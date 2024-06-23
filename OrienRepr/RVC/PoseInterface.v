(*
  Copyright 2022 Zhengpu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Interface of pose representation (version 1)
  author    : Zhengpu Shi
  date      : Nov, 2023
  
  reference :
  1. Peter Corke, Robotics Vision and Control
     Ch2 Representing Position and Orientation 位置和朝向表示
 *)

Declare Scope pose_scope.
Delimit Scope pose_scope with pose.
Open Scope pose_scope.

(** An abstract formal model for kinematics transformation.
    1. for 2D/3D orientation or pose.
    2. use right-hand rule to determine positive direction or positive angle.
 *)
Module Type PoseInterface.
  (* 坐标系 *)
  Parameter Frame : Type.

  (* 在某个坐标系下描述的点，约束向量，坐标向量 *)
  Parameter Point : Frame -> Type.

  (* 相对位姿（简称位姿）。例如，${}^A\xi_B$ 表示 B 相对于 A 的位姿 *)
  Parameter Pose : Frame -> Frame -> Type.

  (* 位姿的良定义性。比如：正交矩阵，SO(3),SE(3)等 *)
  Parameter poseWd : forall {B C}, Pose B C -> Prop.

  (* 位姿参数。用以创建一个位姿 *)
  Parameter PoseParam : Type.
  (* 使用位姿参数创建位姿 *)
  Parameter makePose : forall {B C}, PoseParam -> Pose B C.
  (* 使用位姿参数创建出的位姿满足位姿良定义性 *)
  Axiom makePose_poseWd : forall B C pp, @poseWd B C (makePose pp).

  (* 坐标变换 *)
  Parameter pointTrans : forall {B C} (p : Pose B C) (v : Point B), Point C.
  Infix "*" := pointTrans.
  (* 坐标变换需要满足的性质：确保变换的结果符合几何推理 *)
  Parameter PointTransSpec : forall {B C} (p : Pose B C) (vb : Point B) (vc : Point C), Prop.
  Axiom pointTrans_PointTransSpec : forall B C (p : Pose B C) (vb : Point B),
      PointTransSpec p vb (p * vb).
  (* 坐标变换的唯一性 *)
  (* Axiom pointTrans_uniq : forall B C (p1 p2 : Pose B C) (vb : Point B), p1 * vb = p2 * vb. *)

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
End PoseInterface.


(* Example *)
Module test1.
  Declare Module AP : PoseInterface.
  Import AP.

  (* O,F,B,C,R 的例子 *)
  Section example.

    (* 给定一些坐标系 *)
    Variable O : Frame.         (* 世界坐标系 *)
    Variable F : Frame.         (* fixed camera *)
    Variable B : Frame.         (* object *)
    Variable C : Frame.         (* camera on robot *)
    Variable R : Frame.         (* robot *)
    
    (* 给定几个位姿 *)
    Variable pOF : Pose O F.      (* 从 O 到 F 的位姿 *)
    Variable pOB : Pose O B.
    Variable pOR : Pose O R.
    Variable pFB : Pose F B.
    Variable pCB : Pose C B.
    Variable pRC : Pose R C.

    (* `pFB` is equivalent to `(- pOF) + pOB` *)
    Goal forall (p : Point F), pFB * p = (- pOF + pOB) * p.
    Proof. intros. apply pointTrans_uniq. Qed.
    
    (* Give different paths to represent pFR *)
    Definition pFOR : Pose F R := - pOF + pOR.
    Definition pFBCR : Pose F R := pFB - pCB - pRC.

  End example.
End test1.
