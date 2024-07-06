(*
  Copyright 2023 Zhengpu Shi
  This file is part of OrienRepr. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : End-user friendly interface for Orientation Representation
  author    : Zhengpu Shi
  date      : 2022.06

  remark    :
  1. This file provides users and extractions with a friendly name for
     the OR algorithms.
  
  2. We always use pre-multiplication(预乘). That is:
     Give an orientation representation of frame {B} respect to {A}, also known as 
     relative pose of {B} respect to {A}, and denoted as R_B2A.
     Now, give the coordinate of a vector v⃗ respect to {A} is vA, then the 
     coordinate of v⃗ respect to {B} is:
              vB = R_B2A *v vA
  
  3. Although there are 24 convensions for euler angles,
     Here, we only focus on mostly used convension, ZYX euler angles.
     That is, intrinsic rotation by z-, y, and x-axis.
     This is equal to extrinsic rotation by x-, y-, and z-axis.
     The rotation matrix is a multiplication of basic rotation matrices by 
     reversed order. That is:
         R(ϕ,θ,ψ) = Rz(ψ) * Ry(θ) * Rx(ϕ)

  usage     :
  1. Four methods for ORs
    * Rotation matrix:
      Formally, it is a `smat 3`, especially, it is belong to SO(3)
    * Euler angles: 
      We use S123 convention, that is, extrinsic rotation with zyx sequence.
      It is equivalent to intrinsic rotation with xyz sequence (RPY angles).
      Three angles denoted with (\phi,\theta,\psi), i.e., (ϕ,θ,ψ)
      Formally, it is a `vec 3` type
    * Axis-angle:
      It has two parameters, a 3-dimensional vector for axis, a real number for angle.
      Not that, the axis vector must be in unit to be used correctly.
      Formally, it is a `vec 4` type. First 3 elements are axis, the last one is angle.
    * Unit quaternion
      It has 4 parameters, which we called W,X,Y,Z
      Not that, the quaternion must be in unit to be used correctly.
      Formally, it is a `vec 4` type.
  2. Conversion between them.
     We will use this notation:
        m : Rotation matrix
        e : Euler angles
        a : Axis-angle
        q : Unit quaternion
     Now, these conversion is supported.
              m   e    a    q
         m   id  m2e   -   m2q
         e  e2m   id   -   e2q
         a  a2m  a2e   id  a2q
         q  q2m  a2e  q2a   id
 *)

Require Export RotationMatrix3D AxisAngle EulerAngle Quaternion.

Open Scope R.
Open Scope quat_scope.
Open Scope mat_scope.
Open Scope vec_scope.


(* ########################################################################### *)
(** * Comparison of Extrinsic and Intrinsic Rotation *)
(* rot by xyz (RPY angles) is equal to Intrinsic rot by zyx (Euler angles) *)
Module xyzRPY_eq_zyxEULER.
  (* 
     1. Extrinsic Rotation:
        * Passive. Rotates the object with respect to a fixed frame.
        * If perform a rotation about x-, y-, and z-axis, then R = Rz * Ry * Rx.
          That is, the matrix multiplication order is reversed.
        * Specifically, xyz extrinsic rotation corresponds to RPY angles.
     2. Intrinsic Rotation:
        * = active rotation = rotate respect to moving frame
        * If perform a rotation about x-, y-, and z-axis, then R = Rx * Ry * Rz.
          That is, the matrix multiplication order is normal.
        * Specifically, zyx intrinsic rotation is a convention for Euler angles.
   *)

  (* extrinsic rotation *)
  Definition xyzEXTR (angx angy angz : R) : smat 3 := Rz angz * Ry angy * Rx angx.

  Section xyzEXTR_spec.
    (* 初始坐标系E，点P在E中的坐标为 p *)
    Variable p : vec 3.
    
    (* 1. P 绕 E 的 x 轴旋转 angx，得到点 P1 的坐标 p1 = Rx(angx) * p；
       2. P1 绕 E 的 y 轴旋转 angy 得到点 P2 的坐标 p2 = Ry(angy) * p1；
       3. P2 绕 E 的 z 轴旋转 angz 得到目标点 P' 的坐标 p' = Rz(angy) * p2 
          于是 
               p' = Rz*Ry*Rx * p
          换言之，按xyz外旋时，新的坐标相对于初始坐标应用了变换 Rz*Ry*Rx，是从右往左 *)
    Variable angx angy angz : R.
    Let p1 := Rx angx *v p.
    Let p2 := Ry angy *v p1.
    Let p' := Rz angz *v p2.

    Lemma xyzEXTR_spec : p' = (xyzEXTR angx angy angz) *v p.
    Proof. unfold xyzEXTR, p', p2, p1. rewrite !mmulv_assoc. auto. Qed.
  End xyzEXTR_spec.

  (* intrinsic rotation *)
  Definition zyxINTR (angx angy angz : R) : smat 3 := Rz angz * Ry angy * Rx angx.

  Section zyxINTR_spec.
    (* 初始坐标系E，点P在E中的坐标为 p *)
    Variable p : vec 3.
    
    (* 1. P 绕 E 的 z 轴旋转 angz，得到点 Q1 的坐标 q1 = Rz(angz) * p，
          坐标系经过同样的旋转形成新的坐标系 E1；
       2. Q1 绕 E1 的 y 轴旋转 angy 得到点 Q2。 
          这个操作等价于先把 E1 转回 E（应用变换 Rz(angz)^{-1})，
          然后绕 E 的 y 轴旋转 angy（应用变换 Ry(angy)），
          再将 E 转到 E1 （应用变换 Rz(angz))。
          所以，Q2 在 E 中的坐标为 
             q2=Rz*Ry*(Rz\T)*q1 = Rz*Ry*p
          同时，坐标系 E1 也在上述变换作用下变成 E2，相对E而言是应用了变换 Rz*Ry
       3. Q2 绕 E2 的 x 轴旋转 angx 得到点 P''。
          类似的，这个操作等价于：
          将 E2 转回 E（应用变换 (Rz*Ry)^{-1})，
          绕 E 的 x 轴旋转（应用变换 Rx），
          再将 E 转回 E2（应用变换 Rz*Ry)，
          所以，P'' 在 E 中的坐标为：
             p''=(Rz*Ry)*Rx*(Rz*Ry)^{-1}*q2
                =Rz*Ry*Rx*Ry\T*Rz\T*(Rz*Ry*p)
                =Rz*Ry*Rx*p
                =p'
          换言之，按zyx内旋时，新的坐标相对于初始坐标应用了变换 Rz*Ry*Rx，是从左往右 *)
    Variable angx angy angz : R.
    Let q1 := Rz angz *v p.
    Let q2 := Rz angz *v Ry angy *v ((Rz angz)\-1) *v q1.
    Let p'' := (Rz angz * Ry angy)
               *v Rx angx
               *v ((Rz angz * Ry angy)\-1)
               *v q2.

    Fact q2_eq : q2 = Rz angz *v Ry angy *v p.
    Proof.
      unfold q2, q1. rewrite <- !mmulv_assoc. rewrite mmul_assoc.
      rewrite mmul_minvAM_l. rewrite mmul_1_r. auto. apply Rz_minvtble.
    Qed.

    Lemma zyxINTR_spec : p'' = (zyxINTR angx angy angz) *v p.
    Proof.
      unfold zyxINTR, p''. rewrite q2_eq.
      rewrite <- !mmulv_assoc. rewrite !mmul_assoc.
      rewrite mmul_minvAM_l. rewrite mmul_1_r. auto.
      apply mmul_minvtble. apply Rz_minvtble. apply Ry_minvtble.
    Qed.
  End zyxINTR_spec.
  
  Lemma xyzEXTR_eq_zyxINTR : forall angx angy angz,
      xyzEXTR angx angy angz = zyxINTR angx angy angz.
  Proof. auto. Qed.

End xyzRPY_eq_zyxEULER.


(* ########################################################################### *)
(** * Rotate a vector in a given frame to obtain new coordinates  *)

(** Rotates vector `v` along the x-axis by `ang` (radians)  *)
Definition rotx (ang : R) : vec 3 -> vec 3 := fun v => (Rx ang) *v v.

(** Rotates vector `v` along the y-axis by `ang` (radians)  *)
Definition roty (ang : R) : vec 3 -> vec 3 := fun v => (Ry ang) *v v.

(** Rotates vector `v` along the z-axis by `ang` (radians)  *)
Definition rotz (ang : R) : vec 3 -> vec 3 := fun v => (Rz ang) *v v.

(** Rotates vector `v` along the `ax`-axis by `ang` (radians)  *)
Definition rotaa (aa : vec 4) : vec 3 -> vec 3 := fun v => rotaa (v2aa aa) v.

(** Rotates vector `v` by rotation matrix `M` *)
Definition rotByM (M : smat 3) (v : vec 3) : vec 3 := M *v v.

(** Rotates vector `v` by unit quaternion `q` *)
Definition rotByQ (q : vec 4) (v : vec 3) : vec 3 := qrotv q v.

(** Rotates vector `v` by unit quaternion `q1` and followed by q2 *)
Definition rot2ByQ (q1 q2 : vec 4) (v : vec 3) : vec 3 := qrotv (q2 * q1)%quat v.


(* ########################################################################### *)
(** * Conversion between ORs *)

(* ======================================================================= *)
(** ** Euler angles <-> Rotation matrix *)

(** Euler angles (roll,pitch,yaw) to rotation matrix *)
Definition e2m (euler : vec 3) : smat 3 := S123 (euler.1) (euler.2) (euler.3).

(** Rotation matrix to euler angles. Note that M must belogn to SO(3) *)
(* roll∈(-π,π), pitch ∈ (-π/2,π/2), yaw ∈ (-π,π) *)
Definition m2e (M : smat 3) : vec 3 :=
  l2v [R2Euler_S123.alg2.ϕ' M; R2Euler_S123.alg2.θ' M; R2Euler_S123.alg2.ψ' M].

(* ======================================================================= *)
(** ** Axis-angle <-> Rotation matrix *)

(** Axis-angle to rotation matrix by rodrigues formula. 
    Note that axis must be unit *)
Definition a2m (aa : vec 4) : smat 3 := aa2mat (v2aa aa).

(** Axis-angle to rotation matrix by direct formula. Note that axis must be unit *)
Definition a2m' (aa : vec 4) : smat 3 := aa2matM (v2aa aa).

(** Rotation matrix to axis-angle (NOT SUPPORTED YET) *)
(* Definition maa2mat (M : smat 3) : (vec 3 * R). *)

(** Axis-angle to Euler angles. Note that axis must be unit *)
Definition a2e (aa : vec 4) : vec 3 := m2e (a2m aa).


(* ======================================================================= *)
(** ** Unit quaternion <-> Rotation matrix *)

(** Unit quaternion to rotation matrix. Note that q must be unit *)
(* Check q2m.     (* : quat -> smat 3 *) *)

(** Rotation matrix to unit quaternion. Note that M must belong to SO(3) *)
(* Check m2q.     (* : smat 3 -> quat *) *)


(* ======================================================================= *)
(** ** Unit quaternion <-> Euler angles *)

(** Unit quaternion to euler angles. Note that q must be unit *)
Definition q2e (q : vec 4) : vec 3 := m2e (q2m q).

(** Euler angles to unit quaternion. *)
Definition e2q (e : vec 3) : vec 4 := m2q (e2m e).


(* ======================================================================= *)
(** ** Unit quaternion <-> Axis-angle *)

(** Unit quaternion to Axis-angle. Note that q must be unit. *)
Definition q2a (q : vec 4) : vec 4 := aa2v (quat2aa q).

(** Axis-angle to quaternion. Note that axis must be unit *)
Definition a2q (aa : vec 4) : vec 4 := aa2quat (v2aa aa).



(* ########################################################################### *)
(** * Examples *)

(** 我们的库是简单的而又有统一类型的：
    1. 简单性：与数学惯例保持一致的记号，如 v.1, v.2, m.11, m.12 等
    2. 类型统一性，以及数学定义的直观性（相比于MathComp的做法）：
       * 向量就是向量，而不是列矩阵或行矩阵，我们提供 mmulv 和 mvmul 运算，
         同时也提供 cvec, rvec 等类型。
       * 点积、叉积等运算不需要借助矩阵才能实现，而是直接定义
         Print v3cross.
       * 四元数是vec 4，做了一些改进。
 *)

(** 在Coq中可计算带来了符号推导的好处 *)
Section executability_for_symbol_derivation.
  (* 以S123矩阵推导为例，看我们如何自动得到这个结果 *)
  Open Scope R_scope.
  Variable ϕ θ ψ : R.

  (* 这是已经定义和验证了的结果 *)
  (* Eval cbv in m2l (S123 ϕ θ ψ). *)
  (* = [[cos θ * cos ψ; sin ϕ * sin θ * cos ψ + - (sin ψ * cos ϕ); cos ϕ * sin θ * cos ψ + sin ψ * sin ϕ];
        [cos θ * sin ψ; sin ϕ * sin θ * sin ψ + cos ψ * cos ϕ; cos ϕ * sin θ * sin ψ + - (cos ψ * sin ϕ)];
        [- sin θ; sin ϕ * cos θ; cos ϕ * cos θ]]
     : dlist tA *)

  (* 我们可以假设一个矩阵，然后用交互式证明的方式来得到这个矩阵的表达式 *)
  Variable a11 a12 a13 a21 a22 a23 a31 a32 a33 : R.
  Let A : smat 3 := l2m [[a11;a12;a13];[a21;a22;a23];[a31;a32;a33]].
  
  Goal A = (Rz ψ * Ry θ * Rx ϕ)%M.
  Proof.
    (* 利用可计算性，以及我们开发的实数自动化功能 *)
    meq; autorewrite with R.
    (* 我们得到了一组待证目标，它们正是所需要的表达式
       a11 = cos ψ * cos θ
       a12 = - (sin ψ * cos ϕ) + cos ψ * sin θ * sin ϕ
       a13 = sin ψ * sin ϕ + cos ψ * sin θ * cos ϕ
       a21 = sin ψ * cos θ
       a22 = cos ψ * cos ϕ + sin ψ * sin θ * sin ϕ
       a23 = - (cos ψ * sin ϕ) + sin ψ * sin θ * cos ϕ
       a31 = - sin θ
       a32 = cos θ * sin ϕ
       a33 = cos θ * cos ϕ *)
  Abort.
End executability_for_symbol_derivation.

(** 还可以抽取出 OCaml 程序，见下一节 *)


(* ########################################################################### *)
(** * Extraction to OCaml code *)

Extraction "ocaml_orienRepr.ml"
  v2l l2v m2l l2m
  rotx roty rotz rotaa rotByM rotByQ rot2ByQ
  e2m e2q
  a2m a2e a2q
  q2e q2m q2a
  m2e m2q.

(* 
   简单测试：https://www.andre-gaschler.com/rotationconverter/

   # 给定欧拉角：0.1, 1.2, 0.8
utop[3]> let e1 = l2v 0. 3 [0.1; 1.2; 0.8];;
val e1 : fin -> float = <fun>
   # 欧拉角到旋转矩阵
utop[4]> let m1 = e2m e1;;
val m1 : fin -> fin -> float = <fun>
   # 旋转矩阵到四元数
utop[5]> let q1 = m2q m1;;
val q1 : fin -> float = <fun>
   # 四元数到轴角
utop[6]> let a1 = q2a q1;;
val a1 : fin -> float = <fun>
   # 轴角到欧拉角
utop[7]> let e2 = a2e a1;;
val e2 : fin -> float = <fun>

utop[8]> v2l 3 e1;;
- : float list = [0.1; 1.2; 0.8]
utop[9]> m2l 3 3 m1;;
- : float list list =
[[0.252457078727871376; -0.64894468218969048; 0.717729909407369693];
 [0.259939542258515621; 0.759975091022927485; 0.595709069424938731];
 [-0.932039085967226288; 0.0361754126778788196; 0.360547475025082442]]
utop[10]> v2l 4 a1;;
- : float list =
[-0.284762446508513123; 0.839613934982884724; 0.46255679569220759;
 1.38320825687225368]
utop[11]> v2l 4 q1;;
- : float list =
[0.770223935744644539; -0.181613953676377504; 0.535483551864568;
 0.295006485214428626]
 *)

