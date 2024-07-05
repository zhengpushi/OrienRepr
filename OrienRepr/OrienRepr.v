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
     The rotation matrix are 
         R(ϕ,θ,ψ) = Rz(ψ) * Ry(θ) * Rx(ϕ)
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
          换言之，按xyz外旋时，新的坐标相对于初始坐标应用了变换 Rz*Ry*Rx *)
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
          换言之，按zyx内旋时，新的坐标相对于初始坐标应用了变换 Rz*Ry*Rx *)
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
Definition rotx (ang : R) (v : vec 3) : vec 3 := (Rx ang) *v v.

(** Rotates vector `v` along the y-axis by `ang` (radians)  *)
Definition roty (ang : R) (v : vec 3) : vec 3 := (Ry ang) *v v.

(** Rotates vector `v` along the z-axis by `ang` (radians)  *)
Definition rotz (ang : R) (v : vec 3) : vec 3 := (Rz ang) *v v.

(** Rotates vector `v` along the `ax`-axis by `ang` (radians)  *)
Definition rotaa (ax : vec 3) (ang : R) (v : vec 3) : vec 3 := rotaa (mkAA ang ax) v.

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

(** Rotation matrix to euler angles. Note that M ∈ SO(3) *)
(* roll∈(-π,π), pitch ∈ (-π/2,π/2), yaw ∈ (-π,π) *)
Definition m2e (M : smat 3) : vec 3 :=
  l2v [R2Euler_S123.alg2.ϕ' M; R2Euler_S123.alg2.θ' M; R2Euler_S123.alg2.ψ' M].

(* ======================================================================= *)
(** ** Axis-angle <-> Rotation matrix *)

(** Axis-angle to rotation matrix by rodrigues formula. Note that axis is unit vector *)
Definition aa2m (axis : vec 3) (angle : R) : smat 3 := aa2mat (mkAA angle axis).

(** Axis-angle to rotation matrix by direct formula. Note that axis is unit vector *)
Definition aa2m' (axis : vec 3) (angle : R) : smat 3 := aa2matM (mkAA angle axis).

(** Rotation matrix to axis-angle *)

(* ?  *)
(* Definition maa2mat (M : smat 3) : (vec 3 * R). *)


(* ======================================================================= *)
(** ** Unit quaternion <-> Rotation matrix *)

(** Unit quaternion to rotation matrix. Note that q is unit quaternions *)
Definition q2m (q : vec 4) : smat 3 := q2m q.

(** Rotation matrix to unit quaternion. Note that M ∈ SO(3) *)
Definition m2q (M : smat 3) : vec 4 := m2q M.


(* ======================================================================= *)
(** ** Unit quaternion <-> Euler angles *)

(** Unit quaternion to euler angles. Note that q is unit quaternions *)
Definition q2e (q : vec 4) : vec 3 := m2e (q2m q).

(** Euler angles to unit quaternion. *)
Definition e2q (e : vec 3) : vec 4 := m2q (e2m e).



(* ########################################################################### *)
(** * Examples *)


(* ########################################################################### *)
(** * Extraction to OCaml code *)

(* Recursive Extraction *)
(*   rotx roty rotz rotaa rotByM rotByQ rot2ByQ *)
(*   e2m m2e *)
(*   aa2m aa2m' *)
(*   q2m m2q *)
(*   q2e e2q. *)

(* Extraction "ocaml_orienRepr.ml" *)
(*   v2l l2v m2l l2m *)
(*   rotx roty rotz rotaa rotByM rotByQ rot2ByQ *)
(*   e2m m2e *)
(*   aa2m aa2m' *)
(*   q2m m2q *)
(*   q2e e2q. *)

(* 
   简单测试：https://www.andre-gaschler.com/rotationconverter/

   # 给定欧拉角：-2.0, 1.0, 0.1
   utop[1]> let v1 = l2v 0. 3 [-2.;1.;0.1];;
   val v1 : fin -> float = <fun>
   
   # 欧拉角到旋转矩阵
   utop[2]> let m1 = (e2m v1);;
   val m1 : fin -> fin -> float = <fun>
   utop[3]> m2l 3 3 m1;;
   - : float list list =
   [[0.537603044848121; -0.719779490760507623; -0.439204338378588466];
   [0.0539402252169759802; -0.490455115035341449; 0.86979551173779468];
   [-0.841470984807896505; -0.491295496433881929; -0.224845095366152908]]

   # 旋转矩阵到欧拉角
   utop[4]> v2l 3 (m2e m1);;
   - : float list = [-2.; 1.; 0.0999999999999999778]

   # 旋转矩阵到四元数
   utop[5]> v2l 4 (m2q m1);;
   - : float list =
   [0.453404574978745256; -0.750483719884984524; 0.221803367581902611;
   0.426616623803230233]

   # 旋转矩阵到四元数，再到欧拉角
   utop[6]> v2l 3 (q2e (m2q m1));;
   - : float list = [-2.; 1.; 0.100000000000000019]

   # 欧拉角到四元数
   utop[7]> v2l 4 (e2q v1);;
   - : float list =
   [0.453404574978745256; -0.750483719884984524; 0.221803367581902611;
   0.426616623803230233]

 *)

