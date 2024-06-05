(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Mathematical base for Pose Representation
  author    : ZhengPu Shi
  date      : 2023.04.01

  reference :
  1. Peter Corke, Robotics Vision and Control
  
  remark    :
  1. How to specify positive direction?
     * In 2D, (when locking from your eyes to the screen (or paper) ), the 
       counterclockwise direction is defined as positive direction, which is 
       consistent with the usual angle definition.
     * In 3D, the right-hand rule is used to specify the positive direction.
  2. Conventions in this text: using column vectors and pre-multiplication.
  3. Understanding of rotation operations rot2 and rot2'.
    (1) Column vectors are composed of the unit vectors of the rotated coordinate axes
        in the original reference coordinate system.
        Linear representation can help to understand this: Give a matrix R=[x̂,ŷ]，
        and a column vector v=[v.1,v.2]^T, then
            R*v = v.1*x̂ + v.2*ŷ
        representing a vector as a linear combination of the unit vectors of the axes
        and their coordinates.
  4. Three uses of the rotation matrix
  (1) It can represent the relative orientation of two coordinate systems.
      * If coordinate system {0} rotates by θ1 to coordinate system {1}, then
        the orientation of {1} relative to {0} is R(0->1) = rot2(θ1);
      * If coordinate system {1} rotates by θ2 to coordinate system {2}, then
        the orientation of {2} relative to {1} is R(1->2) = rot2(θ2);
      * Now, the orientation of coordinate system {2} relative to {0} is
  (2) It can be used to calculate the coordinates of a vector under passive rotation
      due to the rotation of the coordinate system.
      * In a coordinate system, the coordinates of a vector are v, and after rotating
        the vector by an angle θ, its coordinates become v'. Then
        v' = rot2(θ) * v
        v  = rot2(θ)^T * v'
      * That is,
        world coordinates of point A after rotation =
        rotation matrix * world coordinates of point A before rotation
  (3) It can be used to calculate the coordinates of a vector under passive rotation
      due to the rotation of the coordinate system.
      * If coordinate system {0} rotates by an angle θ to coordinate system {1},
        and the coordinates of a vector in {0} and {1} are v0 and v1 respectively.
        Then
        v0 = rot2(θ) * v1,
        v1 = rot2(θ)^T * v0,
        where rot2(θ) represents the rotation matrix of {1} relative to {0}.
      * That is,
        The rotation of the coordinate system is equivalent to the inverse process of
        "active rotation of the vector".
      * Therefore,
        Camera coordinates of point A after transformation =
        inverse of the rotation matrix * world coordinates of point A before transformation.
      * So,
        World coordinates of point A before transformation =
        rotation matrix * camera coordinates of point A after transformation.
      * Using more popular subscript notation: suppose a vector X has coordinates (X)^B
        in coordinate system {B} and (X)^A in coordinate system {A}, and the rotation
        matrix of {B} relative to {A} is R_B^A. Then the following relationship holds:
        (X)^A = R_B^A * (X)^B
  5. Other explanations
    (1) Pure rotation is commutative in 2D, making the sequence not important.
        But it is noncommutative in 3D.
        For example, when working on pose (rotation + translation), this is not commutative.
    (2) If two consecutive rotations are performed, i.e., first rotate by θ1, and then
        rotate by θ2 on this basis, the total relative pose is
        R(θ2) * R(θ1) or R(θ1) * R(θ2)

 *)

From FinMatrix Require Export MatrixR.
Require Export Reals.

Open Scope nat_scope.
Open Scope R_scope.
Open Scope vec_scope.
Open Scope mat_scope.


(* ======================================================================= *)
(** ** Convert a angle between degree and radian *)

Inductive AngleKind := Radian | Degree.

Definition deg2rad (d : R) : R := d * PI / 180.
Definition rad2deg (r : R) : R := r * 180 / PI.

Record angle := {
    angle_radian : R;
    angle_degree : R
  }.

Definition mk_angle_deg (d : R) : angle :=
  Build_angle (deg2rad d) d.

Definition mk_angle_rad (r : R) : angle :=
  Build_angle r (rad2deg r).

Notation "r 'rad" := (mk_angle_rad r) (at level 30).
Notation "d 'deg" := (mk_angle_deg d) (at level 30).

Section test.
  Goal 180 'deg = PI 'rad.
  Proof. cbv. f_equal; field. ra. Qed.
End test.
                       
