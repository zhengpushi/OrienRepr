(*
  Copyright 2023 Zhengpu Shi
  This file is part of OrienRepr. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Pose in 2D space
  author    : Zhengpu Shi
  date      : 2023.04.01

 *)

Require Export Orien2D.


(* ########################################################################### *)
(** * Pose in 2-D *)

(* ======================================================================= *)
(** ** Convert between Euclidean coordinates and homogeneous coordinates *)

(** Convert Euclidean coordinates to homogeneous coordinates *)
Definition e2h (v : vec 2) : vec 3 := mkvec3 (v.1) (v.2) 1.

(** Convert homogeneous coordinates to Euclidean coordinates *)
Definition h2e (v : vec 3) : vec 2 := mkvec2 (v.1/v.3) (v.2/v.3).

Lemma h2e_e2h : forall (v : vec 2), h2e (e2h v) = v.
Proof. intros. veq; ra. Qed.

Lemma e2h_h2e : forall (v : vec 3), v.3 = 1 -> e2h (h2e v) = v.
Proof. intros. cbv in H. veq; rewrite H; ra. Qed.

(* Lemma e2h_vadd : forall (u v : vec 2), e2h (u + v) = e2h u + e2h v. *)
(* Proof. intros. veq; req. Qed. *)


(* ======================================================================= *)
(** ** 2-D homogeneous transformation matrix *)

Open Scope mat_scope.

(** Create a 2-D homogeneous transformation matrix:
    1. It represents translation and orientation, or relative pose. 
       This is often referred to as a rigid-body motion.
    2. 它表示坐标系先平移 t，再旋转 θ 后的相对位姿
    3. trans2 ∈ SE(2) ⊂ R^(3x3), SE: special Euclidean group
    4. 相对位姿可用3个参数(t.1, t.2, θ)，或齐次矩阵来表示，前者省空间，后者有组合性
    5. 由于平移和旋转操作不可交换，所以我们总是使用两个分开的操作
    6. 如何使用该矩阵来变换向量？见 operations *)
Definition trans2 (t : vec 2) (θ : R) : mat 3 3 :=
  l2m
    [[cos θ; - sin θ; t.1];
     [sin θ; cos θ;   t.2];
     [0;     0;       1  ]]%R.

(* ======================================================================= *)
(** ** 2-D transformation operations *)

(** Create a 2-D relative pose with pure translate of offset `t` *)
Definition transl2 (t : vec 2) : mat 3 3 := trans2 t 0.

(** Transform a vector v by "transl2 t" equal to "translate v by offset t" *)
Lemma transl2_spec : forall (t : vec 2) (v : vec 2),
    (transl2 t *v e2h v)%V = e2h (v + t)%V.
Proof. intros. veq; ra. Qed.

(** Create a 2-D relative pose with a pure rotation of angle `theta` *)
Definition trot2 (theta : R) : mat 3 3 := trans2 vzero theta.

(** Transform a vector v by "trot2 theta" equal to "rotate v by angle theta" *)
Lemma trot2_spec : forall (theta : R) (v : vec 2),
    (trot2 theta *v e2h v)%V = e2h (rot2 theta *v v)%V.
Proof. intros. veq; ra. Qed.

(** (trans2 t theta) * v = (trot2 theta) * v + t *)
Lemma trans2_eq : forall (t : vec 2) (theta : R) (v : vec 2),
    (h2e (trans2 t theta *v e2h v) = h2e (trot2 theta *v e2h v) + t)%V. 
Proof. intros. veq; ra. Qed.

(** A transformation to rotate about point C *)
Definition trot2center (C : vec 2) (theta : R) : mat 3 3 :=
  transl2 C * trot2 theta * transl2 (- C)%V.

Section test.
  (* Create a relative pose: translate (1,2), then roate 30 degree *)
  Let trans_example1 := transl2 (mkvec2 1 2) * trot2 (0.5). (* 30 'deg). *)
End test.
  

(* ########################################################################### *)
(** * Others *)

(** The relationship between pre-multiplying and post-multiplying a rotation matrix,
    i.e., R * u = (u' * R')' *)
Lemma rot2_pre_post : forall (u : vec 2) (θ : R),
    let v1 : vec 2 := (rot2 θ *v u)%V in      (* v1是用列向量形式计算的结果 *)
    let v2 : vec 2 := rv2v (v2rv u * (rot2 θ)\T) in  (* v2是用行向量形式计算的结果 *)
    v1 = v2. (* 结果应该相同 *)
Proof. intros. veq; ra. Qed.

(** Special Euclidean Group of dimension 3: T ∈ SE(2) ⊂ R^(3x3) *)
  (* Record SE2 := { *)
  (*     SE2R :> mat 3 3; *)
  (*     _ : orthonormal2 SO2R *)
  (*   }. *)
