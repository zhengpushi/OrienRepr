(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Orientation in 2D
  author    : ZhengPu Shi
  date      : 2023.04.01

 *)

Require Export MathBase.
Import V2Notations.


(* ########################################################################### *)
(** * Preliminary math *)

(** Transformation by SO(n) matrix will keep v2cross. *)
Lemma SOn_keep_v2cross : forall (M : smat 2) (u v : vec 2),
    SOnP M -> (M *v u) \x (M *v v) = u \x v.
Proof.
  intros. cbv. ring_simplify.
  assert (M.11 * M.22 - M.12 * M.21 = 1)%R.
  { destruct H as [Horth Hdet1]. cbv in Hdet1. ring_simplify in Hdet1. cbv. lra. }
  assert (M.11 * u.1 * M.22 * v.2 - M.11 * u.2 * v.1 * M.22 -
            u.1 * M.12 * M.21 * v.2 + M.12 * u.2 * M.21 * v.1 =
            (u.1 * v.2 - u.2 * v.1) * (M.11 * M.22 - M.12 * M.21))%R. lra.
  assert (M.11 * u.1 * M.22 * v.2 - M.11 * u.2 * v.1 * M.22 -
            u.1 * M.12 * M.21 * v.2 + M.12 * u.2 * M.21 * v.1 =
            u.1 * v.2 - u.2 * v.1)%R; auto.
  rewrite H1. rewrite H0. lra.
Qed.

(** Transformation by SO(n) matrix will keep vangle2. *)
Lemma SOn_keep_vangle2 : forall (M : smat 2) (u v : vec 2),
    SOnP M -> (M *v u) /2_ (M *v v) = u /2_ v.
Proof.
  intros. unfold vangle2. rewrite SOn_keep_v2cross; auto.
  rewrite morth_keep_angle; auto. apply H.
Qed.

(* ########################################################################### *)
(** * Skew-symmetric matrix in 2-D *)

(** Equivalent form of skewP of 2D vector *)
Lemma skewP2_eq : forall M : smat 2,
    skewP M <->
      (M.11 = 0) /\ (M.22 = 0) /\ (M.12 = -M.21)%R.
Proof.
  intros. split; intros.
  - hnf in H. assert (m2l (- M) = m2l (M\T))%M. rewrite H; auto.
    cbv in H0. list_eq. cbv in *. ra.
  - apply m2l_inj. cbv in *. list_eq; ra.
Qed.

(** Create a skew-symmetric matrix in 2D with a value *)
Definition skew2 (a : R) : mat 2 2 := l2m [[0; -a];[a; 0]]%R.

Lemma skew2_spec : forall a, skewP (skew2 a).
Proof. intros. rewrite skewP2_eq. cbv. lra. Qed.

(** Convert a skew-symmetric matrix in 2D to its corresponding value *)
Definition vex2 (M : mat 2 2) : R := M.21.

Lemma skew2_vex2 : forall (M : mat 2 2), skewP M -> skew2 (vex2 M) = M.
Proof. intros. rewrite skewP2_eq in H. cbv in H. meq; ra. Qed.

Lemma vex2_skew2 : forall (a : R), vex2 (skew2 a) = a.
Proof. intros. cbv. auto. Qed.


(* ########################################################################### *)
(** * Orientation in 2D (pure rotation) *)

(* ======================================================================= *)
(** ** 2-D Rotation matrix *)

Open Scope mat_scope.

(** 创建了一个2D旋转矩阵：
   1. 该矩阵是标准正交的，即行向量相互正交，列向量相互正交，并且长度都是1.
   2. 其列向量是旋转后的坐标系的坐标轴关于原坐标系的单位向量
   3. 它属于SO(2)，这表明任意两个这样的矩阵相乘，以及逆都在SO(2)中。
   4. 行列式是1，这表明，一个向量被变换后其长度不改变。
   5. 逆矩阵是其转置。
   6. 该矩阵的四个元素并不独立，实际上只有一个参数theta。这是非最小表示的一个例子，
      缺点是占用更多存储空间，优点是可组合性(composability)
   7. 如何使用该矩阵来变换向量？见 operations
 *)
(** Created a 2D rotation matrix:
   1. This matrix is standard orthogonal, i.e., its row vectors are mutually orthogonal,
      its column vectors are mutually orthogonal, and all have unit length.
   2. Its column vectors are the unit vectors of the rotated coordinate axes with respect
      to the original coordinate system.
   3. It belongs to SO(2), which means that the product and inverse of any two such matrices
      are also in SO(2).
   4. The determinant is 1, indicating that the length of a vector does not change after
      transformation.
   5. The inverse matrix is its transpose.
   6. The four elements of this matrix are not independent; in fact, it has only one
      parameter theta. This is an example of a non-minimal representation, with the drawback
      of requiring more storage space but the advantage of composability.
   7. How to use this matrix to transform vectors? See `2D rotation operations`.
 *)

Definition rot2 (theta : R) : smat 2 :=
  (mkmat_2_2
     (cos theta) (- sin theta)
     (sin theta) (cos theta))%R.

(** rot2 is orthogonal matrix *)
Lemma rot2_orth : forall (θ : R), morth (rot2 θ).
Proof. intros; meq; ra. Qed.

(** The determinant of rot2 is 1 *)
Lemma rot2_det1 : forall (θ : R), mdet (rot2 θ) = 1.
Proof. intros; cbv; ra. Qed.

(** rot2 satisfies SOnP *)
Lemma rot2_SOnP : forall (θ : R), SOnP (rot2 θ).
Proof. intros. hnf. split. apply rot2_orth. apply rot2_det1. Qed.

(** rot2 is a member of SO2 *)
Definition rot2_SO2 (θ : R) : SO2 := mkSOn (rot2 θ) (rot2_SOnP θ).

(** rot2 is invertible *)
Lemma rot2_minvtble : forall (θ : R), minvtble (rot2 θ).
Proof. intros. apply morth_minvtble. apply rot2_orth. Qed.

(** rot2\-1 = rot2\T *)
Lemma rot2_inv_eq_trans : forall θ : R, (rot2 θ)\-1 = (rot2 θ)\T.
Proof.
  (* method 1 : prove by computing (slow) *)
  (* intros; meq; ra. *)
  (* method 2 : prove by reasoning *)
  intros; apply (SOn_minv_eq_trans (rot2_SO2 θ)).
Qed.

(** rot2 * rot2\-1 = I *)
Lemma rot2_mul_rot2_inv : forall θ : R, rot2 θ * ((rot2 θ)\-1) = mat1.
Proof. intros. apply mmul_minvAM_r. apply rot2_minvtble. Qed.

(** rot2\-1 * rot2 = I *)
Lemma rot2_inv_mul_rot2 : forall θ : R, (rot2 θ)\-1 * (rot2 θ) = mat1.
Proof. intros. apply mmul_minv_l. apply rot2_minvtble. Qed.

(** rot2 * rot2\T = I *)
Lemma rot2_mul_rot2_trans : forall θ : R, rot2 θ * ((rot2 θ)\T) = mat1.
Proof. intros. rewrite <- rot2_inv_eq_trans. apply rot2_mul_rot2_inv. Qed.

(** rot2\T * rot2 = I *)
Lemma rot2_trans_mul_rot2 : forall θ : R, (rot2 θ)\T * (rot2 θ) = mat1.
Proof. intros. rewrite <- rot2_inv_eq_trans. apply rot2_inv_mul_rot2. Qed.

(** rot2(θ1) * rot2(θ2) = rot2(θ1 + θ2) *)
Lemma rot2_eq_add : forall (θ1 θ2 : R), (rot2 θ1) * (rot2 θ2) = rot2 (θ1 + θ2).
Proof. intros; meq; ra. Qed.

(** rot2(θ1) * rot2(θ2) = rot2(θ2) * rot2(θ1) *)
Lemma rot2_comm : forall (θ1 θ2 : R), (rot2 θ1) * (rot2 θ2) = (rot2 θ2) * (rot2 θ1).
Proof. intros; meq; ra. Qed.

(** rot2(-θ) = rot2(θ)\-1 *)
Lemma rot2_neg_eq_inv : forall θ : R, rot2 (-θ) = (rot2 θ)\-1.
Proof. intros. symmetry. apply mmul_eq1_imply_minvAM_r. meq; ra. Qed.

(** rot2(-θ) = rot2(θ)\T *)
Lemma rot2_neg_eq_trans : forall θ : R, rot2 (-θ) = (rot2 θ)\T.
Proof. intros; meq; ra. Qed.


(* ======================================================================= *)
(** ** Definition of 2D rotation operations *)

Open Scope vec_scope.

(* Given two coordinate frames, the world frame {W} and the body frame
   {B}, where {B} is rotated by an angle of theta relative to {W}, the
   coordinates of a vector v in these two coordinate frames are w and
   b, respectively. The following relationship holds:
      w = rot2(theta) * b
      b = rot2(theta)^T * w

  Assuming there are two coordinate systems, the world coordinate system {W} and the
  body coordinate system {B}, and {B} is rotated by an angle theta relative to {W},
  the coordinates of a vector v in these two coordinate systems, w and b respectively,
  satisfy the following relationships:
    w = rot2(theta) * b,
    b = rot2(theta)' * w.
 *)
Definition world4rot (theta : R) (b : vec 2) : vec 2 := rot2 theta *v b.
Definition body4rot (theta : R) (w : vec 2) : vec 2 := (rot2 theta)\T *v w.

(* In a coordinate frame, if the coordinates of a vector are `a` and
   the vector is rotated by an angle of `theta`, the coordinates after
   rotation are `b`. The following relationship holds:
      b = rot2(theta) * a
      a = rot2(theta)^T * b *)
Definition afterRot (theta : R) (a : vec 2) : vec 2 := rot2 theta *v a.
Definition beforeRot (theta : R) (b : vec 2) : vec 2 := (rot2 theta)\T *v b.


(* ======================================================================= *)
(** ** Properties for 2D rotation operations *)

(** world4rot . body4rot = id *)
Lemma world4rot_body4rot : forall theta w, world4rot theta (body4rot theta w) = w.
Proof.
  intros. unfold world4rot, body4rot. rewrite <- mmulv_assoc.
  rewrite rot2_mul_rot2_trans, mmulv_1_l. auto.
Qed.

(** body4rot . world4rot = id *)
Lemma body4rot_world4rot : forall theta b, body4rot theta (world4rot theta b) = b.
Proof.
  intros. unfold world4rot, body4rot. rewrite <- mmulv_assoc.
  rewrite rot2_trans_mul_rot2, mmulv_1_l. auto.
Qed.

(** world4rot (-θ) = body4rot(θ) *)
Lemma world4rot_neg_eq_body4rot : forall theta v,
    world4rot (-theta) v = body4rot theta v.
Proof.
  intros. unfold world4rot, body4rot. rewrite rot2_neg_eq_trans. auto.
Qed.

(** Two 2-D rotations equal to once with the addition of the angles *)
Lemma world4rot_twice : forall (theta1 theta2 : R) (v : vec 2),
    world4rot theta2 (world4rot theta1 v) =
      world4rot (theta1 + theta2) v.
Proof.
  intros. unfold world4rot. rewrite <- mmulv_assoc.
  rewrite rot2_eq_add. rewrite Rplus_comm. auto.
Qed.

(** The order of two 2-D rotations does not matter *)
Lemma world4rot_anyOrder : forall (θ1 θ2 : R) (v : vec 2),
    world4rot θ2 (world4rot θ1 v) = world4rot θ1 (world4rot θ2 v).
Proof. intros. rewrite !world4rot_twice. f_equal. ring. Qed.

(* we can easily prove the similiarly properties for other operations *)


(* ======================================================================= *)
(** ** Specifications for 2-D rotation operations *)

(** The coordinate change of the same vector in two coordinate systems *)
Section spec_TwoFrame.
  Open Scope mat_scope.
  
  (* 参考了 RVC 书中 2.1.1.1 节的方法 *)

  (* 命题：
     任意二维平面中的原点重合的两个坐标系{W}和{B}，{W}旋转theta后到达{B}，
     某向量 OP 在 {W} 和 {B} 下的坐标分别为 w 和 b，证明：
     w = world4rot(theta,b) 以及 b=body4rot(theta,w) *)
  
  Variable xw' yw' : vec 2.   (* 坐标系 {W} 的坐标轴单位向量 *)
  Hypotheses xw'yw'_orth : morth (cvl2m [xw';yw']). (* {W}的坐标轴是正交的 *)
  Variable xb' yb' : vec 2.   (* 坐标系 {B} 的坐标轴单位向量 *)
  Hypotheses xb'yb'_orth : morth (cvl2m [xb';yb']). (* {B}的坐标轴是正交的 *)
  Variable theta : R.         (* 坐标系{W}旋转theta角后到{B} *)
  Hypotheses Hxb' :           (* xb'由 theta 和 {xw,yw} 表示 *)
    xb' = (cos theta c* xw' + sin theta c* yw')%V.
  Hypotheses Hyb' :           (* yb'由 theta 和 {xw,yw} 表示 *)
    yb' = ((- sin theta)%R c* xw' + cos theta c* yw')%V.
  
  Variable p : vec 2.        (* 任意P点 *)
  Variable w : vec 2.        (* P点在 {W} 下的坐标 *)
  Variable b : vec 2.        (* P点在 {B} 下坐标 *)
  Hypotheses Hpw : p = (w.1 c* xw' + w.2 c* yw')%V. (* P点在{W}中的表示 *)
  Hypotheses Hpb : p = (b.1 c* xb' + b.2 c* yb')%V. (* P点在{B}中的表示 *)

  (* Hxb' 和 Hyb' 的矩阵形式，公式(2.4) *)
  Fact Hxb'Hyb' : cvl2m [xb';yb'] = (cvl2m [xw';yw']) * rot2 theta.
  Proof. subst. meq; ra. Qed.
  
  (* Hxw' 和 Hyw' 的矩阵形式 *)
  Fact Hxw'Hyw' : @cvl2m 2 2 [xw';yw'] = (cvl2m [xb';yb']) * (rot2 theta)\T.
  Proof.
    assert (cvl2m [xb'; yb'] * (rot2 theta)\T =
              cvl2m [xw'; yw'] * rot2 theta * (rot2 theta)\T).
    { rewrite Hxb'Hyb'. auto. }
    rewrite mmul_assoc in H. rewrite rot2_mul_rot2_trans, mmul_1_r in H. auto.
  Qed.

  (* Hpv 的矩阵形式 *)
  Fact HpwM : p = @cvl2m 2 2 [xw';yw'] *v w.
  Proof. rewrite Hpw. veq; ra. Qed.
  
  (* Hpb 的矩阵形式 *)
  Fact HpbM : p = @cvl2m 2 2 [xb';yb'] *v b.
  Proof. rewrite Hpb. veq; ra. Qed.
  
  (* p 用 {xw',yw'} 和 b 的矩阵乘法表示，公式(2.5) *)
  Fact p_w_b : p = (cvl2m [xw';yw'] * rot2 theta)%M *v b.
  Proof. rewrite HpbM. f_equal. f_equal. apply Hxb'Hyb'. Qed.
  
  (* p 用 {xb',yb'} 和 w 的矩阵乘法表示 *)
  Fact p_b_w : p = (cvl2m [xb';yb'] * (rot2 theta)\T)%M *v w.
  Proof. rewrite HpwM. f_equal. f_equal. apply Hxw'Hyw'. Qed.
  
  Lemma world4rot_spec : w = world4rot theta b.
  Proof.
    unfold world4rot.
    assert (@cvl2m 2 2 [xw';yw'] *v w =
              (cvl2m [xw';yw'] * rot2 theta)%M *v b).
    { rewrite <- HpwM. rewrite <- p_w_b. auto. }
    rewrite mmulv_assoc in H. apply mmulv_cancel in H; auto.
    apply morth_minvtble; auto.
  Qed.
  
  Lemma body4rot_spec : b = body4rot theta w.
  Proof.
    unfold body4rot.
    assert (@cvl2m 2 2 [xb';yb'] *v b =
              (cvl2m [xb';yb'] * (rot2 theta)\T)%M *v w)%V.
    { rewrite <- HpbM. rewrite <- p_b_w. auto. }
    rewrite mmulv_assoc in H. apply mmulv_cancel in H; auto.
    apply morth_minvtble; auto.
  Qed.
End spec_TwoFrame.

(** The coordinate change of a vector before and after rotation in the same coordinate system *)
Section spec_OneFrame.

  (* 命题：
     任给二维平面及坐标系{0}，坐标原点为O，某非零点P，向量OP的坐标为a，
     当将OP绕正方向旋转theta角后到达OP'，OP'坐标为b，证明：
     b = afterRot(theta,a) 以及  a = beforeRot(theta,b) *)

  Context (a : vec 2). (* 任给OP在{0}下的坐标a *)
  Context (theta : R). (* 任给旋转角theta *)
  Hypotheses Hneq0 : a <> vzero. (* 假定OP是非零向量 *)
  Let l := ||a||.        (* OP的长度 *)
  Let alpha := v2i /2_ a.       (* x轴正方向到OP的角度, [0, 2PI) *)
  Let b_x := (l * cos (alpha + theta))%R.   (* OP'的横坐标 *)
  Let b_y := (l * sin (alpha + theta))%R.   (* OP'的纵坐标 *)
  Let b : vec 2 := l2v [b_x;b_y].           (* OP'的坐标 *)

  Lemma afterRot_spec : b = afterRot theta a.
  Proof.
    (* convert the equality of matrix to element-wise equalities *)
    intros. unfold b,b_x,b_y,afterRot. apply v2l_inj. rewrite v2l_l2v; auto.
    replace (v2l (rot2 theta *v a))
      with [a.1 * (cos theta) + a.2 * (- sin theta);
            a.1 * (sin theta) + a.2 * (cos theta)]%R.
    2:{ cbv. list_eq; ra. } list_eq.
    (* proof equality of element *)
    - rewrite cos_add. unfold alpha, Rminus, l. ring_simplify.
      rewrite v2len_mul_cos_vangle2_i; auto.
      rewrite v2len_mul_sin_vangle2_i; auto. lra.
    - rewrite sin_add. unfold alpha, l. ring_simplify.
      rewrite v2len_mul_cos_vangle2_i; auto.
      rewrite v2len_mul_sin_vangle2_i; auto. lra.
  Qed.

  Lemma beforeRot_spec : a = beforeRot theta b.
  Proof.
    (* convert the equality of matrix to element-wise equalities *)
    intros. unfold b,b_x,b_y,beforeRot. apply v2l_inj.
    replace (v2l a) with [a.1; a.2]; [|cbv; auto].
    replace (v2l (((rot2 theta)\T *v
                     (l2v [(l * cos (alpha + theta))%R;
                           (l * sin (alpha + theta))%R]))))
      with [
        (cos theta) * l * cos (alpha + theta) +
          (sin theta) * l * sin (alpha + theta);
        - (sin theta) * l * cos (alpha + theta) +
          (cos theta) * l * sin (alpha + theta)]%R.
    2:{ Local Opaque cos sin vlen vangle2. cbv; list_eq; ra. } list_eq.
    (* proof equality of element *)
    - (* Tips: `a.1` and `a.2` is A type, making `ring` will fail. *)
      remember ((a (nat2finS 0)) : R) as a_x.
      rewrite cos_add, sin_add; unfold alpha, Rminus, l. ring_simplify.
      rewrite associative. rewrite v2len_mul_cos_vangle2_i; ra.
    - remember ((a (nat2finS 1)) : R) as a_y.
      rewrite cos_add, sin_add; unfold alpha, Rminus, l. ring_simplify.
      replace ((||a||) * cos theta ^ 2 * sin (v2i /2_ a))%R
        with (cos theta ^ 2 * (||a|| * sin (v2i /2_ a)))%R; ra.
      rewrite associative. rewrite v2len_mul_sin_vangle2_i; ra.
  Qed.
End spec_OneFrame.
