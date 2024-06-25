(*
  Copyright 2023 Zhengpu Shi
  This file is part of OrienRepr. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Quaternion
  author    : Zhengpu Shi
  date      : 2022.06

  remark    :
  * quat := mkQ {W:R, X:R, Y:R, Z:R}
  * q2v : quat -> vec 4
    q2im : quat -> vec 3
    v2q : vec 4 -> quat
    im2q : vec 3 -> quat
    si2q : R -> vec 3 -> quat

  reference :
  1. (QQ) Introduction to Multicopter Design and Control, Springer, Quan Quan, page 96
  2. (Dunn) 3D Math Primer for Graphics and Game Development, Second Edition
     Fletcher Dunn, Ian Parberry.
  3. (Krasjet) Quaternion and 3D rotation（四元数与三维旋转）
 *)

Require Export MathBase.
Require Export AxisAngle.

(** Scope for quaternion *)
Declare Scope quat_scope.
Delimit Scope quat_scope with quat.
Open Scope quat_scope.


(* ######################################################################### *)
(** * Definition of Quaternion *)

(** A quaternion q = w + x i + y j + z k, can be considered as a linear 
    combination with the basis of {1, i, j, k} *)
Record quat : Type := mkQ { W : R; X : R; Y : R; Z : R }.
Bind Scope quat_scope with quat.

Notation "q .W" := (W q) (at level 30, format "q .W") : quat_scope.
Notation "q .X" := (X q) (at level 30, format "q .X") : quat_scope.
Notation "q .Y" := (Y q) (at level 30, format "q .Y") : quat_scope.
Notation "q .Z" := (Z q) (at level 30, format "q .Z") : quat_scope.

Lemma quat_eq_iff : forall (q1 q2 : quat),
    q1 = q2 <-> (q1.W = q2.W /\ q1.X = q2.X /\ q1.Y = q2.Y /\ q1.Z = q2.Z).
Proof.
  intros. split; intros; subst; auto.
  do 3 destruct H as [? H]. destruct q1,q2; simpl in *. f_equal; auto.
Qed.

Lemma quat_neq_iff : forall (q1 q2 : quat),
    q1 <> q2 <-> (q1.W <> q2.W \/ q1.X <> q2.X \/ q1.Y <> q2.Y \/ q1.Z <> q2.Z).
Proof. intros. rewrite quat_eq_iff. tauto. Qed.

(** Get the component of a given quaternion number q *)
(* Definition Re (q : quat) : R := q.W. *)
(* Definition Im1 (q : quat) : R := q.X. *)
(* Definition Im2 (q : quat) : R := q.Y. *)
(* Definition Im3 (q : quat) : R := q.Z. *)

(** Make a quaternion from real part *)
Definition s2q (w : R) : quat := mkQ w 0 0 0.

Lemma s2q_spec : forall w,
    let q := s2q w in
    q.W = w /\ q.X = R0 /\ q.Y = R0 /\ q.Z = R0.
Proof. intros. cbv. auto. Qed.

(** Make a quaternion from real part and imaginary part *)
Definition si2q (w : R) (v : vec 3) : quat := mkQ w (v.1) (v.2) (v.3).

Lemma si2q_spec : forall w v,
    let q := si2q w v in
    q.W = w /\ q.X = v.1 /\ q.Y = v.2 /\ q.Z = v.3.
Proof. intros. v2e v. cbv in *. rewrite Ha. auto. Qed.

(** si2q is injective *)
Lemma si2q_inj : forall w1 w2 v1 v2,
    si2q w1 v1 = si2q w2 v2 -> w1 = w2 /\ v1 = v2.
Proof.
  intros. unfold si2q in H. inversion H. split; auto. apply v3eq_iff; auto.
Qed.

(** Convert between quaternion and 4-dim vector *)
Definition q2v (q:quat) : vec 4 := l2v [q.W; q.X; q.Y; q.Z].
Definition v2q (v:vec 4) : quat := mkQ (v.1) (v.2) (v.3) (v.4).

Lemma q2v_spec : forall q,
    let v := q2v q in
    v.1 = q.W /\ v.2 = q.X /\ v.3 = q.Y /\ v.4 = q.Z.
Proof. intros. destruct q. cbv in *. auto. Qed.

Lemma v2q_spec : forall v,
    let q := v2q v in
    v.1 = q.W /\ v.2 = q.X /\ v.3 = q.Y /\ v.4 = q.Z.
Proof. intros. unfold q. v2e v. cbv in *. auto. Qed.

Lemma q2v_v2q : forall v, q2v (v2q v) = v.
Proof. intros. veq. Qed.

Lemma v2q_q2v : forall q, v2q (q2v q) = q.
Proof. intros. destruct q; auto. Qed.

(** Convert between pure imaginary quanternion and 3-dim vector *)
Definition q2im (q : quat) : vec 3 := l2v [q.X; q.Y; q.Z].
Notation "q .Im" := (q2im q) (at level 30, format "q .Im") : quat_scope.

Definition im2q (v : vec 3) : quat := mkQ 0 (v.1) (v.2) (v.3).

(** q2im (im2q v) = v *)
Lemma q2im_im2q : forall v, q2im (im2q v) = v.
Proof. intros. veq. Qed.

(** q.W = 0 -> im2q (q2im q) = q *)
Lemma im2q_q2im : forall q, q.W = 0 -> im2q (q2im q) = q.
Proof. intros. destruct q. cbv in *. f_equal. auto. Qed.

(* q1.W = q2.W -> q1.Im = q2.Im -> q1 = q2 *)
Lemma qeq_if_W_Im : forall q1 q2, q1.W = q2.W -> q1.Im = q2.Im -> q1 = q2.
Proof.
  intros. unfold q2im in *. destruct q1,q2. simpl in *.
  apply v3eq_iff in H0. cbv in H0. logic.
Qed.


(** ** Automation for quaternion *)

(** Linear Quaternion Algebra, q1 = q2. *)
Ltac lqa (* tac *) :=
  cbv; f_equal; ra.


(* ######################################################################### *)
(** * Quaternion operations *)

(** ** Zero quaternion 零四元数 *)

(** Make a quaternion with all components are 0 *)
Definition qzero : quat := mkQ 0 0 0 0.

(** im2q v = qzero <-> v = vzero *)
Lemma im2q_eq0_iff : forall v, im2q v = qzero <-> v = vzero.
Proof.
  intros. v2e v. ra.
  - cbv in H. inv H. veq.
  - cbv. cbv in H. apply v3eq_iff in H. simpl in *. logic.
Qed.

(** im2q v <> qzero <-> v <> vzero *)
Lemma im2q_neq0_iff : forall v, im2q v <> qzero <-> v <> vzero.
Proof. intros. rewrite im2q_eq0_iff. tauto. Qed.


(** ** Square of magnitude (Length) of a quaternion *)

(** Get square of magnitude (length) of a quaternion *)
Definition qlen2 (q : quat) : R :=
  q.W * q.W + q.X * q.X + q.Y * q.Y + q.Z * q.Z.

(** 0 <= qlen2 q *)
Lemma qlen2_ge0 : forall (q : quat), (0 <= qlen2 q)%R.
Proof. intros. destruct q. unfold qlen2. simpl. ra. Qed.

(** q = qzero <-> qlen2 q = 0 *)
Lemma qlen2_eq0_iff : forall q : quat, qlen2 q = 0 <-> q = qzero.
Proof.
  intros. destruct q. rewrite quat_eq_iff. cbv.
  autorewrite with R. rewrite Rplus4_sqr_eq0. auto.
Qed.

(** q <> qzero <-> qlen2 q <> 0 *)
Lemma qlen2_neq0_iff : forall q : quat, qlen2 q <> 0 <-> q <> qzero.
Proof. intros. unfold not. rewrite qlen2_eq0_iff. easy. Qed.


(** ** Magnitude (Length) of a quaternion *)

(** Get magnitude (length) of a quaternion *)
Definition qlen (q : quat) : R := sqrt (qlen2 q). 
Notation "|| q ||" := (qlen q) : quat_scope.

(** (||q||)² = qlen2 q *)
Lemma sqr_qlen : forall q : quat, (||q||)² = qlen2 q.
Proof. intros. unfold qlen. rewrite Rsqr_sqrt; ra. unfold qlen2. ra. Qed.

(** 0 <= ||q|| *)
Lemma qlen_ge0 : forall q : quat, 0 <= ||q||.
Proof. intros. unfold qlen. ra. Qed.

(** || q || = 0 <-> q = qzero *)
Lemma qlen_eq0_iff : forall q : quat, || q || = 0 <-> q = qzero.
Proof.
  intros. unfold qlen.
  rewrite sqrt_eq0_iff. rewrite <- qlen2_eq0_iff. pose proof (qlen2_ge0 q). ra.
Qed.

(** || q || <> 0 <-> q <> qzero *)
Lemma qlen_neq0_iff : forall q : quat, || q || <> 0 <-> q <> qzero.
Proof.
  intros. unfold qlen.
  rewrite sqrt_neq0_iff. rewrite <- qlen2_eq0_iff. pose proof (qlen2_ge0 q). ra.
Qed.

(** || q1 || = || q2 || <-> qlen2 q1 = qlen2 q2 *)
Lemma qlen_eq_iff_qlen2_eq : forall q1 q2 : quat,
    || q1 || = || q2 || <-> qlen2 q1 = qlen2 q2.
Proof.
  intros. rewrite <- !sqr_qlen. split; intros; ra.
  apply Rsqr_inj; auto. all: apply qlen_ge0.
Qed.


(** ** Unit quaternion *)

(** A unit quaternion has a magnitude equal to 1 *)
Definition qunit (q : quat) : Prop := ||q|| = 1.

(** vunit v -> qunit [0,v] *)
Lemma im2q_qunit : forall v : vec 3, vunit v -> qunit (im2q v).
Proof.
  intros. v2e v. cbv in H. cbv. ra. rewrite associative. rewrite H. ra.
Qed.

(** qunit q <-> qlen2 q = 1 *)
Lemma qunit_iff_qlen2_eq1 : forall q : quat, qunit q <-> qlen2 q = 1.
Proof. intros. unfold qunit, qlen, qlen2 in *. split; intros; ra. Qed.

(** qunit q -> q.W ^ 2 = 1 - q.X ^ 2 - q.Y ^ 2 - q.Z ^ 2 *)
Lemma qunit_imply_W : forall q : quat,
    qunit q -> q.W ^ 2 = (1 - q.X ^ 2 - q.Y ^ 2 - q.Z ^ 2)%R.
Proof. intros. apply qunit_iff_qlen2_eq1 in H. rewrite <- H. cbv. ring. Qed.

(** qunit q -> q.W ^ 2 + q.X ^ 2 + q.Y ^ 2 + q.Z ^ 2 = 1 *)
Lemma qunit_imply_Im : forall q : quat,
    qunit q -> (q.W ^ 2 + q.X ^ 2 + q.Y ^ 2 + q.Z ^ 2 = 1)%R.
Proof. intros. apply qunit_iff_qlen2_eq1 in H. rewrite <- H. cbv. ring. Qed.

(** qunit q -> q <> qzero *)
Lemma qunit_neq0 : forall q : quat, qunit q -> q <> qzero.
Proof. intros. apply qlen_neq0_iff. intro. unfold qunit in H. lra. Qed.

(** q.W = 0 -> vunit (q.Im) -> qunit q *)
Lemma qim_vunit_imply_qunit : forall q : quat, q.W = 0 -> vunit (q.Im) -> qunit q.
Proof. intros. apply qunit_iff_qlen2_eq1. destruct q. simpl in *. cbv in *. ra. Qed.


(** ** Quaternion normalization *)


(** ** Quaternion addition 四元数加法 *)
Definition qadd (q1 q2 : quat) : quat :=
  mkQ (q1.W + q2.W) (q1.X + q2.X) (q1.Y + q2.Y) (q1.Z + q2.Z).
Notation "p + q" := (qadd p q) : quat_scope.


(** ** Quaternion negation 四元数取负 *)
Definition qopp (q : quat) : quat := mkQ (- q.W) (- q.X) (- q.Y) (- q.Z).
Notation "- q" := (qopp q) : quat_scope.


(** ** Quaternion subtraction 四元数减法 *)
Definition qsub (q1 q2 : quat) : quat := qadd q1 (qopp q2).
Notation "p - q" := (qsub p q) : quat_scope.


(** ** Quaternion multiplication *)

(** Quaternion multiplication, also known as "Hamilton product" *)
Definition qmul (q1 q2 : quat) : quat :=
  mkQ
    (q1.W * q2.W - q1.X * q2.X - q1.Y * q2.Y - q1.Z * q2.Z)
    (q1.W * q2.X + q1.X * q2.W + q1.Y * q2.Z - q1.Z * q2.Y) 
    (q1.W * q2.Y - q1.X * q2.Z + q1.Y * q2.W + q1.Z * q2.X) 
    (q1.W * q2.Z + q1.X * q2.Y - q1.Y * q2.X + q1.Z * q2.W).
Notation "p * q" := (qmul p q) : quat_scope.

(** Multiplication of two quaternions by vector form，(p96)
                |pw|   |qw|   |   pw qw - <pv,qv>     |
        p * q = |pv| + |qv| = |pw qv + qw pv + pv × qv|
      This formula is also known Graβmann Product. *)
Lemma qmul_spec (p q : quat) :
  p * q =
    si2q
      (p.W * q.W - <p.Im, q.Im>)
      (p.W s* q.Im + q.W s* p.Im + p.Im \x q.Im)%V.
Proof. destruct p, q. lqa. Qed.

(** qlen2 (q1 * q2) = (qlen2 q1) * (qlen2 q2) *)
Lemma qlen2_qmul : forall (q1 q2 : quat),
    qlen2 (q1 * q2) = ((qlen2 q1) * (qlen2 q2))%R.
Proof. intros. destruct q1,q2. cbv. ring. Qed.

(** || q1 * q2 || = ||q1|| * ||q2|| *)
Lemma qlen_qmul : forall (q1 q2 : quat), || q1 * q2 || = (||q1|| * ||q2||)%R.
Proof.
  intros. apply Rsqr_inj. apply qlen_ge0. apply Rmult_le_pos; apply qlen_ge0.
  autorewrite with R. rewrite !sqr_qlen. destruct q1,q2; cbv; ring.
Qed.

(** qunit p -> qunit q -> qunit (p * q) *)
Lemma qmul_qunit (p q : quat) : qunit p -> qunit q -> qunit (p * q).
Proof.
  intros. destruct p,q. unfold qunit. rewrite qlen_qmul. rewrite H,H0. ring.
Qed.

(** (q * r) * m = q * (r * m) *)
Lemma qmul_assoc (q r m : quat) : (q * r) * m = q * (r * m).
Proof. destruct q,r,m. lqa. Qed.

(** The multiplication is non-commutative. That is: p * q <> q * p. *)
Lemma qmul_comm_fail : exists (p q : quat), p * q <> q * p.
Proof.
  exists (mkQ 0 1 2 1).
  exists (mkQ 0 2 1 2).
  cbv. intros. inversion H. lra.
Qed.

(** q * (r + m) = q * r + q * m *)
Lemma qmul_qadd_distr_l (q r m : quat) : q * (r + m) = q * r + q * m.
Proof. destruct q,r,m. lqa. Qed.

(** (r + m) * q = r * q + m * q *)
Lemma qmul_qadd_distr_r (r m q : quat) : (r + m) * q = r * q + m * q.
Proof. destruct r,m,q. lqa. Qed.

(** multplication of two pure quaternions: (0,u) * (0,v) = (-<u,v>, u × v)  *)
Lemma qmul_im2q_eq (u v : vec 3) :
  (im2q u) * (im2q v) = si2q (- <u,v>) (u \x v).
Proof. lqa. Qed.

(** (s1,0) * (s2,0) = (s1*s2,0) *)
Lemma qsqr_s2q : forall s1 s2 : R,
    (s2q s1) * (s2q s2) = s2q (s1 * s2).
Proof. intros. lqa. Qed.

(** vunit u -> (0,u) * (0,u) = (-1,0) *)
Lemma qsqr_im2q : forall v : vec 3,
    vunit v -> (im2q v) * (im2q v) = s2q (-1).
Proof.
  intros. pose proof (v3unit_sqr_x v H).
  v2e v. cbv in H0. cbv. rewrite H0. lqa.
Qed.

(** Left scalar multiplication *)
Definition qscal (a : R) (q : quat) : quat :=
  mkQ (a * q.W) (a * q.X) (a * q.Y) (a * q.Z).
Notation "a s* q" := (qscal a q) : quat_scope.

(** 1 s* q = q *)
Lemma qscal_1_l : forall q : quat, 1 s* q = q.
Proof. intros. destruct q. lqa. Qed.

(** (a s* p) * q = a s* (p * q) *)
Lemma qmul_qscal_l : forall (a : R) (p q : quat), (a s* p) * q = a s* (p * q).
Proof. intros. destruct p,q. lqa. Qed.

(** p * (a s* q) = a s* (p * q) *)
Lemma qmul_qscal_r : forall (a : R) (p q : quat), p * (a s* q) = a s* (p * q).
Proof. intros. destruct p,q. lqa. Qed.

(** a s* (b s* q) = (a * b) s* q *)
Lemma qscal_assoc : forall (a b : R) (q : quat), a s* (b s* q) = (a * b) s* q.
Proof. intros. destruct q. lqa. Qed.

(** qlen2 (a s* q) = a² * (qlen2 q) *)
Lemma qlen2_qscal : forall (a : R) (q : quat), qlen2 (a s* q) = (a² * (qlen2 q))%R.
Proof. intros. destruct q. cbv. ring. Qed.

(** a s* q = qzero <-> (a = 0) \/ (q = qzero) *)
Lemma qscal_eq0_iff : forall (q : quat) (a : R),
    a s* q = qzero <-> (a = 0) \/ (q = qzero).
Proof. intros. destruct q. rewrite !quat_eq_iff; simpl. ra. Qed.

(** a s* q <> qzero <-> (a <> 0) /\ (q <> qzero) *)
Lemma qscal_neq0_iff : forall (q : quat) (a : R),
    a s* q <> qzero <-> (a <> 0) /\ (q <> qzero).
Proof. intros. pose proof(qscal_eq0_iff q a). tauto. Qed.

(** Right scalar multiplication *)
Definition qmulc (q : quat) (s : R) : quat := qscal s q.
Notation "q *s a" := (qmulc q a) : quat_scope.

(** s s* q = q *s s *)
Lemma qscal_eq_qmulc (s : R) (q : quat) : s s* q = q *s s.
Proof. destruct q. lqa. Qed.


(** *** The matrix form of quaternion multiplication *)

(** Quaternion matrix function, also be found in QQ,p96,p+ *)
Definition qmatL (q : quat) : smat 4 :=
  let (w,x,y,z) := q in
  l2m [[w; -x; -y; -z];
       [x; w; -z; y];
       [y; z; w; -x];
       [z; -y; x; w]]%R.

(** Verify the construction *)
Lemma qmatL_spec1 : forall q : quat,
    let m1 : smat 4 := (q.W s* mat1)%M in
    let m2a : vec 4 := vconsH 0 (-(q.Im))%V in
    let m2b : mat 3 4 := mconscH (q.Im) (skew3 (q.Im)) in
    let m2 : smat 4 := mconsrH m2a m2b in
    qmatL q = (m1 + m2)%M.
Proof. destruct q. meq; ra. Qed.

(** p * q = L(p) * q *)
Lemma qmatL_spec2 : forall (p q : quat), p * q = v2q ((qmatL p) *v (q2v q))%M.
Proof. intros. destruct p,q. lqa. Qed.

(** Right matrix form of a quaternion, also be found in QQ,p96,p- *)
Definition qmatR (q : quat) : smat 4 :=
  let (w,x,y,z) := q in
  l2m [[w; -x; -y; -z];
       [x; w; z; -y];
       [y; -z; w; x];
       [z; y; -x; w]]%R.

(** Verify the construction *)
Lemma qmatR_spec1 : forall q : quat,
    let m1 : smat 4 := (q.W s* mat1)%M in
    let m2a : vec 4 := vconsH 0 (-q.Im)%V in
    let m2b : mat 3 4 := mconscH (q.Im) (-(skew3 (q.Im)))%M in
    let m2 : smat 4 := mconsrH m2a m2b in
    qmatR q = (m1 + m2)%M.
Proof. destruct q. meq; ra. Qed.

(** p * q = R(q) * p *)
Lemma qmatR_spec2 : forall (p q : quat), p * q = v2q ((qmatR q) *v (q2v p))%M.
Proof. intros. destruct p,q. lqa. Qed.


(** ** Identity quaternion 恒等四元数 *)

(** 恒定四元数：角位移为0的四元数（因为角位移就是朝向的变换，所以这里就是恒等元）

    几何上有两个恒等四元数：(1,0̂) 和 (-1,0̂)
    当 θ 是 2π 的偶数倍时，cos (θ/2) = 1, sin(θ/2) = 0, n̂是任意值
    当 θ 是 2π 的奇数倍时，cos (θ/2) = -1, sin(θ/2) = 0, n̂是任意值
    直观上，若旋转角度是绕任何轴转完整的整数圈，则在三维中方向上不会有任何实际的改变。

    代数上只有一个恒等四元数 [0̂ 1]。因为要求任意 q 乘以单位元后不变。
 *)

(** Make a identity quaternion, i.e., (1,0,0,0) *)
Definition qone : quat := mkQ 1 0 0 0.

(** (-1,0,0,0) *)
Definition qoneNeg : quat := mkQ (-1) 0 0 0.

(** ToDo: 是否可证只有 qone 是唯一的恒等四元数？*)

(** 1 * q = q *)
Lemma qmul_1_l : forall q : quat, qone * q = q.
Proof. intros. destruct q. lqa. Qed.

(** q * 1 = q *)
Lemma qmul_1_r : forall q : quat, q * qone = q.
Proof. intros. destruct q. lqa. Qed.


(** ** Quaternion conjugate *)

(** 当只使用单位四元数时，共轭和逆相等。
      q和q∗ 代表相反的角位移。
      可直观的验证这种想法：q∗使得v变成了-v，所以旋转轴反向，颠倒了正方向，所以是相反的。
 *)

(** Conjugate of a quaternion *)
Definition qconj (q : quat) : quat := si2q (q.W) (- q.Im)%V.

Notation "q \*" := (qconj q) (at level 30) : quat_scope.

(** q \* \* = q *)
Lemma qconj_qconj (q : quat) : q \* \* = q.
Proof. destruct q. lqa. Qed.

(** (im2q v)\* = im2q (-v) *)
Lemma qconj_im2q : forall (v : vec 3), (im2q v)\* = im2q (-v)%V.
Proof. lqa. Qed.

(** (p * q)\* = q\* * p\* *)
Lemma qconj_qmul (p q : quat) : (p * q)\* = q\* * p\*.
Proof. destruct p,q. lqa. Qed.

(** (a s* q)\* = a s* (q\* ) *)
Lemma qconj_qscal : forall (a : R) (q : quat), (a s* q)\* = a s* (q\*).
Proof. intros. lqa. Qed.

(** (p + q)\* = p\* + q\* *)
Lemma qconj_qadd (p q : quat) : (p + q)\* = p\* + q\*.
Proof. destruct p,q. lqa. Qed.

(** q * q\* = q\* * q *)
Lemma qmul_qconj_comm (q : quat) : q * q\* = q\* * q.
Proof. destruct q. lqa. Qed.

(** Im (q\* * q) = 0 *)
Lemma qmul_qconj_l_Im0 (q : quat) : (q\* * q).Im = vzero.
Proof. veq; ra. Qed.

(** Im (q * q\* ) = 0 *)
Lemma qmul_qconj_r_Im0 (q : quat) : (q * q\*).Im = vzero.
Proof. veq; ra. Qed.

(** qunit q -> q\* * q = qone *)
Lemma qunit_qmul_qconj_l : forall q, qunit q -> q\* * q = qone.
Proof.
  intros. apply qeq_if_W_Im.
  - destruct q. cbv in *. ra.
  - rewrite qmul_qconj_l_Im0. veq.
Qed.

(** qunit q -> q * q\* = qone *)
Lemma qunit_qmul_qconj_r : forall q, qunit q -> q * q\* = qone.
Proof. intros. rewrite qmul_qconj_comm. rewrite qunit_qmul_qconj_l; auto. Qed.

(** || q\* || = || q || *)
Lemma qlen_qconj (q : quat) : || q\* || = || q ||.
Proof.
  intros. apply Rsqr_inj; try apply qlen_ge0.
  rewrite !sqr_qlen. destruct q; cbv; ring.
Qed.

(** || q\* * q || = qlen2 q *)
Lemma qlen_qmul_qconj_l : forall (q : quat), || q\* * q || = qlen2 q.
Proof. intros. rewrite qlen_qmul. rewrite qlen_qconj. apply sqr_qlen. Qed.

(** || q * q\* || = qlen2 q *)
Lemma qlen_qmul_qconj_r : forall (q : quat), || q * q\* || = qlen2 q.
Proof. intros. rewrite qlen_qmul. rewrite qlen_qconj. apply sqr_qlen. Qed.

(** qunit q <-> qunit (q\* ) *)
Lemma qconj_qunit : forall (q : quat), qunit (q\*) <-> qunit q.
Proof. intros. unfold qunit. rewrite qlen_qconj. easy. Qed.

(** L(q\* ) = L(q)\T *)
Lemma qmatL_qconj : forall q : quat, qmatL (q\*) = (qmatL q)\T.
Proof. intros. destruct q. meq; ra. Qed.

(** R(q\* ) = R(q)\T *)
Lemma qmatR_qconj : forall q : quat, qmatR (q\*) = (qmatR q)\T.
Proof. intros. destruct q. meq; ra. Qed.

(** L(q) R(q\* ) *)
Definition qmat (q : quat) : smat 4 :=
  let (w,x,y,z) := q in
  l2m [[1; 0; 0; 0];
       [0; 1 - 2*y² - 2*z²; 2*x*y - 2*w*z; 2*w*y + 2*x*z];
       [0; 2*x*y + 2*w*z; 1 - 2*x² - 2*z²; 2*y*z - 2*w*x];
       [0; 2*x*z - 2*w*y; 2*w*x + 2*y*z; 1 - 2*x² - 2*y²]]%R.

(** qunit q -> q v q* = L(q) R(q* ) v *)
Lemma qmat_spec : forall (q v : quat),
    qunit q -> q * v * q\* = v2q ((qmat q) *v (q2v v))%M.
Proof.
  intros. destruct q,v.
  apply qunit_imply_W in H.
  cbv in *. ring_simplify in H. f_equal; ring_simplify; simp_pow.
  all: rewrite H; ra.
Qed.


(** ** Quaternion inverse *)

(** inversion of quaternion *)
Definition qinv (q : quat) : quat := (/ (qlen2 q)) s* (q \*).
Notation "q \-1" := (qinv q) : quat_scope.

(** q \-1 * q = 1 *)
Lemma qmul_qinv_l : forall q : quat, q <> qzero -> q \-1 * q = qone.
Proof.
  intros. destruct q. lqa.
  apply quat_neq_iff in H. apply Rplus4_sqr_neq0. ra.
Qed.

(** q * q \-1 = 1 *)
Lemma qmul_qinv_r : forall q : quat, q <> qzero -> q * q \-1 = qone.
Proof.
  intros. destruct q. lqa.
  apply quat_neq_iff in H. apply Rplus4_sqr_neq0. ra.
Qed.

(** qunit q -> q \-1 = q \* *)
Lemma qinv_eq_qconj : forall q : quat, qunit q -> q \-1 = q \*.
Proof.
  intros. unfold qinv. apply qunit_iff_qlen2_eq1 in H. rewrite H.
  autorewrite with R. rewrite qscal_1_l. auto.
Qed.

(** (p * q)\-1 = q\-1 * p\-1 *)
Lemma qinv_qmul : forall p q : quat, p <> qzero -> q <> qzero -> (p * q)\-1 = q\-1 * p\-1.
Proof.
  intros. unfold qinv. rewrite qconj_qmul.
  rewrite qmul_qscal_l. rewrite qmul_qscal_r. rewrite qscal_assoc. f_equal.
  rewrite qlen2_qmul. field. split; apply qlen2_neq0_iff; auto.
Qed.

(** (a s* q)\-1 = (1/a) s* q\-1 *)
Lemma qinv_qscal : forall (q : quat) (a : R),
    a <> 0 -> q <> qzero -> (a s* q)\-1 = (1/a) s* q\-1.
Proof.
  intros.
  unfold qinv. rewrite qlen2_qscal.
  rewrite qconj_qscal. rewrite !qscal_assoc. f_equal.
  unfold Rsqr. field. apply qlen2_neq0_iff in H0. auto.
Qed.

(** p * q = r -> p = r * q\-1 *)
Lemma qmul_imply_solve_l : forall p q r : quat, q <> qzero -> p * q = r -> p = r * q\-1.
Proof.
  intros. rewrite <- H0. rewrite qmul_assoc, qmul_qinv_r, qmul_1_r; auto.
Qed.

(** p * q = r -> q = p\-1 * r *)
Lemma qmul_imply_solve_r : forall p q r : quat, p <> qzero -> p * q = r -> q = p\-1 * r.
Proof.
  intros. rewrite <- H0. rewrite <- qmul_assoc, qmul_qinv_l, qmul_1_l; auto.
Qed.

(** 以下几个公式是我发现的，或许本质上很简单 *)

(** L(q) * R(q\-1) = R(q\-1) * L(q) *)
Lemma qmul_qL_qR_qinv_comm : forall q,
    let m1 := qmatL q in
    let m2 := qmatR (q\-1) in
    (m1 * m2 = m2 * m1)%M.
Proof. destruct q. meq; ra. Qed.

(** L(q\-1) * L(q)\T = L(q)\T * L(q\-1) *)
Lemma qmul_qL_qinv_qtrans_qL_comm : forall q,
    let m1 := qmatL (q\-1) in
    let m2 := (qmatL q)\T in
    (m1 * m2 = m2 * m1)%M.
Proof. destruct q. meq; ra. Qed.

(** R(q\-1) * L(q)\T = L(q)\T * R(q\-1) *)
Lemma qmul_qR_qinv_qtrans_qL_comm : forall q,
    let m1 := qmatR (q\-1) in
    let m2 := (qmatL q)\T in
    (m1 * m2 = m2 * m1)%M.
Proof. destruct q. meq; ra. Qed.

(** L(q\-1) * R(q\-1) = R(q\-1) * L(q\-1) *)
Lemma qmul_qL_qinv_qR_qinv_comm : forall q,
    let m1 := qmatL (q\-1) in
    let m2 := qmatR (q\-1) in
    (m1 * m2 = m2 * m1)%M.
Proof. destruct q. meq; ra. Qed.


(** ** Divide of quaternion *)

(** 利用除法，可以计算两个给定旋转 a 和 b 之间的某种角位移 d。在 Slerp 时会使用它。*)

(** If r * p = q, then r ≜ q * p\-1 表示从p到q旋转的角位移 *)
Definition qdiv (q p : quat) : quat := p * q\-1.

Lemma qdiv_spec : forall a b : quat, a <> qzero -> (qdiv a b) * a = b.
Proof. intros. unfold qdiv. rewrite qmul_assoc,qmul_qinv_l,qmul_1_r; auto. Qed.



(* ######################################################################### *)
(** * Unit quaternion <-> Axis-Angle *)

(** Unit quaternion and the Axis-Angle representation are bijection. That is,
    every unit quaternion has a corresponded unique axis-angle value,
    every axis-angle value has a corresponded unique unit quaternion. *)

(** Convert axis-angle value to unit quaternion *)
Definition aa2quat (aa : AxisAngle) : quat :=
  let (θ,n) := aa in
  si2q (cos (θ/2)) (sin (θ/2) s* n)%V.

(** Any quaternion constructed from axis-angle is unit quaternion *)
Lemma aa2quat_unit : forall aa : AxisAngle,
    let (θ,n) := aa in
    vunit n -> qunit (aa2quat aa).
Proof.
  intros. destruct aa as [θ n]. intros.
  pose proof (v3unit_sqr_x n H).
  v2e n. cbv. cbv in H0. ra. rewrite H0.
  rewrite sqrt_eq1_if_eq1; auto. ring_simplify. ra.
Qed.
  
(** Convert unit quaternion to axis-angle value *)
Definition quat2aa (q : quat) : AxisAngle :=
  let θ : R := (2 * acos (q.W))%R in
  let n : vec 3 := ((1 / sqrt (1-q.W²)) s* q.Im)%V in
  mkAA θ n.

(** 若q = aa(θ,n) = (cos(θ/2), sin(θ/2)*n) 是单位向量，则：
    (1) 当 q = (1,0,0,0)，则θ为2kπ；否则 θ≠2kπ 且 n 是单位向量。
    (2) 当 q ≠ (1,0,0,0)，则n一定是单位向量 *)
Lemma quat2aa_unit : forall (q : quat) (H : qunit q) (H1 : q <> qone),
    let (θ,n) := quat2aa q in vunit n.
Proof.
  intros.
  pose proof (qunit_imply_W q H).
  destruct q. simpl in *.
  apply quat_neq_iff in H1. simpl in *.
  cbv; ring_simplify. cbv in H0; field_simplify in H0. ra.
  replace ((/ sqrt (1 + - W0²))²) with (/ (1 - W0²)); ra. rewrite H0. field.
  - rewrite <- H0.
Abort.

Lemma aa2quat_quat2aa_id : forall q : quat, aa2quat (quat2aa q) = q.
Proof.
  intros. destruct q. lqa.
Abort.

Lemma quat2aa_aa2quat_id : forall aa : AxisAngle, quat2aa (aa2quat aa) = aa.
Proof.
  intros. destruct aa. lqa.
Abort.



(* ######################################################################### *)
(** * Rotate 3D vector by unit quaternion *)

(** vector v (be wrapped to quaterion) is rotated by a quaternion q.
    Note that: q must be a rotation quaternion *)
(* Definition qrot (q : quat) (v : quat) : quat := q * v * q\-1. *)
Definition qrot (q : quat) (v : quat) : quat := q * v * q\*.

(** vector form of qrot *)
Definition qrotv (q : quat) (v : vec 3) : vec 3 := q2im (qrot q (im2q v)).

(** 证明四元数乘法能够旋转三维矢量 *)

(** 方法1：计算其生成的结果与轴角表示的结果相同，这是大多数文献所采用的方法。*)
Lemma qrot_spec1 : forall (aa : AxisAngle) (v : vec 3),
    vunit (aaAxis aa) ->
    let q := aa2quat aa in
    qrotv q v = rotaa aa v.
Proof.
  intros. destruct aa as [θ n].
  pose proof (v3unit_sqr_x n H).
  v2e n. v2e v. simpl in *.
  unfold q. rewrite Ha in *. cbv in H, H0. veq.
  (* 以下三部分一模一样，但为了看到过程，所以没有全部使用分号策略“;”。*)
  - field_simplify; ra; rewrite H0, cos2; try lra.
    remember (θ / (R1 + R1))%R as α. replace θ with (α + α)%R by lra.
    rewrite cos_plus, sin_plus. unfold Rminus. field_simplify; try lra.
    simp_pow. field_simplify. rewrite cos2. field_simplify; lra.
  - field_simplify; ra; rewrite H0, cos2; try lra.
    remember (θ / (R1 + R1))%R as α. replace θ with (α + α)%R by lra.
    rewrite cos_plus, sin_plus. unfold Rminus. field_simplify; try lra.
    simp_pow. field_simplify. rewrite cos2. field_simplify; lra.
  - field_simplify; ra; rewrite H0, cos2; try lra.
    remember (θ / (R1 + R1))%R as α. replace θ with (α + α)%R by lra.
    rewrite cos_plus, sin_plus. unfold Rminus. field_simplify; try lra.
    simp_pow. field_simplify. rewrite cos2. field_simplify; lra.
Qed.

(** 方法2：QQ书上的推导过程 *)

(* 1. 任给单位四元数q，总能写成
   q = [cos(θ/2), n * sin(θ/2)]
   其中，n是带单位向量，表示旋转轴，θ是旋转的角度，q表示绕n旋转θ。

   我们声称，以下公式能够将任意向量 v 按照q的作用旋转到 v'
   [0,v'] = q⊗[0,v]⊗ q^{-1}
   其中，q是单位四元数。

   下面，证明这个结论。
   1. 第一行可以验证是成立的（即从纯四元数得到了纯四元数）。
      这里其实分了两步，左乘，右乘。每一步都使得w不为0，但两次抵消了。
   2. 经过变换，v' 和 v 的长度不变。
   3. 非零实数s乘以q以后，仍然是相同的作用。
   4. 表示旋转的论证
   (1). 给定两个不相关的3D单位向量 v0 v1 (v0 ≠ ± v1），使得
   1': <v0,v1> = cos(θ/2),即，θ/2 为 v0 到 v1 之间的夹角，
   2': n = cvnorm(v0×v1)
   即，v0,v1是以n为法向量的平面上的一对基向量。
   我们可以得到这些结论：
   n = (v0 × v1) / |v0 × v1| 
   = (v0 × v1) / (|v0| * |v1| * sin(θ/2))
   = (v0 × v1) / sin(θ/2)
   所以，v0 × v1 = v * sin(θ/2)
   所以，q = [<v0,v1>, v0 × v1] = [0,v1] ⊗ [0,v0]*

   (2) 使用四元数旋转公式将v0变换到v1，即：[0,v2] = q⊗[0,v0]⊗q^{-1}
   可证明 [<v1,v2>, v1 × v2] = [0,v2] ⊗ [0,v1]* = q
   于是，现在可知 <v1,v2> = <v0,v1> 且 v1 × v2 = v0 × v1
   这表明：
   v2位于v0和v1所在的平面，且v1与v2夹角是θ/2
   所以对v0作用单位向量q，可看作是把v0绕v旋转θ后得到v2。
     
   (3) 变换v1到v3，即：[0,v3] = q⊗[0,v1]⊗q^{-1}
   可证明 [<v2,v3>, v1 × v2] = [0,v3] ⊗ [0,v2]* = q
   于是，现在可知 <v2,v3> = <v1,v2> 且 v2 × v3 = v1 × v2
   这表明：
   v3位于v1和v2所在的平面，且v2与v3夹角是θ/2
   所以对v1作用单位向量q，可看作是把v1绕v旋转θ后得到v3。
     
   (4) 还可以验证 q ⊗ [0,v] = [0,v] ⊗ q，进一步可验证
   q ⊗ [0,v] ⊗ q* = [0,v] ⊗ q ⊗ q* = [0,v]
   这表明，v是旋转轴（经过作用后没有变化）。

   (5) 任意向量 vt 可分解为 vt = s0*v0 + s1*v1 + s2*v,
   由双线性性质，我们可以分别对v0,v1,v2作用。
   因此，q对向量vt的作用是绕v进行θ角的一次旋转。

   一般化定理5.1，可知每个3D旋转对应一个单位四元数。
   进一步，若q1,q2两次相继旋转可得到进一步的公式。
 *)

(** qrot对向量加法是线性的 *)
Lemma qrot_linear_vadd : forall (q : quat) (v1 v2 : vec 3),
    (qrotv q (v1 + v2) = qrotv q v1 + qrotv q v2)%V.
Proof. intros. veq; ra. Qed.

(** qrot对向量数乘是线性的 *)
Lemma qrot_linear_vscal : forall (q : quat) (v : vec 3) (k : R),
    (qrotv q (k s* v) = k s* (qrotv q v))%V.
Proof. intros. veq; ra. Qed.

(** qrot作用于某个四元数后不改变它的w分量。公式5.26 *)
Lemma qrot_keep_w : forall (q v : quat),
    qunit q -> (qrot q v).W = v.W.
Proof.
  intros. pose proof (qunit_imply_W q H). destruct q,v. cbv in *. ra.
  field_simplify. ra. rewrite H0. ra.
Qed.

(** qrot作用于某个纯四元数后所得四元数的w分量为0，即仍然是纯四元数 *)
Lemma qrot_im2q_w0 : forall (q : quat) (v : vec 3),
    qunit q -> (qrot q (im2q v)).W = 0.
Proof. intros. rewrite qrot_keep_w; auto. Qed.

(** 单位四元数的另一种表示形式：由旋转轴(单位向量)和旋转角构成 5.25 *)

(** qrot operation keep vector dot product *)
Lemma qrot_keep_dot : forall (q : quat) (v1 v2 : vec 3),
    qunit q -> < qrotv q v1, qrotv q v2> = <v1, v2>.
Proof.
  (* 1. 推理式的证明。先证明q的范数不变，又因为“v的范数 + w的平方和 = q的范数”，
     所以v的范数不变 *)
  (* 2. 计算式的证明 *)
  intros. pose proof (qunit_imply_W q H).
  v2e v1. v2e v2. destruct q; cbv in *.
  field_simplify. ra. rewrite H0. ra.
Qed.

(** qrot operation and vnorm operation are commutative *)
Lemma qrot_vnorm_comm : forall (q : quat) (v : vec 3),
    qunit q -> vnorm (qrotv q v) = qrotv q (vnorm v).
Proof.
  intros. unfold vnorm. unfold vlen, Vector.vlen.
  rewrite qrot_keep_dot; auto. rewrite qrot_linear_vscal. easy.
Qed.

(** qrot operation keep vector length *)
Lemma qrot_keep_vlen : forall (q : quat) (v : vec 3),
    qunit q -> (|| qrotv q v || = || v ||)%V.
Proof. intros. unfold vlen, Vector.vlen. f_equal. rewrite qrot_keep_dot; auto. Qed.

(** qrot operation keep vector angle *)
Lemma qrot_keep_vangle : forall (q : quat) (v1 v2 : vec 3),
    qunit q -> v1 /_ v2 = (qrotv q v1) /_ (qrotv q v2).
Proof.
  intros. unfold vangle. f_equal.
  rewrite !qrot_vnorm_comm; auto. rewrite qrot_keep_dot; auto.
Qed.

(** qrot operation keep unit vector *)
Lemma qrot_im2q_vunit : forall (q : quat) (v : vec 3),
    qunit q -> vunit v -> vunit (qrotv q v).
Proof.
  intros. apply vunit_spec. rewrite qrot_keep_vlen; auto.
  apply vunit_spec; auto.    
Qed.

(* 若旋转轴 v 是单位向量，则依转轴和转角生成的四元数是单位四元数 *)
(** qrot operation with unit vector yields unit quaternion *)
Lemma qrot_im2q_qunit : forall (q : quat) (v : vec 3),
    qunit q -> vunit v -> qunit (qrot q (im2q v)).
Proof.
  intros. apply qim_vunit_imply_qunit; auto.
  apply qrot_im2q_w0; auto. apply qrot_im2q_vunit; auto.
Qed.

(* 公式5.25中的四元数作用：绕n轴旋转θ角度。
       换言之，公式5.25是如何构造的？它为什么能表示旋转 *)

(* 计算两个向量的夹角 *)
(* Check vangle. *)
(* Check cv2angle. *)

(* 计算两个向量所决定的转轴（垂直于所在平面的法向量) *)
(* Check v3cross. *)

(* 由两个单位向量构造四元数 : (<u,v>, u \x v)
   几何意义，该四元数的w分量是u,v夹角的余弦，向量分量是由u,v确定的垂直轴 *)
Definition ab2q (u v : vec 3) : quat := si2q (<u,v>) (u \x v).

(* 由两个单位向量的乘法构造四元数 : (0,v) ⊗ (0,u)∗ 
       代数意义，两个四元数的乘积代表了一个四元数 *)
Definition ab2q' (u v : vec 3) : quat := (im2q v) * ((im2q u)\* ).

(** 两种方式定义出的四元数相等，(0,v) ⊗ (0,u)\*  = (<u,v>,u \x v) *)
Lemma ab2q_eq_ab2q' : forall u v : vec 3, ab2q u v = ab2q' u v.
Proof. intros. lqa. Qed.

(** 该四元数是单位四元数 vunit u -> vunit v -> qunit (ab2q u v) *)
Lemma ab2q_qunit : forall u v : vec 3,
    vunit u -> vunit v -> qunit (ab2q u v).
Proof.
  intros. rewrite ab2q_eq_ab2q'. unfold ab2q'. apply qmul_qunit.
  apply im2q_qunit; auto.
  rewrite qconj_qunit. apply im2q_qunit; auto.
Qed.

(** 任给两个单位向量v0,v1，并由它们的夹角和垂直轴确定出一个四元数q，若将v1由q
        旋转后得到v2，则(v1,v2)所确定的四元数也等于q q *)
Lemma ab2q_eq : forall (v0 v1 : vec 3),
    let q : quat := ab2q v0 v1 in
    let v2 : vec 3 := qrotv q v0 in
    vunit v0 -> vunit v1 -> ab2q v1 v2 = q.
Proof.
  intros.
  rewrite ab2q_eq_ab2q'. unfold ab2q'. unfold v2. unfold qrotv.
  rewrite im2q_q2im.
  2:{ rewrite qrot_im2q_w0; auto. apply ab2q_qunit; auto. }
  unfold qrot. unfold q at 2.
  rewrite ab2q_eq_ab2q'. unfold ab2q'.
  rewrite qconj_qmul, !qconj_qconj.
  rewrite <- qmul_assoc. rewrite (qmul_assoc q _ _). rewrite qsqr_im2q; auto.
  rewrite qmul_assoc. rewrite qconj_im2q. rewrite qsqr_im2q.
  rewrite qmul_assoc. rewrite qsqr_s2q. lqa.
  (* small things *)
  rewrite vopp_vunit; auto.
Qed.

(** qrot保持向量的单位性 *)
Lemma qrot_keep_vunit : forall (q : quat) (v : vec 3),
    qunit q -> vunit v -> qunit (qrot q (im2q v)).
Proof. intros. apply qrot_im2q_qunit; auto. Qed.

(** 论证旋转，需要构造一些中间变量，所以逻辑有点绕 *)
Section rotation_derivation.
  (* 任给(0,2π)内的旋转角θ, 旋转轴n，
       在以n为法线的平面上给出夹角为θ/2的两个3D单位向量v0,v1 *)
  Variables (θ : R) (n v0 v1 : vec 3).
  Hypotheses (Hbound_θ : 0 < θ < 2 * PI)
    (Hunit_v0: vunit v0) (Hunit_v1: vunit v1)
    (Hnorm_v01_n: vnorm (v0 \x v1) = n)
    (Hangle_v01_θ: vangle v0 v1 = θ/2).
  
  (* 并按照轴角方式构造一个四元数 *)
  Let q : quat := aa2quat (mkAA θ n).

  (** *** 一组关于 θ 的断言，暂时未使用 *)
  Section about_θ.
    (** 0 < sin (θ/2) *)
    Fact sin_θ2_gt0 : 0 < sin (θ/2).
    Proof. rewrite <- Hangle_v01_θ. apply sin_gt_0; ra. Qed.

    (* (** θ = 0 <-> v0 = v1 *) *)
    (* Fact θ_eq0_iff_v0_eq_v1 : θ = 0 <-> v0 = v1. *)
    (* Proof. rewrite cv3eq_iff_len_angle0. rewrite !vlen_vunit; auto. ra. Qed. *)

    (** θ = 0 <-> sin (θ/2) = 0 *)
    Fact θ_eq0_iff_sin_θ2_eq0 : θ = 0 <-> sin (θ/2) = 0.
    Proof.
      split; intros H.
      - apply sin_eq_O_2PI_1; ra.
      - apply sin_eq_O_2PI_0 in H; ra.
    Qed.
    
    (** θ ≠ 0 <-> sin (θ/2) ≠ 0*)
    Fact θ_neq0_iff_sin_θ2_neq0 : θ <> 0 <-> sin (θ/2) <> 0.
    Proof. rewrite θ_eq0_iff_sin_θ2_eq0. easy. Qed.
    
    (** θ = 0 <-> ||v0\xv1|| = 0 *)
    Fact θ_eq0_iff_v01_vcross_len0 : θ = 0 <-> (||v0 \x v1|| = 0)%V.
    Proof.
      rewrite vlen_v3cross_eq0_iff_angle_0_pi; auto; ra.
      all: apply vunit_neq0; auto.
    Qed.
    
    (** θ = 0 <-> v0 \x v1 = vzero *)
    Fact θ_eq0_iff_v01_vcross_eq0 : θ = 0 <-> v0 \x v1 = vzero.
    Proof.
      rewrite <- (vlen_eq0_iff_eq0 (v0 \x v1)).
      rewrite θ_eq0_iff_v01_vcross_len0. easy.
    Qed.
  End about_θ.

  (** *** 1. 基本的事实 *)

  (** v0 _|_ n *)
  Fact v0_orth_n : v0 _|_ n.
  Proof.
    rewrite <- Hnorm_v01_n. rewrite vorth_vnorm_r.
    - apply vorth_comm. apply v3cross_orth_l.
    - intro. apply θ_eq0_iff_v01_vcross_eq0 in H. ra.
  Qed.

  (** v1 _|_ n *)
  Fact v1_orth_n : v1 _|_ n.
  Proof.
    rewrite <- Hnorm_v01_n. apply vorth_vnorm_r.
    - intro. apply θ_eq0_iff_v01_vcross_eq0 in H. ra.
    - apply vorth_comm. apply v3cross_orth_r.
  Qed.

  (** n is unit *)
  Fact Hunit_n : vunit n.
  Proof.
    rewrite <- Hnorm_v01_n. apply vnorm_is_unit.
    intro. apply θ_eq0_iff_v01_vcross_eq0 in H. ra.
  Qed.

  (** (<v0,v1>, v0 \x v1) = q *)
  Fact v01_eq_q : ab2q v0 v1 = q.
  Proof.
    unfold q. unfold aa2quat. unfold ab2q. f_equal.
    - rewrite vdot_eq_cos_angle. rewrite <- Hangle_v01_θ.
      rewrite !vunit_imply_vlen_eq1; auto. ra.
    - rewrite v3cross_eq_vscal; ra.
      rewrite Hangle_v01_θ, Hnorm_v01_n.
      rewrite !vunit_imply_vlen_eq1; auto. ra.
      all: apply vunit_neq0; auto.
  Qed.

  (** q 是单位向量 *)
  Fact q_qunit : qunit q.
  Proof. rewrite <- v01_eq_q. apply ab2q_qunit; auto. Qed.

  
  (** *** 2. 证明 (v1,v2) 与 (v0,v1) 的几何关系 *)
  
  (* 用 q 来旋转 v0 得到 v2 *)
  Let v2 : vec 3 := qrotv q v0.

  (** v2 是单位向量，即长度不变 *)
  Fact v2_vunit : vunit v2.
  Proof. unfold v2. apply qrot_im2q_vunit; auto. apply q_qunit. Qed.

  (** 由 v1,v2 构造的四元数等于 q *)
  Fact v12_eq_q : ab2q v1 v2 = q.
  Proof.
    pose proof (ab2q_eq v0 v1 Hunit_v0 Hunit_v1) as H; simpl in H.
    rewrite v01_eq_q in H. auto.
  Qed.

  (** <v1,v2> = <v0,v1>，保持点积 *)
  Fact v12_v01_keep_vdot : <v1,v2> = <v0,v1>.
  Proof.
    pose proof (v12_eq_q). rewrite <- v01_eq_q in H. unfold ab2q in H.
    apply si2q_inj in H; destruct H; auto.
  Qed.
  
  (** v1 \x v2 = v0 \x v1, 表明(v1,v2)和(v0,v1)所确定的垂直轴相同 *)
  Fact v12_v01_keep_vcross : v1 \x v2 = v0 \x v1.
  Proof.
    pose proof (v12_eq_q). rewrite <- v01_eq_q in H. unfold ab2q in H.
    apply si2q_inj in H; destruct H; auto.
  Qed.

  (** v2 _|_ n *)
  Fact v2_orth_n : v2 _|_ n.
  Proof.
    copy Hnorm_v01_n.
    rewrite <- v12_v01_keep_vcross in HC. rewrite <- HC.
    apply vorth_vnorm_r.
    - intro. rewrite v12_v01_keep_vcross in H.
      apply θ_eq0_iff_v01_vcross_eq0 in H. ra.
    - apply vorth_comm. apply v3cross_orth_r.
  Qed.

  (** (v1,v2)和(v0,v1)的这两个夹角相同 *)
  Fact v12_v01_same_angle : v1 /_ v2 = v0 /_ v1.
  Proof.
    unfold vangle. f_equal.
    rewrite !vdot_vnorm. rewrite !vunit_imply_vlen_eq1; auto.
    rewrite v12_v01_keep_vdot. auto.
    all: try apply vunit_neq0; auto; try apply v2_vunit.
  Qed.

  (** 给定两个向量，若将这两个向量同时旋转θ角，则向量之和在旋转前后的夹角也是θ。*)
  Lemma vangle_vadd : forall {n} (a b c d : vec n),
      a <> vzero -> b <> vzero ->
      ||a||%V = ||c||%V -> ||b||%V = ||d||%V ->
      a /_ b = c /_ d ->
      ((a + b) /_ (c + d) = b /_ d)%V.
  Proof.
  Admitted.

  Lemma vangle_add : forall {n} (a b c : vec n), a /_ c = ((a /_ b) + (b /_ c))%R.
  Proof.
  (* 由于目前 vangle 只是夹角，没有区分起始和结束向量，所以该性质不成立。
   在2D和3D中有带方向的 vangle2, vangle3。并且在3D中，还需要共面条件。 *)
  Admitted.

  (** (v0,v2) 的夹角是 θ *)
  Fact v02_angle_θ : v0 /_ v2 = θ.
  Proof.
    rewrite (vangle_add v0 v1 v2); ra.
    rewrite v12_v01_same_angle. rewrite Hangle_v01_θ. lra.
  Qed.

  (* (** v0,v1,v2 共面 *) *)
  (* Fact v012_coplanar : cv3coplanar v0 v1 v2. *)
  (* Proof. *)
  (*   apply cv3cross_same_cv3coplanar. symmetry. apply v12_v01_keep_vcross. *)
  (* Qed. *)
  
  (** *** 3. 证明 (v2,v3) 与 (v1,v2) 的几何关系 *)    
  
  (* 用 q 来旋转 v1 得到 v3 *)
  Let v3 : vec 3 := qrotv q v1.
  
  (** v3 是单位向量，即长度不变 *)
  Fact v3_vunit : vunit v3.
  Proof. unfold v3. apply qrot_im2q_vunit; auto. apply q_qunit. Qed.

  (** 由 v2,v3 构造的四元数等于 q *)
  Fact v23_eq_q : ab2q v2 v3 = q.
  Proof.
    pose proof (ab2q_eq v1 v2 Hunit_v1 v2_vunit) as H; simpl in H.
    rewrite v12_eq_q in H. auto.
  Qed.

  (** <v2,v3> = <v1,v2>，保持点积 *)
  Fact v23_v12_keep_vdot : <v2,v3> = <v1,v2>.
  Proof.
    intros. pose proof (v23_eq_q). rewrite <- v12_eq_q in H.
    apply si2q_inj in H; destruct H; auto.
  Qed.
  
  (** v2 \x v3 = v1 \x v2, 表明(v2,v3)和(v1,v2)所确定的垂直轴相同 *)
  Fact v23_v12_keep_vcross : v2 \x v3 = v1 \x v2.
  Proof.
    pose proof (v23_eq_q). rewrite <- v12_eq_q in H. unfold ab2q in H.
    apply si2q_inj in H; destruct H; auto.
  Qed.

  (** v3 _|_ n *)
  Fact v3_orth_n : v3 _|_ n.
  Proof.
    assert (v0 \x v1 = v2 \x v3) as H.
    { rewrite v23_v12_keep_vcross, v12_v01_keep_vcross. easy. }
    copy Hnorm_v01_n.
    rewrite H in HC. rewrite <- HC. apply vorth_vnorm_r.
    - rewrite <- H. intro. apply θ_eq0_iff_v01_vcross_eq0 in H0. ra.
    - apply vorth_comm. apply v3cross_orth_r.
  Qed.

  (** (v2,v3)和(v1,v2)的这两个夹角相同 *)
  Fact v23_v12_same_angle : v2 /_ v3 = v1 /_ v2.
  Proof.
    unfold vangle. f_equal.
    rewrite !vdot_vnorm. rewrite !vunit_imply_vlen_eq1.
    rewrite v23_v12_keep_vdot. auto.
    all: try apply vunit_neq0; auto.
    all: try apply v2_vunit; try apply v3_vunit.
  Qed.
  
  (** (v1,v3) 的夹角是 θ *)
  Fact v13_angle_θ : v1 /_ v3 = θ.
  Proof.
    rewrite (vangle_add v1 v2 v3); ra.
    rewrite v23_v12_same_angle, v12_v01_same_angle; lra.
  Qed.

  (** v1,v2,v3 共面 *)
  Fact v123_coplanar : v3coplanar v1 v2 v3.
  Proof.
    apply v3cross_same_v3coplanar. symmetry. apply v23_v12_keep_vcross.
  Qed.

  (** *** 4. 证明 q 对 n 不起作用 *)

  (** q ⊗ [0,n] = [0,n] ⊗ q *)
  Fact qn_eq_nq : q * im2q n = im2q n * q.
  Proof. lqa. (* 这里可计算式的证明，但我暂不知如何推导这个命题。*) Qed.
  
  (** 使用 q 对 n 旋转，不改变 n。即，符合几何上的直观含义：n 是旋转轴。 *)
  Fact rot_n_eq_n : qrotv q n = n.
  Proof.
    unfold qrotv, qrot. rewrite qn_eq_nq. rewrite qmul_assoc.
    rewrite <- qinv_eq_qconj. rewrite qmul_qinv_r. rewrite qmul_1_r. apply q2im_im2q.
    apply qunit_neq0. apply q_qunit. apply q_qunit.
  Qed.
  
  (** *** 5. 证明 q 与任意向量 v 的几何关系 *)
  Section main_theorem_analysis.
    
    (* 由于v0,v1,n是线性无关的一组基，所以任意向量v都可以由它们线性表出。
         这里跳过了这部分理论的论证。即 v 的定义的合理性。
         假设用(v0,v1,n)和给定的一组系数(s0,s1,s2)表出了一个向量 *)
    Variable s0 s1 s2 : R.
    (* we assume that: 0 < s0, 0 < s1,
       instead assuming that: s0 <> 0, s1 <> 0 *)
    Hypotheses (Hs0_gt0 : 0 < s0) (Hs1_gt0 : 0 < s1).
    Let v : vec 3 := (s0 s* v0 + s1 s* v1 + s2 s* n)%V.
    (* 假设 v 被 qrot 作用后成为了 v' *)
    Let v' : vec 3 := qrotv q v.

    (** 我们证明如下结论：
          (1) v和v'的长度相等
          (2) v和v'在n的法平面上的投影的夹角是θ
          这说明了 qrot 将 v 绕 n 轴旋转了 θ 度，到达 v'。
          所以，单位四元数旋转公式
          [0 v'] = qrot (q, v) = q ⊗ [0 n] ⊗ q\* , 其中，q = (cos(θ/2), sin(θ/2)*n)
          表达式了我们想要的旋转。
     *)

    (** v和v'的长度相等 *)
    Fact vlen_vv' : (||v'|| = ||v||)%V.
    Proof.
      unfold v',v. rewrite qrot_keep_vlen; auto. apply q_qunit.
    Qed.

    (** v和v'在n的法平面上的投影的夹角是θ *)
    Fact vangle_vv' : vperp v n /_ vperp v' n = θ.
    Proof.
      pose proof (vunit_neq0 n Hunit_n).
      unfold v',v.
      rewrite !qrot_linear_vadd, !qrot_linear_vscal.
      fold v2. fold v3. rewrite rot_n_eq_n.
      (* elim (s2 s* n) *)
      rewrite !vperp_vadd, !vperp_vscal; auto.
      rewrite vperp_self; auto. rewrite vscal_0_r, !vadd_0_r.
      (* elim vperp *)
      rewrite !vorth_imply_vperp_eq_l.
      (* (s0 s* v0 + s1 s* v1)%V /_ (s0 s* v2 + s1 s* v3)%V = θ *)
      rewrite vangle_vadd.
      all: rewrite ?vangle_vscal_l_gt0, ?vangle_vscal_r_gt0; auto.
      (* solve goals such as: v1 <> vzero *)
      all: try (apply vunit_neq0; try apply v3_vunit; try apply v2_vunit; easy).
      all: try apply v3_orth_n; try apply v2_orth_n; try apply v1_orth_n.
      all: try apply v0_orth_n; try apply v13_angle_θ.
      (* solve goals such as: (s1 s* v3)%V <> vzero *)
      all: try apply vscal_neq0_neq0_neq0; unfold Azero; try lra.
      all: try (apply vunit_neq0; try apply v3_vunit; easy).
      (* solve goals such as: (||s0 s* v0||)%V = (||s0 s* v2||)%V *)
      all: rewrite ?vlen_vscal,?vunit_imply_vlen_eq1; auto.
      apply v2_vunit. apply v3_vunit.
      (* v0 /_ v1 = v2 /_ v3 *)
      rewrite v23_v12_same_angle. rewrite v12_v01_same_angle. auto.
    Qed.
  End main_theorem_analysis.

End rotation_derivation.

(** 四元数乘法能表示旋转（这一版，仍然使用 v0,v1 这两个中间变量，以后也许能去掉） *)
Theorem qrot_valid : forall (v0 v1 : vec 3) (s0 s1 s2 : R) (aa : AxisAngle),
    let (θ, n) := aa in
    let q : quat := aa2quat aa in
    let v : vec 3 := (s0 s* v0 + s1 s* v1 + s2 s* n)%V in
    let v' : vec 3 := qrotv q v in
    vunit v0 -> vunit v1 ->
    0 < θ < 2 * PI ->
    vnorm (v0 \x v1) = n ->
    vangle v0 v1 = θ/2 ->
    0 < s0 -> 0 < s1 ->
    (||v'|| = ||v||)%V /\ vperp v n /_ vperp v' n = θ.
Proof.
  intros. destruct aa as [θ n]. intros.
  split; [apply vlen_vv'|apply vangle_vv']; auto.
Qed.

(** 方法3：Dunn 中提到的 *)
Section qrot_spec_method3.
(* 我们想知道，最初是如何发现这个旋转操作的。
   在 8.7.3 将根据几何关系推导从四元数到矩阵形式的转换 *)
End qrot_spec_method3.


(** 备注：四元数乘法可以连接多个旋转，就像矩阵乘法一样。
    但实际上还有一些区别。矩阵乘法时，可以使用行矢量左乘矩阵，也可使用列矢量右乘
    矩阵（转置形式）。而四元数没有这种灵活性，多个连接总是从右到左或说“从里到外”
    读取。对于 Dunn 的这个观点，我们可以进一步实验，看看四元数是否也能通过某种
    “转置”操作实现更换方向。当然，这个实验可能只是理论上的需要，实际并无此需求。
    由于四元数乘法有对应的矩阵形式，我么可以直接在矩阵上操作 *)

(** Rotate twice: first by q1, then by q2 *)
Lemma qrot_twice : forall (q1 q2 : quat) (v : quat),
    qrot q2 (qrot q1 v) = qrot (q2 * q1) v.
Proof.
  intros. unfold qrot. rewrite qconj_qmul, !qmul_assoc; auto.
Qed.

(** vector form *)
Lemma qrot_twice_vec : forall (q1 q2 : quat) (v : vec 3),
    qunit q1 -> qrotv q2 (qrotv q1 v) = qrotv (q2 * q1) v.
Proof.
  intros. unfold qrotv.
  rewrite <- qrot_twice; try apply qunit_neq0; auto.
  unfold qrot. f_equal. f_equal. f_equal. rewrite im2q_q2im; auto.
  pose proof (qrot_im2q_w0 q1 v H). unfold qrot in H0. auto.
Qed.


(** ** 坐标系旋转的情况 *)
Section qrotAxis.

  (** 向量v(被包装为四元数)所在的坐标系旋转q，则新坐标系中v的向量如下。
      注意，q必须是旋转四元数 *)
  (* Definition qrotAxis (q : quat) (v : quat) : quat := q\-1 * v * q. *)
  Definition qrotAxis (q : quat) (v : quat) : quat := q \* * v * q.

  (* 由于旋转坐标系是旋转向量的逆过程，所以我们可以通过验证逆来说明此定义正确 *)
  Lemma qrotAxis_qrot : forall q v, qunit q -> qrot q (qrotAxis q v) = v.
  Proof.
    intros. unfold qrot, qrotAxis.
    rewrite <- !qmul_assoc. rewrite qunit_qmul_qconj_r; auto. rewrite qmul_1_l.
    rewrite !qmul_assoc. rewrite qunit_qmul_qconj_r; auto. rewrite qmul_1_r. auto.
  Qed.

  Lemma qrot_qrotAxis : forall q v, qunit q -> qrotAxis q (qrot q v) = v.
  Proof.
    intros. unfold qrot, qrotAxis.
    rewrite <- !qmul_assoc. rewrite qunit_qmul_qconj_l; auto. rewrite qmul_1_l.
    rewrite !qmul_assoc. rewrite qunit_qmul_qconj_l; auto. rewrite qmul_1_r. auto.
  Qed.
  
  (** 坐标系旋转q时，某向量在旧坐标系下的坐标 v 在新坐标系下为 *)
  Definition qrotvAxis (q : quat) (v : vec 3) : vec 3 := q2im (qrotAxis q (im2q v)).

  (* 验证 qrotvAxis 和 qrot 语义等价即可 *)
  Lemma qrotvAxis_eq_qrotv : forall q v, qrotvAxis q v = q2im (qrotAxis q (im2q v)).
  Proof. auto. Qed.

  (** 坐标系相继旋转q1和q2时，向量在就坐标系下的坐标v在新坐标系下为 *)
  Lemma qrotAxis_twice : forall q1 q2 v,
      qrotAxis q2 (qrotAxis q1 v) = qrotAxis (q1 * q2) v. 
  Proof.
    intros. unfold qrotAxis. rewrite qconj_qmul, !qmul_assoc; auto.
  Qed.
    
End qrotAxis.


(** ** 四元数与旋转矩阵 *)

Definition q2m (q : quat) : smat 3 :=
  let (w,x,y,z) := q in
  l2m [[w^2+x^2-y^2-z^2; 2*x*y-2*w*z; 2*x*z+2*w*y];
       [2*x*y+2*w*z; w^2-x^2+y^2-z^2; 2*y*z-2*w*x];
       [2*x*z-2*w*y; 2*y*z+2*w*x; w^2-x^2-y^2+z^2]]%R.

(**            [1 0]
    quint q -> [0 C] = qmatL (q\-1) * qmatR q, where C = q2m q *)
Lemma q2m_eq : forall q,
    let C := q2m q in
    qunit q ->
    mconsrH (vconsH 1 vzero) (mconscH vzero C) = (qmatL q * qmatR (q\-1))%M.
Proof.
  intros. rewrite qinv_eq_qconj; auto. destruct q. cbv in H.
  assert ((W0 * W0 + X0 * X0 + Y0 * Y0 + Z0 * Z0)%R = 1) by ra.
  meq. all: try lra.
Qed.

(** qrotv q v = (q2m q) * v *)
Lemma q2m_spec : forall (q : quat) (v : vec 3),
    qunit q -> qrotv q v = ((q2m q) *v v)%M.
Proof. intros. unfold qrotv,qrot. destruct q. v2e v. veq; ra. Qed.

Definition Rsign (r : R) : R := if r >=? 0 then 1 else (-1).

(** One rotation matrix corresponds to two quaternions, namely q, -q *)
Definition m2q (M : smat 3) : quat :=
  (let sign0 : R := 1 in
  let sign1 : R := sign0 * (Rsign (M.32 - M.23)) in
  let sign2 : R := sign0 * (Rsign (M.13 - M.31)) in
  let sign3 : R := sign0 * (Rsign (M.21 - M.12)) in
  let w : R := sign0 * (1/2) * sqrt (1 + M.11 + M.22 + M.33) in
  let x : R := sign1 * (1/2) * sqrt (1 + M.11 - M.22 - M.33) in
  let y : R := sign2 * (1/2) * sqrt (1 - M.11 + M.22 - M.33) in
  let z : R := sign3 * (1/2) * sqrt (1 - M.11 - M.22 + M.33) in
  mkQ w x y z)%R.

Lemma m2q_qunit : forall (M : smat 3), morth M -> qunit (m2q M).
Proof.
  intros.
  apply morth_iff_mrowsOrthonormal in H.
  hnf in H. destruct H as [H1 H2]. hnf in H1,H2.
  assert (@nat2finS 2 0 <> #1) as H01 by fin.
  assert (@nat2finS 2 0 <> #2) as H02 by fin.
  assert (@nat2finS 2 1 <> #2) as H12 by fin.
  pose proof (H1 #0 #1 H01).
  pose proof (H1 #0 #2 H02).
  pose proof (H1 #1 #2 H12).
  pose proof (H2 #0). pose proof (H2 #1). pose proof (H2 #2).
  clear H1 H2. v2eALL M. cbv in *. apply sqrt_eq1_if_eq1. field_simplify. ra.
  (* destruct Rle_Dec. *)
  (* repeat destruct dec. *)
  (* I cann't prove it now *)
Admitted.

(** 此处应该有两个值，该引理暂无法证明 *)
Lemma q2m_m2q_id : forall (M : smat 3), morth M -> q2m (m2q M) = M.
Proof.
  intros.
  v2eALL M. meq.
  (* - ra. destruct Rle_Dec. *)
Admitted.

Lemma m2q_spec : forall (M : smat 3) (v : vec 3),
    morth M -> (M *v v)%M = qrotv (m2q M) v.
Proof.
  intros. rewrite q2m_spec. f_equiv.
  - rewrite q2m_m2q_id; easy.
  - apply m2q_qunit; auto.
Qed.

(* 四元数与欧拉角
   1. 可借助旋转矩阵实现：四元数 <=> 旋转矩阵 <=> 欧拉角
   2. 也可直接推导
 *)

Section euler2quat.
  Variable euler : vec 3.
  Notation ϕ := (euler.1). Notation θ := (euler.2). Notation ψ := (euler.3).
  Notation ϕ2 := (ϕ/2). Notation θ2 := (θ/2). Notation ψ2 := (ψ/2).
  Notation cϕ2 := (cos ϕ2).  Notation sϕ2 := (sin ϕ2).
  Notation cθ2 := (cos θ2).  Notation sθ2 := (sin θ2).
  Notation cψ2 := (cos ψ2).  Notation sψ2 := (sin ψ2).

  (* ZYX欧拉角到四元数 *)
  Definition euler2quat : quat :=
    mkQ
      (cϕ2 * cθ2 * cψ2 + sϕ2 * sθ2 * sψ2)
      (sϕ2 * cθ2 * cψ2 - cϕ2 * sθ2 * sψ2)
      (cϕ2 * sθ2 * cψ2 + sϕ2 * cθ2 * sψ2)
      (cϕ2 * cθ2 * sψ2 - sϕ2 * sθ2 * cψ2).

  (* 分别绕三个坐标轴旋转所对应的四元数 *)
  Let qx := aa2quat (mkAA ϕ v3i).
  Let qy := aa2quat (mkAA θ v3j).
  Let qz := aa2quat (mkAA ψ v3k).

  (* ZYX欧拉角对应的四元数等于三次旋转的四元数乘积 *)
  Lemma euler2quat_eq : euler2quat = qz * qy * qx.
  Proof.
    intros.
    remember (euler #0). remember (euler #1). remember (euler #2).
    v2e euler. subst. cbv in qx,qy,qz. unfold qx,qy,qz.
    unfold euler2quat. subst. cbv. f_equal; ra.
  Qed.
  
  (* ZYX欧拉角对应的四元数的旋转效果等价于三次相继旋转 *)
  Lemma euler2quat_spec : forall v, qrot euler2quat v = qrot qz (qrot qy (qrot qx v)).
  Proof. intros. rewrite !qrot_twice. rewrite euler2quat_eq. auto. Qed.
End euler2quat.

Section quat2euler.
  Variable q : quat.
  Notation q0 := (q.W). Notation q1 := (q.X).
  Notation q2 := (q.Y). Notation q3 := (q.Z).

  (* 当 ϕ∈[-π,π], θ∈[-π/2,π/2], ψ∈[-π,π] 时，四元数q对应的欧拉角如下 *)
  Definition quat2euler : vec 3 :=
    let phi := atan ((2 * (q0 * q1 + q2 * q3)) / (1 - 2 * (q1² + q2²))) in
    let theta := asin (2 * (q0 * q2 - q1 * q3)) in
    let psi := atan ((2 * (q0 * q3 + q1 * q2)) / (1 - 2 * (q2² + q3²))) in
    l2v [phi; theta; psi].

  (* ToDo: spec *)

  (* ToDo: 当θ=±π/2时的情形 *)
  
End quat2euler.

(* Extract Constant Rabst => "__". *)
(* Extract Constant Rrepr => "__". *)
(* Extraction "quat.ml" mk_mat_3_1. (* Why so many warning? *) *)
(* Recursive Extraction mk_quat mk_quat quat_of_t4 qmul qconj qinv qlen rot_by_quat. *)
(* Extraction "quat.ml" mk_quat mk_quat quat_of_t4 qmul qconj qinv. qlen rot_by_quat. *)


(* Extract Constant Rabst => "__". *)
(* Extract Constant Rrepr => "__". *)
(* Extraction "quat.ml" mk_mat_3_1. (* Why so many warning? *) *)
(* Recursive Extraction mkQ mkQ quat_of_t4 qmul qconj qinv qlen rot_by_quat. *)
(* Extraction "quat.ml" mkQ mkQ quat_of_t4 qmul qconj qinv. qlen rot_by_quat. *)

