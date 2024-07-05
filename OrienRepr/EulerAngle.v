(*
  Copyright 2023 Zhengpu Shi
  This file is part of OrienRepr. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Euler angle in 3D
  author    : Zhengpu Shi
  date      : 2023.04.01
  
  reference :
  1. Peter Corke, Robotics Vision and Control. page34.
  2. https://en.wikipedia.org/wiki/Euler_angles
  3. https://krasjet.github.io/quaternion
  4. https://zhuanlan.zhihu.com/p/98320567
  5. Carlos M. Roithmayr and Deway H. Hodges, Dynamics: Theory and Application of 
     Kane's Method. page22, page484.
  6. James Diebel, Representing Attitude: Euler Angles, Unit Quaternions, and 
     Rotation Vectors.
  7. https://petercorke.com/robotics/roll-pitch-yaw-angles/

  remark    :

  1. Understanding "Euler angles"
  (1). 右手定则与左手定则(right- or left-handed rule)，可用于决定旋转角的符号
     右手和左手参考系( .. coordinates)，按照x->y->z的顺序，可用于决定第三个轴的方向。
  (2). 主动和被动旋转 (Alibi or alias, 也称 active or passive)，
     主动是旋转物体（刚体、表示刚体的向量），被动是旋转坐标系
  (3). 内部和外部旋转 (intrinsic or extrinsic rotation)，
     内部是绕物体自身的坐标系，旋转轴对于物体不变，但对于外部参考系在变化；
     外部是绕固定的参考坐标系，旋转轴对于外部参考系不变，但对于物体在变化。
  (4). 预乘和后乘 (pre- or post-multiplication)
     同一个点P，可以被表示为列向量v或行向量w。
     旋转矩阵能被预乘以列向量 Rv，或者后乘以行向量 wR。
     然而，Rv产生的旋转与wR的是反向的。
     为了得到相同的旋转（即，P点相同的最终坐标），等价的行向量必须后乘以R的转置（即，wR\T）
  (5). 经典欧拉角和Tait-Bryan角
     欧拉角通常表示为 α,β,γ 或 ψ,θ,ϕ。
     不同作者可能使用不同的旋转轴来定义欧拉角，或者为相同的角起不同的名字。
     因此，任何涉及欧拉角的讨论都应该先说它们的定义。
     不考虑旋转轴的两种不同惯例时，旋转轴顺序存在12种可能，分为两组：
     Proper Euler angles: (xyx,xzx,yxy,yzy,zxz,zyz)
     Tait-Bryan angles: (xyz,xzy,yxz,yzx,zxy,zyx)
     其中，Tait-Bryan角，也称 Cardan angles; nautical angles; heading,elevation, and 
     bank; or yaw, pitch, and roll.
     有时这两种顺序都称“Euler angles”。
     此时，第一种顺序也称为 proper or classic 欧拉角。
  (6). 欧拉角的定义有24种
     (内部 or 外部) * (Proper or Tait-Bryan) = 2 * (6 + 6) = 24 

  2. Rotation matrices.
  (1) There are two explanations for coordinate transformation:
   i. The vector is static, and the coordinate system is changing from one to another.
    reference: {Dibel - Representing}
    We define the rotation matrix that encodes the attitude of a rigid body to be 
    the matrix that when pre-multiplied by a vector expressed in the body-fixed 
    coordinates yields the same vector expressed in the word coordinates.
    That is, if v\in R^3 is a vector in the body-fixed coordinates and v'\in R^3 is 
    the same vector expressed in the word coordinates, then the following relations 
    hold:
            v' = R * v
            v = R\T * v'
    These expression apply to {vectors}, relative quantities lacking a position in 
    space. To transform a {point} from one coordinate system to other we must 
    subtract the offset to the origin of the target coordinate system before 
    applying the rotation matrix.
  ii. There is only one coordinate system, the vector is chaning.
    Orthogormal rotation matrices for rotation of θ aobout the x-,y- and z- axes.
    Notes:
    (1). Give a column-vector v1 respect to this coordinate, when actively rotate it 
        about the x-axes, we could get a new vector v1' respect to this coordinate by
        this formula:
             v1' = Rx(θ) v1
     (2). If give a row-vector v2, ..., v2' ...
             v2' = v2 (Rx(θ))\T

  向量的旋转变换矩阵 vs 坐标系的旋转变换矩阵
  向量的旋转变换，写作 v' = R v，表示：坐标系不动，向量 v 旋转到了 v'
  坐标系的旋转变换，写作 v' = R\T v，表示：坐标系旋转，得到的是不动的点 v 在新坐标系
  下的表示。
  注意以下对应关系：
     (1) v' = R v 表示v经过R旋转到达v'，对应的， R' v' = v 表示v'经过R'旋转到达v。 
     (2) R\T 就是 R^(-1)，也写作 R'，它表示一个逆的旋转
     (3) 旋转矩阵R表示向量旋转一个正角度(逆时针)，R\T则表示向量旋转一个负角度（顺时针）。
     (4) 向量旋转正角度，相当于坐标系旋转负角度
     (5) v' = (RxRyRz) v 表示对向量 v 按z,y,x轴的顺序进行旋转得到 v'，
         而需要由 v' 计算 v 时，令 v' W = v，则 W = (RxRyRz)' = Rz'Ry'Rx'
  (2). 任意朝向都能分解为从已知的标准朝向开始的三个基本旋转。
     等价的，任意旋转矩阵R能被分解为三个基本旋转矩阵的乘积。
     例如 R = X(α)Y(β)Z(γ) 是一个旋转矩阵，可表示关于 z,y,x轴的外部旋转的复合，
     或是关于 x,y',z''轴的内部旋转的复合。

  3. Linearization:
  (1). 小角度变化经常被用来近似描述系统的动态特性，此时系统的响应可通过线性模型来预测和控制。
  (2). 角度变化很小(通常认为10度以内)时，可线性化处理，
     sin(α)->α, cos(α)->1, 高阶项sin(α)*sin(β)->0

  4. 再次理解欧拉角和Roll-Pitch-Yaw角
     参考：https://petercorke.com/robotics/roll-pitch-yaw-angles/
     Euler angles vs roll-pitch-yaw angels
     * 这里没有明确的对错，作者使用不精确的语言，并将特定领域的惯例视为严格的定义。
     * 让我们回到基础知识。欧拉旋转定理（自 1775 年）指出，
       一个 3D 坐标系相对于另一个 3D 坐标系的方向可以通过“绕三个轴连续旋转，使得
       没有两个连续旋转绕同一轴”来描述。  然而，围绕三个轴的旋转有十二种不同的排列
       满足欧拉的标准：XYX、XYZ、XZX、XZY、YXY、YXZ、YZX、YZY、ZXY、ZXZ、ZYX、ZYZ。
     * 我们可以将这十二种排列分为两组，每组六种：
       Eulerian (在Euler之后) 涉及到旋转轴的不连续的重复：XYX、XZX、YXY、YZY、ZXZ 或 ZYZ。
       Cardanian（在Cardano之后，也称 Tait-Bryan 角）涉及绕所有三个轴的旋转：XYZ、XZY、YZX、YXZ、ZXY 或 ZYX。
     * 在一些参考文献中，所有十二个序列都被称为欧拉角，但在这里我们将仅将上面的欧拉序列视为欧拉角。
       有六种不同的序列可供选择，特定的角度序列是特定技术领域内的惯例。 
       在航空航天中，欧拉角的约定是 ZYZ，其中相应的旋转矩阵是 R(ϕ,θ,ψ)=Rz(ϕ)Ry(θ)Rz(ψ)
     * The Cardanian angles也称为roll,pitch and yaw angles (滚动角、俯仰角和偏航角)。
       令人困惑的是，常用的有两个不同的版本：序列 XYZ 和 ZYX。教科书在这个问题上根本不一致。
       如果存在任何不一致的模式，那就是移动机器人社区（无人机、地面车辆）使用 ZYX，而机器人操纵器社区使用 XYZ。
     * 为什么会这样？ 当描述船舶、飞机和汽车等交通工具的姿态时，惯例是 x 轴指向前方，z 轴
       指向上方或下方。这意味着根据叉积规则，y 轴必须指向侧面。
       想象一下试图描述一架飞机的姿态。  
       我们的参考姿态是飞机位于水平面上，机头指向世界坐标系x轴方向。  
       我们要做的第一件事是将机头指向正确的罗盘航向，即在 xy 平面内并绕世界 z 轴旋转。
       接下来我们将描述俯仰角，即正面相对于水平面的高度，它是绕新 y 轴的旋转。
       最后，我们描述滚转，即绕车辆前轴的旋转，即绕新的 x 轴的旋转。  
       这导致 ZYX 角度序列，其中旋转矩阵由下式给出 R(r,p,y)=Rz(y)Ry(p)Rx(r)
     * 当描述机器人夹具的姿态时，如图2.16所示，约定是z轴指向前方，x轴指向上方或下方。
       这导致 XYZ 角度序列 R(r,p,y)=Rx(y)Ry(p)Rz(r)
 *)

Require Export MathBase.
Require Export AxisAngle.
Require Export RotationMatrix3D.

(* ########################################################################### *)
(** * Euler angles under 24 definitions *)
Section EulerAngle24.

  Variable θ1 θ2 θ3 : R.
  Notation c1 := (cos θ1). Notation s1 := (sin θ1).
  Notation c2 := (cos θ2). Notation s2 := (sin θ2).
  Notation c3 := (cos θ3). Notation s3 := (sin θ3).

  (** 关于0点的线性化 *)
  Section LinearizationCondition_at_Zero.
    Definition LinearizationCondition : Prop :=
      (s1 = θ1 /\ s2 = θ2 /\ s3 = θ3 /\
        c1 = 1 /\ c2 = 1 /\ c3 = 1 /\
         s1 * s2 = 0 /\ s1 * s3 = 0 /\ s2 * s3 = 0 /\
         s2 * s1 = 0 /\ s3 * s1 = 0 /\ s3 * s2 = 0)%R.
  End LinearizationCondition_at_Zero.

  (** 1. Body-three, 123 *)
  Definition B123 : mat 3 3 :=
    l2m
      [[c2 * c3; -c2 * s3; s2];
       [s1 * s2 * c3 + s3 * c1; - s1 * s2 * s3 + c3 * c1; - s1 * c2];
       [-c1 * s2 * c3 + s3 * s1; c1 * s2 * s3 + c3 * s1; c1 * c2]]%R.

  Theorem B123_spec : B123 = Rx θ1 * Ry θ2 * Rz θ3.
  Proof. meq; ring. Qed.

  (** B123 is a member of SO3 *)
  Lemma B123_SOnP : SOnP B123.
  Proof.
    rewrite B123_spec. apply SOnP_mmul. apply SOnP_mmul.
    apply Rx_SOnP. apply Ry_SOnP. apply Rz_SOnP.
  Qed.

  (* verify morth keep cross *)
  Section verify_orth_keep_cross.

    (* Tips:
       1. 在B123的特定情况下的旋转矩阵，前两列的叉乘等于第三列。
       2. Matlab无法完成这样的证明。
       3. ra 有一定的自动化能力。
       4. 但最好是能够直接证明旋转矩阵有这个性质。*)
    Fact orth_keep_cross_c1c2 : B123&1 \x B123&2 = B123&3.
    Proof.
      apply SO3_v3cross_r12.
      rewrite mcol_eq_mtrans.
      apply SOnP_mtrans. apply B123_SOnP.
    Qed.
      
  End verify_orth_keep_cross.

  (* Linearation *)
  
  (* 这里只证明这一个例子，其余例子可以仿照此处做法 *)
  Definition B123_Linear : mat 3 3 :=
    l2m
      [[1; -θ3; θ2];
       [θ3; 1; -θ1];
       [-θ2; θ1; 1]]%R.

  Theorem B123_Linear_spec : LinearizationCondition -> B123 = B123_Linear.
  Proof.
    intros.
    destruct H as
      [Hs1 [Hs2 [Hs3 [Hc1 [Hc2 [Hc3 [H12 [H13 [H23 [H21 [H31 H32]]]]]]]]]]].
    unfold B123, B123_Linear.
    rewrite ?Hc1,?Hc2,?Hc3. meq; ring_simplify; auto; try lra.
    rewrite associative. rewrite H23. lra.
  Qed.
  

  (** 2. Body-three, 231 *)
  Definition B231 : mat 3 3 :=
    l2m
      [[c1 * c2; - c1 * s2 * c3 + s3 * s1; c1 * s2 * s3 + c3 * s1];
       [s2; c2 * c3; - c2 * s3];
       [- s1 * c2; s1 * s2 * c3 + s3 * c1; - s1 * s2 * s3 + c3 * c1]]%R.

  Theorem B231_spec : B231 = Ry θ1 * Rz θ2 * Rx θ3.
  Proof. meq; ring. Qed.

  (** 3. Body-three, 312 *)
  Definition B312 : mat 3 3 :=
    l2m
      [[- s1 * s2 * s3 + c3 * c1; - s1 * c2; s1 * s2 * c3 + s3 * c1];
       [c1 * s2 * s3 + c3 * s1; c1 * c2; - c1 * s2 * c3 + s3 * s1];
       [- c2 * s3; s2; c2 * c3]]%R.

  Theorem B312_spec : B312 = Rz θ1 * Rx θ2 * Ry θ3.
  Proof. meq; ring. Qed.

  (** 4. Body-three, 132 *)
  Definition B132 : mat 3 3 :=
    l2m
      [[c2 * c3; - s2; c2 * s3];
       [c1 * s2 * c3 + s3 * s1; c1 * c2; c1 * s2 * s3 - c3 * s1];
       [s1 * s2 * c3 - s3 * c1; s1 * c2; s1 * s2 * s3 + c3 * c1]]%R.

  Theorem B132_spec : B132 = Rx θ1 * Rz θ2 * Ry θ3.
  Proof. meq; ring. Qed.

  (** 5. Body-three, 213 *)
  Definition B213 : mat 3 3 :=
    l2m
      [[s1 * s2 * s3 + c3 * c1; s1 * s2 * c3 - s3 * c1; s1 * c2];
       [c2 * s3; c2 * c3; - s2];
       [c1 * s2 * s3 - c3 * s1; c1 * s2 * c3 + s3 * s1; c1 * c2]]%R.
        
  Theorem B213_spec : B213 = Ry θ1 * Rx θ2 * Rz θ3.
  Proof. meq; ring. Qed.

  (** 6. Body-three, 321 *)
  Definition B321 : mat 3 3 :=
    l2m
      [[c1 * c2; c1 * s2 * s3 - c3 * s1; c1 * s2 * c3 + s3 * s1];
       [s1 * c2; s1 * s2 * s3 + c3 * c1; s1 * s2 * c3 - s3 * c1];
       [- s2; c2 * s3; c2 * c3]]%R.
  
  Theorem B321_spec : B321 = Rz θ1 * Ry θ2 * Rx θ3.
  Proof. meq; ring. Qed.

  (** 7. Body-two, 121 *)
  Definition B121 : mat 3 3 :=
    l2m
      [[c2; s2 * s3; s2 * c3];
       [s1 * s2; - s1 * c2 * s3 + c3 * c1; - s1 * c2 * c3 - s3 * c1];
       [- c1 * s2; c1 * c2 * s3 + c3 * s1; c1 * c2 * c3 - s3 * s1]]%R.

  Theorem B121_spec : B121 = Rx θ1 * Ry θ2 * Rx θ3.
  Proof. meq; ring. Qed.
  
  (** 8. Body-two, 131 *)
  Definition B131 : mat 3 3 :=
    l2m
      [[c2; - s2 * c3; s2 * s3];
       [c1 * s2; c1 * c2 * c3 - s3 * s1; - c1 * c2 * s3 - c3 * s1];
       [s1 * s2; s1 * c2 * c3 + s3 * c1; - s1 * c2 * s3 + c3 * c1]]%R.
  
  Theorem B131_spec : B131 = Rx θ1 * Rz θ2 * Rx θ3.
  Proof. meq; ring. Qed.
  
  (** 9. Body-two, 212 *)
  Definition B212 : mat 3 3 :=
    l2m
      [[- s1 * c2 * s3 + c3 * c1; s1 * s2; s1 * c2 * c3 + s3 * c1];
       [s2 * s3; c2; - s2 * c3];
       [- c1 * c2 * s3 - c3 * s1; c1 * s2; c1 * c2 * c3 - s3 * s1]]%R.

  Theorem B212_spec : B212 = Ry θ1 * Rx θ2 * Ry θ3.
  Proof. meq; ring. Qed.
  
  (** 10. Body-two, 232 *)
  Definition B232 : mat 3 3 :=
    l2m
      [[c1 * c2 * c3 - s3 * s1; - c1 * s2; c1 * c2 * s3 + c3 * s1];
       [s2 * c3; c2; s2 * s3];
       [- s1 * c2 * c3 - s3 * c1; s1 * s2; - s1 * c2 * s3 + c3 * c1]]%R.
  
  Theorem B232_spec : B232 = Ry θ1 * Rz θ2 * Ry θ3.
  Proof. meq; ring. Qed.
  
  (** 11. Body-two, 313 *)
  Definition B313 : mat 3 3 :=
    l2m
      [[- s1 * c2 * s3 + c3 * c1; - s1 * c2 * c3 - s3 * c1; s1 * s2];
       [c1 * c2 * s3 + c3 * s1; c1 * c2 * c3 - s3 * s1; - c1 * s2];
       [s2 * s3; s2 * c3; c2]]%R.
  
  Theorem B313_spec : B313 = Rz θ1 * Rx θ2 * Rz θ3.
  Proof. meq; ring. Qed.
  
  (** 12. Body-two, 323 *)
  Definition B323 : mat 3 3 :=
    l2m
      [[c1 * c2 * c3 - s3 * s1; - c1 * c2 * s3 - c3 * s1; c1 * s2];
       [s1 * c2 * c3 + s3 * c1; - s1 * c2 * s3 + c3 * c1; s1 * s2];
       [- s2 * c3; s2 * s3; c2]]%R.
  
  Theorem B323_spec : B323 = Rz θ1 * Ry θ2 * Rz θ3.
  Proof. meq; ring. Qed.

  (** 13. Space-three, 123 *)
  Definition S123 : mat 3 3 :=
    l2m
      [[c2 * c3; s1 * s2 * c3 - s3 * c1; c1 * s2 * c3 + s3 * s1];
       [c2 * s3; s1 * s2 * s3 + c3 * c1; c1 * s2 * s3 - c3 * s1];
       [- s2; s1 * c2; c1 * c2]]%R.
                                                               
  Theorem S123_spec : S123 = Rz θ3 * Ry θ2 * Rx θ1.
  Proof. meq; ring. Qed.

  (** 14. Space-three, 231 *)
  Definition S231 : mat 3 3 :=
    l2m
      [[c1 * c2; - s2; s1 * c2];
       [c1 * s2 * c3 + s3 * s1; c2 * c3; s1 * s2 * c3 - s3 * c1];
       [c1 * s2 * s3 - c3 * s1; c2 * s3; s1 * s2 * s3 + c3 * c1]]%R.
  
  Theorem S231_spec : S231 = Rx θ3 * Rz θ2 * Ry θ1.
  Proof. meq; ring. Qed.

  (** 15. Space-three, 312 *)
  Definition S312 : mat 3 3 :=
    l2m
      [[s1 * s2 * s3 + c3 * c1; c1 * s2 * s3 - c3 * s1; c2 * s3];
       [s1 * c2; c1 * c2; - s2];
       [s1 * s2 * c3 - s3 * c1; c1 * s2 * c3 + s3 * s1; c2 * c3]]%R.
  
  Theorem S312_spec : S312 = Ry θ3 * Rx θ2 * Rz θ1.
  Proof. meq; ring. Qed.

  (** 16. Space-three, 132 *)
  Definition S132 : mat 3 3 :=
    l2m
      [[c2 * c3; - c1 * s2 * c3 + s3 * s1; s1 * s2 * c3 + s3 * c1];
       [s2; c1 * c2; - s1 * c2];
       [- c2 * s3; c1 * s2 * s3 + c3 * s1; - s1 * s2 * s3 + c3 * c1]]%R.
  
  Theorem S132_spec : S132 = Ry θ3 * Rz θ2 * Rx θ1.
  Proof. meq; ring. Qed.

  (** 17. Space-three, 213 *)
  Definition S213 : mat 3 3 :=
    l2m
      [[- s1 * s2 * s3 + c3 * c1; - c2 * s3; c1 * s2 * s3 + c3 * s1];
       [s1 * s2 * c3 + s3 * c1; c2 * c3; - c1 * s2 * c3 + s3 * s1];
       [- s1 * c2; s2; c1 * c2]]%R.
  
  Theorem S213_spec : S213 = Rz θ3 * Rx θ2 * Ry θ1.
  Proof. meq; ring. Qed.

  (** 18. Space-three, 321 *)
  Definition S321 : mat 3 3 :=
    l2m
      [[c1 * c2; - s1 * c2; s2];
       [c1 * s2 * s3 + c3 * s1; - s1 * s2 * s3 + c3 * c1; - c2 * s3];
       [- c1 * s2 * c3 + s3 * s1; s1 * s2 * c3 + s3 * c1; c2 * c3]]%R.
        
  Theorem S321_spec : S321 = Rx θ3 * Ry θ2 * Rz θ1.
  Proof. meq; ring. Qed.

  (** 19. Space-two, 121 *)
  Definition S121 : mat 3 3 :=
    l2m
      [[c2; s1 * s2; c1 * s2];
       [s2 * s3; - s1 * c2 * s3 + c3 * c1; - c1 * c2 * s3 - c3 * s1];
       [- s2 * c3; s1 * c2 * c3 + s3 * c1; c1 * c2 * c3 - s3 * s1]]%R.

  Theorem S121_spec : S121 = Rx θ3 * Ry θ2 * Rx θ1.
  Proof. meq; ring. Qed.

  (** 20. Space-two, 131 *)
  Definition S131 : mat 3 3 :=
    l2m
      [[c2; - c1 * s2; s1 * s2];
       [s2 * c3; c1 * c2 * c3 - s3 * s1; - s1 * c2 * c3 - s3 * c1];
       [s2 * s3; c1 * c2 * s3 + c3 * s1; - s1 * c2 * s3 + c3 * c1]]%R.
          
  Theorem S131_spec : S131 = Rx θ3 * Rz θ2 * Rx θ1.
  Proof. meq; ring. Qed.

  (** 21. Space-two, 212 *)
  Definition S212 : mat 3 3 :=
    l2m
      [[- s1 * c2 * s3 + c3 * c1; s2 * s3; c1 * c2 * s3 + c3 * s1];
       [s1 * s2; c2; - c1 * s2];
       [-s1 * c2 * c3 - s3 * c1; s2 * c3; c1 * c2 * c3 - s3 * s1]]%R.
  
  Theorem S212_spec : S212 = Ry θ3 * Rx θ2 * Ry θ1.
  Proof. meq; ring. Qed.

  (** 22. Space-two, 232 *)
  Definition S232 : mat 3 3 :=
    l2m
      [[c1 * c2 * c3 - s3 * s1; - s2 * c3; s1 * c2 * c3 + s3 * c1];
       [c1 * s2; c2; s1 * s2];
       [- c1 * c2 * s3 - c3 * s1; s2 * s3; - s1 * c2 * s3 + c3 * c1]]%R.
  
  Theorem S232_spec : S232 = Ry θ3 * Rz θ2 * Ry θ1.
  Proof. meq; ring. Qed.

  (** 23. Space-two, 313 *)
  Definition S313 : mat 3 3 :=
    l2m
      [[- s1 * c2 * s3 + c3 * c1; - c1 * c2 * s3 - c3 * s1; s2 * s3];
       [s1 * c2 * c3 + s3 * c1; c1 * c2 * c3 - s3 * s1; - s2 * c3];
       [s1 * s2; c1 * s2; c2]]%R.
  
  Theorem S313_spec : S313 = Rz θ3 * Rx θ2 * Rz θ1.
  Proof. meq; ring. Qed.

  (** 24. Space-two, 323 *)
  Definition S323 : mat 3 3 :=
    l2m
      [[c1 * c2 * c3 - s3 * s1; - s1 * c2 * c3 - s3 * c1; s2 * c3];
       [c1 * c2 * s3 + c3 * s1; - s1 * c2 * s3 + c3 * c1; s2 * s3];
       [-c1 * s2; s1 * s2; c2]]%R.
  
  Theorem S323_spec : S323 = Rz θ3 * Ry θ2 * Rz θ1.
  Proof. meq; ring. Qed.

End EulerAngle24.

(** Because the relativity, the 24 ways are actually only 12 ways.
    B123 = S321, B132 = S231, B213 = S312, B231 = S132, B312 = S213, B321 = S123,
    B121 = S121, B131 = S131, B212 = S212, B232 = S232, B313 = S313, B323 = S323 *)
Section EulerAngle24_only_half.
  Variable a1 a2 a3 : R.

  Lemma B123_eq_S321 : B123 a1 a2 a3 = S321 a3 a2 a1.
  Proof. meq; ring. Qed.
  
  Lemma B132_eq_S231 : B132 a1 a3 a2 = S231 a2 a3 a1.
  Proof. meq; ring. Qed.
  
  Lemma B213_eq_S312 : B213 a2 a1 a3 = S312 a3 a1 a2.
  Proof. meq; ring. Qed.
  
  Lemma B231_eq_S132 : B231 a2 a3 a1 = S132 a1 a3 a2.
  Proof. meq; ring. Qed.

  Lemma B312_eq_S213 : B312 a3 a1 a2 = S213 a2 a1 a3.
  Proof. meq; ring. Qed.

  Lemma B321_eq_S123 : B321 a3 a2 a1 = S123 a1 a2 a3.
  Proof. meq; ring. Qed.

  Lemma B121_eq_S121 : B121 a1 a2 a1 = S121 a1 a2 a1.
  Proof. meq; ring. Qed.

  Lemma B131_eq_S131 : B131 a1 a3 a1 = S131 a1 a3 a1.
  Proof. meq; ring. Qed.

  Lemma B212_eq_S212 : B212 a2 a1 a2 = S212 a2 a1 a2.
  Proof. meq; ring. Qed.

  Lemma B232_eq_S232 : B232 a2 a3 a2 = S232 a2 a3 a2.
  Proof. meq; ring. Qed.

  Lemma B313_eq_S313 : B313 a3 a1 a3 = S313 a3 a1 a3.
  Proof. meq; ring. Qed.

  Lemma B323_eq_S323 : B323 a3 a2 a3 = S323 a3 a2 a3.
  Proof. meq; ring. Qed.
End EulerAngle24_only_half.

(** Convert Rotation Matrix to Euler angles by S123 *)
Module R2Euler_S123.

  Open Scope R.
  
  (** 奇异性问题的存在性 *)
  Section singularity.

    (** Claim: If θ = kπ+π/2, then we can not uniquely determine ϕ and ψ. *)

    (* Let's prove some simpler goals first. *)
    
    (** If θ = π/2, then the rotation matrix has following form. *)
    Lemma S123_θ_eq_pi2 : forall (ϕ θ ψ : R),
        θ = PI/2 ->
        S123 ϕ θ ψ =
          l2m [[0; - sin (ψ - ϕ); cos (ψ - ϕ)];
               [0; cos (ψ - ϕ); sin (ψ - ϕ)];
               [-1; 0; 0]].
    Proof.
      intros; rewrite H. pose proof cos_PI2. pose proof sin_PI2. cbv in H0, H1.
      meq. all: try ra.
    Qed.

    (** If θ = -π/2, then the rotation matrix has following form. *)
    Lemma S123_θ_eq_pi2_neg : forall (ϕ θ ψ : R),
        θ = -PI/2 ->
        S123 ϕ θ ψ =
          l2m [[0; - sin (ψ + ϕ); - cos (ψ + ϕ)];
               [0; cos (ψ + ϕ); - sin (ψ + ϕ)];
               [1; 0; 0]].
    Proof.
      intros; rewrite H. pose proof cos_PI2. pose proof sin_PI2. cbv in H0, H1.
      meq. all: try ra.
    Qed.

    (** If θ = π/2, then there are infinite ϕ can generate a same matrix. *)
    Lemma S123_singularity_ϕ_when_θ_eq_pi2 : forall (ϕ θ ψ : R),
        θ = PI/2 -> forall ϕ', (exists ψ', S123 ϕ' θ ψ' = S123 ϕ θ ψ).
    Proof.
      intros. eexists. rewrite !S123_θ_eq_pi2; auto.
      instantiate (1:=ψ - ϕ + ϕ'). repeat (f_equal; try lra).
    Qed.
    
    (** If θ = -π/2, then there are infinite ϕ can generate a same matrix. *)
    Lemma S123_singularity_ϕ_when_θ_eq_pi2_neg : forall (ϕ θ ψ : R),
        θ = -PI/2 -> forall ϕ', (exists ψ', S123 ϕ' θ ψ' = S123 ϕ θ ψ).
    Proof.
      intros. eexists. rewrite !S123_θ_eq_pi2_neg; auto.
      instantiate (1:=ψ + ϕ - ϕ'). repeat (f_equal; try lra).
    Qed.

    (** If θ = ±π/2, then there are infinite ϕ can generate a same matrix. *)
    Theorem S123_singularity_ϕ : forall (ϕ θ ψ : R),
        (θ = PI/2 \/ θ = -PI/2) -> forall ϕ', (exists ψ', S123 ϕ' θ ψ' = S123 ϕ θ ψ).
    Proof.
      intros. destruct H.
      apply S123_singularity_ϕ_when_θ_eq_pi2; auto.
      apply S123_singularity_ϕ_when_θ_eq_pi2_neg; auto.
    Qed.

    (** If θ = π/2, then there are infinite ψ can generate a same matrix. *)
    Lemma S123_singularity_ψ_when_θ_eq_pi2 : forall (ϕ θ ψ : R),
        θ = PI/2 -> forall ψ', (exists ϕ', S123 ϕ' θ ψ' = S123 ϕ θ ψ).
    Proof.
      intros. eexists. rewrite !S123_θ_eq_pi2; auto.
      instantiate (1:=ψ' - ψ + ϕ). repeat (f_equal; try lra).
    Qed.
    
    (** If θ = -π/2, then there are infinite ψ can generate a same matrix. *)
    Lemma S123_singularity_ψ_when_θ_eq_pi2_neg : forall (ϕ θ ψ : R),
        θ = -PI/2 -> forall ψ', (exists ϕ', S123 ϕ' θ ψ' = S123 ϕ θ ψ).
    Proof.
      intros. eexists. rewrite !S123_θ_eq_pi2_neg; auto.
      instantiate (1:=ψ + ϕ - ψ'). repeat (f_equal; try lra).
    Qed.

    (** If θ = ±π/2, then there are infinite ψ can generate a same matrix. *)
    Theorem S123_singularity_ψ : forall (ϕ θ ψ : R),
        (θ = PI/2 \/ θ = -PI/2) -> forall ψ', (exists ϕ', S123 ϕ' θ ψ' = S123 ϕ θ ψ).
    Proof.
      intros. destruct H.
      apply S123_singularity_ψ_when_θ_eq_pi2; auto.
      apply S123_singularity_ψ_when_θ_eq_pi2_neg; auto.
    Qed.
  End singularity.

  (* 算法1：避开奇异点，小机动范围，即 roll,pitch,yaw ∈ (-π/2,π/2) *)
  Module alg1.
    Definition ϕ' (C : smat 3) := atan (C.32 / C.33).
    Definition θ' (C : smat 3) := asin (-C.31).
    Definition ψ' (C : smat 3) := atan (C.21 / C.11).
    
    Theorem alg_spec : forall (ϕ θ ψ : R) (C : smat 3),
        -PI/2 < ϕ < PI/2 ->
        -PI/2 < θ < PI/2 ->
        -PI/2 < ψ < PI/2 ->
        C = S123 ϕ θ ψ ->
        ϕ' C = ϕ /\ θ' C = θ /\ ψ' C = ψ.
    Proof.
      intros. v2eALL C.
      apply Vector.v3eq_iff in H2. destruct H2,H3.
      apply Vector.v3eq_iff in H2,H3,H4. cbv in H2,H3,H4.
      cbv. logic.
      - rewrite H5,H6. ra. rewrite atan_tan; auto.
      - rewrite H4. ra. rewrite asin_sin; ra.
      - rewrite H3,H2. ra. rewrite atan_tan; ra.
    Qed.
  End alg1.

  (* 算法2：避开奇异点，大机动范围，即 pitch ∈ (-π/2,π/2), roll,yaw ∈ (-π,π) *)
  Module alg2.
    Definition ϕ' (C : smat 3) := atan2 (C.32) (C.33).
    Definition θ' (C : smat 3) := asin (- C.31).
    Definition ψ' (C : smat 3) := atan2 (C.21) (C.11).

    Theorem alg_spec : forall (ϕ θ ψ : R) (C : smat 3),
        -PI < ϕ < PI ->
        -PI/2 < θ < PI/2 ->
        -PI < ψ < PI ->
        C = S123 ϕ θ ψ ->
        ϕ' C = ϕ /\ θ' C = θ /\ ψ' C = ψ.
    Proof.
      intros. cbv. rewrite !H2; auto. cbv; ra.
      assert (0 < cos θ). { apply cos_gt_0; try lra. }
      repeat split.
      - rewrite atan2_sin_cos_eq1; auto. lra.
      - rewrite asin_sin; ra.
      - rewrite !(Rmult_comm (cos θ)). rewrite atan2_sin_cos_eq1; auto. lra.
    Qed.
  End alg2.
  
  (* 算法3：保留奇异点，完整的机动范围，即 roll,pitch,yaw ∈ [-π,π] *)
  Module alg3.
    (* 该算法来自于 QQ's book, page94.
         1. 当θ=±π/2时(此时 r11=r21=0)，ϕ和ψ不唯一，可以人为规定 ϕ = 0
         2. 当ϕ,ψ为边界时，即当 r11=r33=1, r21=r31=r32=0, 有两种可能
            (ϕ,θ,ψ) = (0,0,0);(π,π,π)，此时根据与上次的值相近的结果
         3. 其余情况，可在 alg2 的基础上改进，以便θ从(-π/2,π/2)扩展到(-π,π)
            具体做法：
            (1) 计算出6个欧拉角，ϕ0,θ0,ψ0,ϕ1,θ1,ψ1，它们的组合有8种。
            (2) 计算这8种组合下的旋转矩阵与输入矩阵的差的范数（没有说是哪一种）
            (3) 范数最小时的那个组合就是所要求的欧拉角

         思考"步骤3"的原理：
         1. 为何旋转矩阵之差异矩阵的范数最小时对应了所需的欧拉角？
     *)
    
    (** sign of a real number *)
    Definition Rsign (r : R) : R := if r <? 0 then -1 else 1.
    
    Section sec.
      (* Let's have a rotation matrix *)
      Variable C : smat 3.

      (* (5.13) When r11=r21=0, this is the answer *)
      Definition case1_cond : bool := (C.11 =? 0) && (C.21 =? 0).

      (* ϕ, θ, ψ = v.1, v.2, v.3 *)
      Definition case1_values : vec 3 :=
        l2v [0; (Rsign (-C.31)) * (PI / 2); atan2 (-C.12) (C.22)].

      (* (5.15) possible euler angles *)
      
      (* 
           ϕ_0, θ_0, ψ_0 = m.11, m.21, m.31 
           ϕ_1, θ_1, ψ_1 = m.12, m.22, m.32 
       *)
      Definition case2_params : mat 3 2 :=
        let θ_0 := asin (-C.31) in
        l2m [[atan2 (C.32) (C.33); atan2 (-C.32) (-C.33)];
             [θ_0; Rsign θ_0 * PI - θ_0];
             [atan2 (C.21) (C.11); atan2 (-C.21) (-C.11)]].

      (* (5.14) best composition of euler angles *)
      Definition find_best : (R*R*R*R) :=
        let gen_val (ϕ θ ψ : R) : R*R*R*R := (ϕ, θ, ψ, mnormF (C - S123 ϕ θ ψ)%M) in
        let m := case2_params in
        let a111 := gen_val (m.11) (m.21) (m.31) in
        let a112 := gen_val (m.11) (m.21) (m.32) in
        let a121 := gen_val (m.11) (m.22) (m.31) in
        let a122 := gen_val (m.11) (m.22) (m.32) in
        let a211 := gen_val (m.12) (m.21) (m.31) in
        let a212 := gen_val (m.12) (m.21) (m.32) in
        let a221 := gen_val (m.12) (m.22) (m.31) in
        let a222 := gen_val (m.12) (m.22) (m.32) in
        let l := [a111;a112;a121;a122;a211;a212;a221;a222] in
        list_min a111
          (fun x y => match x, y with (_,_,_,x1),(_,_,_,y1) => x1 <? y1 end)
          l.

      Definition case2_values : vec 3 :=
        let '(ϕ,θ,ψ,_) := find_best in
        l2v [ϕ; θ; ψ].

      (** If the matrix is identity matrix, there are two possible solutions *)
      Definition case3_cond : bool :=
        (C.11 =? 1) && (C.33 =? 1) && (C.21 =? 0) && (C.32 =? 0) && (C.31 =? 0).
      
      (** If the euler angles is {0,0,0} or {π,π,π}, then the matrix is identity matrix *)
      Lemma case3_opts_1_eq_mat1 :
        S123 0 0 0 = mat1.
      Proof. meq; ra. Qed.
      
      Lemma case3_opts_2_eq_mat1 :
        S123 PI PI PI = mat1.
      Proof. meq; ra. Qed.

      Definition case3_values (old : vec 3) : vec 3 :=
        (* 根据历史值，与之接近的是正解 *)
        let closest (old opt1 opt2 : R) : R :=
          if Rabs (old - opt1) <? Rabs (old - opt2) then opt1 else opt2 in
        l2v [
            closest (old.1) 0 PI;
            closest (old.2) 0 PI;
            closest (old.3) 0 PI
          ].

      (** final algorithm *)
      Definition euler_angles (old : vec 3) : vec 3 :=
        if case1_cond
        then case1_values
        else if case3_cond
             then case3_values old
             else case2_values.

      (** This algorithm havn't been verified yet. *)
      
    End sec.
  End alg3.
    
End R2Euler_S123.

(** 2. Body-three, 123 *)
Module R2Euler_B123.

  Open Scope R_scope.

  (** 奇异性问题的存在性 *)
  Section singularity.

    (** Claim: If θ = kπ+π/2, then we can not uniquely determine ϕ and ψ. *)

    (* Let's prove some simpler goals first. *)
    
    (** If θ = π/2, then the rotation matrix has following form. *)
    Lemma B123_θ_eq_pi2 : forall (ϕ θ ψ : R),
        θ = PI/2 ->
        B123 ϕ θ ψ =
          l2m [[0; 0; 1];
               [sin (ϕ + ψ); cos (ϕ + ψ); 0];
               [- cos (ϕ + ψ); sin (ϕ + ψ); 0]].
    Proof.
      intros; rewrite H.
      pose proof cos_PI2. pose proof sin_PI2. cbv in H0, H1. meq; ra.
    Qed.

    (** If θ = -π/2, then the rotation matrix has following form. *)
    Lemma B123_θ_eq_pi2_neg : forall (ϕ θ ψ : R),
        θ = -PI/2 ->
        B123 ϕ θ ψ =
          l2m [[0; 0; -1];
               [sin (ψ - ϕ); cos (ψ - ϕ); 0];
               [cos (ψ - ϕ); - sin (ψ - ϕ); 0]].
    Proof.
      intros; rewrite H.
      pose proof cos_PI2. pose proof sin_PI2. cbv in H0, H1. meq; ra.
    Qed.

    (** If θ = π/2, then there are infinite ϕ can generate a same matrix. *)
    Lemma B123_singularity_ϕ_when_θ_eq_pi2 : forall (ϕ θ ψ : R),
        θ = PI/2 -> forall ϕ', (exists ψ', B123 ϕ' θ ψ' = B123 ϕ θ ψ).
    Proof.
      intros. eexists. rewrite !B123_θ_eq_pi2; auto.
      instantiate (1:=ψ + ϕ - ϕ'). repeat (f_equal; try lra).
    Qed.
    
    (** If θ = -π/2, then there are infinite ϕ can generate a same matrix. *)
    Lemma B123_singularity_ϕ_when_θ_eq_pi2_neg : forall (ϕ θ ψ : R),
        θ = -PI/2 -> forall ϕ', (exists ψ', B123 ϕ' θ ψ' = B123 ϕ θ ψ).
    Proof.
      intros. eexists. rewrite !B123_θ_eq_pi2_neg; auto.
      instantiate (1:=ψ - ϕ + ϕ'). repeat (f_equal; try lra).
    Qed.

    (** If θ = ±π/2, then there are infinite ϕ can generate a same matrix. *)
    Theorem B123_singularity_ϕ : forall (ϕ θ ψ : R),
        (θ = PI/2 \/ θ = -PI/2) -> forall ϕ', (exists ψ', B123 ϕ' θ ψ' = B123 ϕ θ ψ).
    Proof.
      intros. destruct H.
      apply B123_singularity_ϕ_when_θ_eq_pi2; auto.
      apply B123_singularity_ϕ_when_θ_eq_pi2_neg; auto.
    Qed.

    (** If θ = π/2, then there are infinite ψ can generate a same matrix. *)
    Lemma B123_singularity_ψ_when_θ_eq_pi2 : forall (ϕ θ ψ : R),
        θ = PI/2 -> forall ψ', (exists ϕ', B123 ϕ' θ ψ' = B123 ϕ θ ψ).
    Proof.
      intros. eexists. rewrite !B123_θ_eq_pi2; auto.
      instantiate (1:=ψ + ϕ - ψ'). repeat (f_equal; try lra).
    Qed.
    
    (** If θ = -π/2, then there are infinite ψ can generate a same matrix. *)
    Lemma B123_singularity_ψ_when_θ_eq_pi2_neg : forall (ϕ θ ψ : R),
        θ = -PI/2 -> forall ψ', (exists ϕ', B123 ϕ' θ ψ' = B123 ϕ θ ψ).
    Proof.
      intros. eexists. rewrite !B123_θ_eq_pi2_neg; auto.
      instantiate (1:=-ψ + ϕ + ψ'). repeat (f_equal; try lra).
    Qed.

    (** If θ = ±π/2, then there are infinite ψ can generate a same matrix. *)
    Theorem B123_singularity_ψ : forall (ϕ θ ψ : R),
        (θ = PI/2 \/ θ = -PI/2) -> forall ψ', (exists ϕ', B123 ϕ' θ ψ' = B123 ϕ θ ψ).
    Proof.
      intros. destruct H.
      apply B123_singularity_ψ_when_θ_eq_pi2; auto.
      apply B123_singularity_ψ_when_θ_eq_pi2_neg; auto.
    Qed.
  End singularity.

  (* 算法1：避开奇异点，小机动范围，即 roll,pitch,yaw ∈ (-π/2,π/2) *)
  Module alg1.
    Definition ϕ' (C : smat 3) := atan (- C.23 / C.33).
    Definition θ' (C : smat 3) := asin (C.13).
    Definition ψ' (C : smat 3) := atan (- C.12 / C.11).
    
    Theorem alg_spec : forall (ϕ θ ψ : R) (C : smat 3),
        -PI/2 < ϕ < PI/2 ->
        -PI/2 < θ < PI/2 ->
        -PI/2 < ψ < PI/2 ->
        C = B123 ϕ θ ψ ->
        ϕ' C = ϕ /\ θ' C = θ /\ ψ' C = ψ.
    Proof.
      intros. v2eALL C.
      apply Vector.v3eq_iff in H2. destruct H2,H3.
      apply Vector.v3eq_iff in H2,H3,H4. cbv in H2,H3,H4.
      cbv. logic.
      - rewrite H8,H6. ra. rewrite atan_tan; auto.
      - rewrite H10. rewrite asin_sin; ra.
      - rewrite H9,H2. ra. rewrite atan_tan; ra.
    Qed.
  End alg1.

  (* 算法2：避开奇异点，大机动范围，即 pitch ∈ (-π/2,π/2), roll,yaw ∈ (-π,π) *)
  Module alg2.
    Definition ϕ' (C : smat 3) := atan2 (- C.23) (C.33).
    Definition θ' (C : smat 3) := asin (C.13).
    Definition ψ' (C : smat 3) := atan2 (- C.12) (C.11).

    Theorem alg_spec : forall (ϕ θ ψ : R) (C : smat 3),
        -PI < ϕ < PI ->
        -PI/2 < θ < PI/2 ->
        -PI < ψ < PI ->
        C = B123 ϕ θ ψ ->
        ϕ' C = ϕ /\ θ' C = θ /\ ψ' C = ψ.
    Proof.
      intros. cbv. rewrite !H2; auto. cbv; ra.
      assert (0 < cos θ). { apply cos_gt_0; try lra. }
      repeat split.
      - rewrite atan2_sin_cos_eq1; auto. lra.
      - rewrite asin_sin; ra.
      - rewrite !(Rmult_comm (cos θ)). rewrite atan2_sin_cos_eq1; auto. lra.
    Qed.
  End alg2.

End R2Euler_B123.
