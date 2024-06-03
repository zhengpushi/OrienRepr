(*
  Copyright 2023 ZhengPu Shi
  This file is part of VFCS. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.

  purpose   : Quaternion_rot (rotation theory)
  author    : ZhengPu Shi
  date      : 2022.06

  remark    :
  1. quat:{w,x,y,z} <==> vec4[w;x;y;z]
                    <==> vec3[x;y;z]

  reference :
  1. (QQ) Introduction to Multicopter Design and Control, Springer, Quan Quan, page 96
  2. (Dunn) 3D Math Primer for Graphics and Game Development, Second Edition
     Fletcher Dunn, Ian Parberry.
  3. (Krasjet) Quaternion and 3D rotation（四元数与三维旋转）
 *)

Require Export Ratan2.
Require Export Quaternion_base.

Open Scope R.
Open Scope mat_scope.
Open Scope cvec_scope.
Open Scope quat_scope.
