
type __ = Obj.t

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val pred : int -> int

val add : int -> int -> int

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val pow : int -> int -> int
 end

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val pow : positive -> positive -> positive

  val size_nat : positive -> int

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val ggcdn : int -> positive -> positive -> positive * (positive * positive)

  val ggcd : positive -> positive -> positive * (positive * positive)

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> int

  val of_nat : int -> positive

  val of_succ_nat : int -> positive
 end

val nth : int -> 'a1 list -> 'a1 -> 'a1

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : int -> int -> int list

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val sgn : z -> z

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val max : z -> z -> z

  val min : z -> z -> z

  val abs : z -> z

  val to_nat : z -> int

  val of_nat : int -> z

  val to_pos : z -> positive

  val pos_div_eucl : positive -> z -> z * z

  val div_eucl : z -> z -> z * z

  val div : z -> z -> z

  val ggcd : z -> z -> z * (z * z)
 end

type q = { qnum : z; qden : positive }

type cReal = { seq0 : (z -> q); scale : z }

type dReal = (q -> bool)

module type RbaseSymbolsSig =
 sig
  type coq_R

  val coq_Rabst : cReal -> coq_R

  val coq_Rrepr : coq_R -> cReal

  val coq_R0 : coq_R

  val coq_R1 : coq_R

  val coq_Rplus : coq_R -> coq_R -> coq_R

  val coq_Rmult : coq_R -> coq_R -> coq_R

  val coq_Ropp : coq_R -> coq_R
 end

module RbaseSymbolsImpl :
 RbaseSymbolsSig

val rminus :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val iPR_2 : positive -> RbaseSymbolsImpl.coq_R

val iPR : positive -> RbaseSymbolsImpl.coq_R

val iZR : z -> RbaseSymbolsImpl.coq_R

val total_order_T :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool option

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl :
 RinvSig

val rdiv :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val pow0 : RbaseSymbolsImpl.coq_R -> int -> RbaseSymbolsImpl.coq_R

val rlt_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

val rle_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

val rlt_le_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

val rle_lt_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

val rsqr : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val cos : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val sin : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val pI : RbaseSymbolsImpl.coq_R

val sqrt : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val atan : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val asin : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val acos : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

type 'tA dec =
  'tA -> 'tA -> bool
  (* singleton inductive, whose constructor was Build_Dec *)

val dec0 : 'a1 dec -> 'a1 -> 'a1 -> bool

val nat_eq_Dec : int dec

val nat_lt_Dec : int dec

module NormedOrderedFieldElementTypeR :
 sig
  type tA = RbaseSymbolsImpl.coq_R

  val coq_Azero : tA

  val coq_Aadd :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

  val coq_Aone : tA

  val coq_Aopp : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

  val coq_Amul :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

val rleb : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

val rltb : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

val atan2 :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

type fin = int
  (* singleton inductive, whose constructor was Fin *)

val fin2nat : int -> fin -> int

val nat2finS : int -> int -> fin

val nat2fin : int -> int -> fin

val fSuccRange : int -> fin -> fin

val fPredRange : int -> fin -> fin

val fPredRangeP : int -> fin -> fin

val fSuccRangeS : int -> fin -> fin

val finseq : int -> fin list

val seqsumAux : ('a1 -> 'a1 -> 'a1) -> int -> (int -> 'a1) -> 'a1 -> 'a1

val seqsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> (int -> 'a1) -> 'a1

type 'tA vec = fin -> 'tA

val vrepeat : int -> 'a1 -> 'a1 vec

val vzero : 'a1 -> int -> 'a1 vec

val v2f : 'a1 -> int -> 'a1 vec -> int -> 'a1

val l2v : 'a1 -> int -> 'a1 list -> 'a1 vec

val v2l : int -> 'a1 vec -> 'a1 list

val mkvec3 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec

val vmap : int -> ('a1 -> 'a2) -> 'a1 vec -> 'a2 vec

val vmap2 : int -> ('a1 -> 'a2 -> 'a3) -> 'a1 vec -> 'a2 vec -> 'a3 vec

val vremoveH : int -> 'a1 vec -> 'a1 vec

val vremoveT : int -> 'a1 vec -> 'a1 vec

val vconsH : int -> 'a1 -> 'a1 vec -> 'a1 vec

val vconsT : int -> 'a1 vec -> 'a1 -> 'a1 vec

val vsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1 vec -> 'a1

val vadd : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec -> 'a1 vec

val vopp : ('a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec

val vscal : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 vec -> 'a1 vec

val vdot :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec
  -> 'a1

val m2l : int -> int -> 'a1 vec vec -> 'a1 list list

val l2m : 'a1 -> int -> int -> 'a1 list list -> 'a1 vec vec

val madd :
  ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 vec vec -> 'a1 vec vec -> 'a1 vec vec

val mat1 : 'a1 -> 'a1 -> int -> 'a1 vec vec

val mscal : ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1 vec vec -> 'a1 vec vec

val mmul :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> int -> int -> 'a1
  vec vec -> 'a1 vec vec -> 'a1 vec vec

val mmulv :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 vec vec
  -> 'a1 vec -> 'a1 vec

val v2l0 :
  int -> NormedOrderedFieldElementTypeR.tA vec ->
  NormedOrderedFieldElementTypeR.tA list

val l2v0 :
  int -> NormedOrderedFieldElementTypeR.tA list ->
  NormedOrderedFieldElementTypeR.tA vec

val mkvec0 :
  NormedOrderedFieldElementTypeR.tA -> NormedOrderedFieldElementTypeR.tA ->
  NormedOrderedFieldElementTypeR.tA -> NormedOrderedFieldElementTypeR.tA vec

val vtail :
  int -> NormedOrderedFieldElementTypeR.tA vec ->
  NormedOrderedFieldElementTypeR.tA

val vremoveH0 :
  int -> NormedOrderedFieldElementTypeR.tA vec ->
  NormedOrderedFieldElementTypeR.tA vec

val vremoveT0 :
  int -> NormedOrderedFieldElementTypeR.tA vec ->
  NormedOrderedFieldElementTypeR.tA vec

val vconsH0 :
  int -> NormedOrderedFieldElementTypeR.tA -> NormedOrderedFieldElementTypeR.tA
  vec -> NormedOrderedFieldElementTypeR.tA vec

val vconsT0 :
  int -> NormedOrderedFieldElementTypeR.tA vec ->
  NormedOrderedFieldElementTypeR.tA -> NormedOrderedFieldElementTypeR.tA vec

val l2m0 :
  int -> int -> NormedOrderedFieldElementTypeR.tA list list ->
  NormedOrderedFieldElementTypeR.tA vec vec

val m2l0 :
  int -> int -> NormedOrderedFieldElementTypeR.tA vec vec ->
  NormedOrderedFieldElementTypeR.tA list list

val vadd0 :
  int -> NormedOrderedFieldElementTypeR.tA vec ->
  NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA vec

val madd0 :
  int -> int -> NormedOrderedFieldElementTypeR.tA vec vec ->
  NormedOrderedFieldElementTypeR.tA vec vec -> NormedOrderedFieldElementTypeR.tA
  vec vec

val vopp0 :
  int -> NormedOrderedFieldElementTypeR.tA vec ->
  NormedOrderedFieldElementTypeR.tA vec

val vscal0 :
  int -> NormedOrderedFieldElementTypeR.tA -> NormedOrderedFieldElementTypeR.tA
  vec -> NormedOrderedFieldElementTypeR.tA vec

val vdot0 :
  int -> NormedOrderedFieldElementTypeR.tA vec ->
  NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA

val mat0 : int -> NormedOrderedFieldElementTypeR.tA vec vec

val mscal0 :
  int -> int -> NormedOrderedFieldElementTypeR.tA ->
  NormedOrderedFieldElementTypeR.tA vec vec -> NormedOrderedFieldElementTypeR.tA
  vec vec

val mmul0 :
  int -> int -> int -> NormedOrderedFieldElementTypeR.tA vec vec ->
  NormedOrderedFieldElementTypeR.tA vec vec -> NormedOrderedFieldElementTypeR.tA
  vec vec

val mmulv0 :
  int -> int -> NormedOrderedFieldElementTypeR.tA vec vec ->
  NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA vec

val v3cross :
  NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA vec
  -> NormedOrderedFieldElementTypeR.tA vec

val skew3 :
  NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA vec
  vec

type axisAngle = { aaAxis : NormedOrderedFieldElementTypeR.tA vec;
                   aaAngle : RbaseSymbolsImpl.coq_R }

val v2aa : NormedOrderedFieldElementTypeR.tA vec -> axisAngle

val aa2v : axisAngle -> NormedOrderedFieldElementTypeR.tA vec

val rotaa :
  axisAngle -> NormedOrderedFieldElementTypeR.tA vec ->
  NormedOrderedFieldElementTypeR.tA vec

val aa2mat : axisAngle -> NormedOrderedFieldElementTypeR.tA vec vec

val rx : RbaseSymbolsImpl.coq_R -> NormedOrderedFieldElementTypeR.tA vec vec

val ry : RbaseSymbolsImpl.coq_R -> NormedOrderedFieldElementTypeR.tA vec vec

val rz : RbaseSymbolsImpl.coq_R -> NormedOrderedFieldElementTypeR.tA vec vec

val s123 :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R ->
  NormedOrderedFieldElementTypeR.tA vec vec

module R2Euler_S123 :
 sig
  module Coq_alg2 :
   sig
    val _UU03d5_' :
      NormedOrderedFieldElementTypeR.tA vec vec -> RbaseSymbolsImpl.coq_R

    val _UU03b8_' :
      NormedOrderedFieldElementTypeR.tA vec vec -> RbaseSymbolsImpl.coq_R

    val _UU03c8_' :
      NormedOrderedFieldElementTypeR.tA vec vec -> RbaseSymbolsImpl.coq_R
   end
 end

type quat = NormedOrderedFieldElementTypeR.tA vec

val si2q : RbaseSymbolsImpl.coq_R -> NormedOrderedFieldElementTypeR.tA vec -> quat

val q2im : quat -> NormedOrderedFieldElementTypeR.tA vec

val im2q : NormedOrderedFieldElementTypeR.tA vec -> quat

val qmul : quat -> quat -> quat

val qconj : quat -> quat

val aa2quat : axisAngle -> quat

val quat2aa : quat -> axisAngle

val qrot : quat -> quat -> quat

val qrotv :
  quat -> NormedOrderedFieldElementTypeR.tA vec ->
  NormedOrderedFieldElementTypeR.tA vec

val q2m : quat -> NormedOrderedFieldElementTypeR.tA vec vec

val rsign : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val m2q : NormedOrderedFieldElementTypeR.tA vec vec -> quat

val rotx :
  RbaseSymbolsImpl.coq_R -> NormedOrderedFieldElementTypeR.tA vec ->
  NormedOrderedFieldElementTypeR.tA vec

val roty :
  RbaseSymbolsImpl.coq_R -> NormedOrderedFieldElementTypeR.tA vec ->
  NormedOrderedFieldElementTypeR.tA vec

val rotz :
  RbaseSymbolsImpl.coq_R -> NormedOrderedFieldElementTypeR.tA vec ->
  NormedOrderedFieldElementTypeR.tA vec

val rotaa0 :
  NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA vec
  -> NormedOrderedFieldElementTypeR.tA vec

val rotByM :
  NormedOrderedFieldElementTypeR.tA vec vec -> NormedOrderedFieldElementTypeR.tA
  vec -> NormedOrderedFieldElementTypeR.tA vec

val rotByQ :
  NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA vec
  -> NormedOrderedFieldElementTypeR.tA vec

val rot2ByQ :
  NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA vec
  -> NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA
  vec

val e2m :
  NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA vec
  vec

val m2e :
  NormedOrderedFieldElementTypeR.tA vec vec -> NormedOrderedFieldElementTypeR.tA
  vec

val a2m :
  NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA vec
  vec

val a2e :
  NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA vec

val q2e :
  NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA vec

val e2q :
  NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA vec

val q2a :
  NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA vec

val a2q :
  NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA vec
