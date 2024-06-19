
type __ = Obj.t

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



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

val rminus : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val iPR_2 : positive -> RbaseSymbolsImpl.coq_R

val iPR : positive -> RbaseSymbolsImpl.coq_R

val iZR : z -> RbaseSymbolsImpl.coq_R

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl :
 RinvSig

val rdiv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val cos : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val sin : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val pI : RbaseSymbolsImpl.coq_R

val sqrt : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

type 'tA dec = 'tA -> 'tA -> bool
  (* singleton inductive, whose constructor was Build_Dec *)

val dec0 : 'a1 dec -> 'a1 -> 'a1 -> bool

val nat_lt_Dec : int dec

module NormedOrderedFieldElementTypeR :
 sig
  type tA = RbaseSymbolsImpl.coq_R

  val coq_Azero : tA
 end

type fin = int
  (* singleton inductive, whose constructor was Fin *)

val fin2nat : int -> fin -> int

val nat2finS : int -> int -> fin

val finseq : int -> fin list

type 'tA vec = fin -> 'tA

val vrepeat : int -> 'a1 -> 'a1 vec

val vzero : 'a1 -> int -> 'a1 vec

val l2v : 'a1 -> int -> 'a1 list -> 'a1 vec

val v2l : int -> 'a1 vec -> 'a1 list

val m2l : int -> int -> 'a1 vec vec -> 'a1 list list

val l2m : 'a1 -> int -> int -> 'a1 list list -> 'a1 vec vec

val l2v0 : int -> NormedOrderedFieldElementTypeR.tA list -> NormedOrderedFieldElementTypeR.tA vec

val l2m0 : int -> int -> NormedOrderedFieldElementTypeR.tA list list -> NormedOrderedFieldElementTypeR.tA vec vec

val m2l0 : int -> int -> NormedOrderedFieldElementTypeR.tA vec vec -> NormedOrderedFieldElementTypeR.tA list list

val deg2rad : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val rot : NormedOrderedFieldElementTypeR.tA vec -> RbaseSymbolsImpl.coq_R -> NormedOrderedFieldElementTypeR.tA vec vec

val ex_3_6 : NormedOrderedFieldElementTypeR.tA list list
