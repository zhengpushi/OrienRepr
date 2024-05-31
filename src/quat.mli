
type __ = Obj.t

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



val add : nat -> nat -> nat

val sub : nat -> nat -> nat

type 'a t2 = 'a * 'a

type 'a t3 = 'a t2 * 'a

type 'a t_2_2 = 'a t2 * 'a t2

type 'a t_3_3 = ('a t3 * 'a t3) * 'a t3

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
  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat

  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val even : nat -> bool

  val pow : nat -> nat -> nat

  val divmod : nat -> nat -> nat -> nat -> nat * nat

  val modulo : nat -> nat -> nat
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

  val size_nat : positive -> nat

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val ggcdn : nat -> positive -> positive -> positive * (positive * positive)

  val ggcd : positive -> positive -> positive * (positive * positive)

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_nat : nat -> positive

  val of_succ_nat : nat -> positive
 end

val pow_pos : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val seq : nat -> nat -> nat list

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

  val max : z -> z -> z

  val min : z -> z -> z

  val abs : z -> z

  val to_nat : z -> nat

  val of_nat : nat -> z

  val to_pos : z -> positive

  val ggcd : z -> z -> z * (z * z)
 end

val z_lt_dec : z -> z -> bool

val z_lt_ge_dec : z -> z -> bool

val z_lt_le_dec : z -> z -> bool

type q = { qnum : z; qden : positive }

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qlt_le_dec : q -> q -> bool

val qpower_positive : q -> positive -> q

val qpower : q -> z -> q

val z_inj_nat_rev : nat -> z

type cReal = { seq0 : (z -> q); scale : z }

type cRealLt = z

val cRealLt_lpo_dec :
  cReal -> cReal -> (__ -> (nat -> bool) -> nat option) -> (cRealLt, __) sum

val sig_forall_dec : (nat -> bool) -> nat option

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

val iPR_2 : positive -> RbaseSymbolsImpl.coq_R

val iPR : positive -> RbaseSymbolsImpl.coq_R

val iZR : z -> RbaseSymbolsImpl.coq_R

val total_order_T : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool option

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl :
 RinvSig

val req_EM_T : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool

type 'a dec = 'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_Dec *)

val dec0 : 'a1 dec -> 'a1 -> 'a1 -> bool

val nat_lshl : nat -> nat -> nat -> nat

val nat_lshr : nat -> nat -> nat -> nat

val seqeq_dec : 'a1 dec -> nat -> (nat -> 'a1) dec

val seq2eq_dec : 'a1 dec -> nat -> nat -> (nat -> nat -> 'a1) dec

val seqsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> (nat -> 'a1) -> nat -> 'a1

module Coq__2 : sig
 type 'a mat = nat -> nat -> 'a
   (* singleton inductive, whose constructor was mk_mat *)
end
include module type of struct include Coq__2 end

val matf : nat -> nat -> 'a1 mat -> nat -> nat -> 'a1

val f2m : nat -> nat -> (nat -> nat -> 'a1) -> 'a1 mat

val m2f : nat -> nat -> 'a1 mat -> nat -> nat -> 'a1

val meq_dec : 'a1 dec -> nat -> nat -> 'a1 mat dec

val mnth : 'a1 -> nat -> nat -> 'a1 mat -> nat -> nat -> 'a1

val l2m : 'a1 -> nat -> nat -> 'a1 list list -> 'a1 mat

val m2l : nat -> nat -> 'a1 mat -> 'a1 list list

val mcshl : nat -> nat -> 'a1 mat -> nat -> 'a1 mat

val mcshr : 'a1 -> nat -> nat -> 'a1 mat -> nat -> 'a1 mat

val mclshl : nat -> nat -> 'a1 mat -> nat -> 'a1 mat

val mclshr : nat -> nat -> 'a1 mat -> nat -> 'a1 mat

val mk_diag : 'a1 -> nat -> 'a1 list -> 'a1 mat

val mconsr : nat -> nat -> 'a1 mat -> 'a1 mat -> 'a1 mat

val mconsc : nat -> nat -> 'a1 mat -> 'a1 mat -> 'a1 mat

val mappr : nat -> nat -> nat -> 'a1 mat -> 'a1 mat -> 'a1 mat

val mappc : nat -> nat -> nat -> 'a1 mat -> 'a1 mat -> 'a1 mat

val mk_mat_0_c : 'a1 -> nat -> 'a1 mat

val mk_mat_1_1 : 'a1 -> 'a1 -> 'a1 mat

val mk_mat_1_2 : 'a1 -> 'a1 -> 'a1 -> 'a1 mat

val mk_mat_1_3 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 mat

val mk_mat_1_4 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 mat

val mk_mat_1_c : 'a1 -> nat -> 'a1 list -> 'a1 mat

val mk_mat_r_0 : 'a1 -> nat -> 'a1 mat

val mk_mat_2_1 : 'a1 -> 'a1 -> 'a1 -> 'a1 mat

val mk_mat_2_2 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 mat

val mk_mat_3_1 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 mat

val mk_mat_3_3 :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 mat

val mk_mat_4_1 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 mat

val mk_mat_4_4 :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 mat

val mk_mat_r_1 : 'a1 -> nat -> 'a1 list -> 'a1 mat

val t2m_2_2 : 'a1 -> 'a1 t_2_2 -> 'a1 mat

val t2m_3_3 : 'a1 -> 'a1 t_3_3 -> 'a1 mat

val m2t_1_1 : 'a1 mat -> 'a1

val scalar_of_mat : 'a1 mat -> 'a1

val m2t_2_2 : 'a1 mat -> 'a1 t_2_2

val m2t_3_3 : 'a1 mat -> 'a1 t_3_3

val mmap : nat -> nat -> ('a1 -> 'a1) -> 'a1 mat -> 'a1 mat

val mmap2 : nat -> nat -> ('a1 -> 'a1 -> 'a1) -> 'a1 mat -> 'a1 mat -> 'a1 mat

val mtrans : nat -> nat -> 'a1 mat -> 'a1 mat

val mat0 : 'a1 -> nat -> nat -> 'a1 mat

val mat1 : 'a1 -> 'a1 -> nat -> 'a1 mat

val mtrace : ('a1 -> 'a1 -> 'a1) -> 'a1 -> nat -> 'a1 mat -> 'a1

val madd : ('a1 -> 'a1 -> 'a1) -> nat -> nat -> 'a1 mat -> 'a1 mat -> 'a1 mat

val mopp : ('a1 -> 'a1) -> nat -> nat -> 'a1 mat -> 'a1 mat

val msub : ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> nat -> nat -> 'a1 mat -> 'a1 mat -> 'a1 mat

val mcmul : ('a1 -> 'a1 -> 'a1) -> nat -> nat -> 'a1 -> 'a1 mat -> 'a1 mat

val mmulc : ('a1 -> 'a1 -> 'a1) -> nat -> nat -> 'a1 mat -> 'a1 -> 'a1 mat

val mmul :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> nat -> nat -> nat -> 'a1 mat -> 'a1
  mat -> 'a1 mat

val mhp : ('a1 -> 'a1 -> 'a1) -> nat -> 'a1 mat -> 'a1 mat -> 'a1 mat

val msubmat : nat -> 'a1 mat -> nat -> nat -> 'a1 mat

val mdet :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> nat -> 'a1 mat
  -> 'a1

val mdet1 : 'a1 mat -> 'a1

val mdet2 : ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 mat -> 'a1

val mdet3 : ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 mat -> 'a1

val mdet4 : ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 mat -> 'a1

val madj :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> nat -> 'a1 mat
  -> 'a1 mat

val mchgcol : nat -> 'a1 mat -> nat -> 'a1 mat -> 'a1 mat

val cramerRule :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1)
  -> nat -> 'a1 mat -> 'a1 mat -> 'a1 mat

val minv :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1)
  -> nat -> 'a1 mat -> 'a1 mat

val minv1 : 'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> 'a1 mat -> 'a1 mat

val minv2 :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> 'a1
  mat -> 'a1 mat

val minv3 :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> 'a1
  mat -> 'a1 mat

val minv4 :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> 'a1
  mat -> 'a1 mat

val brt_e : 'a1 -> nat -> nat -> nat -> nat -> 'a1 -> 'a1 mat

val brt_cmul : 'a1 -> 'a1 -> nat -> nat -> nat -> 'a1 -> 'a1 mat

val brt_add : ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> nat -> nat -> nat -> 'a1 -> 'a1 mat

val brt_swap :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> 'a1 -> nat -> nat -> nat -> 'a1 mat

val get_first_none_zero : 'a1 -> 'a1 dec -> nat -> 'a1 mat -> nat -> nat -> nat

val elem_change_down :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> nat -> 'a1 mat
  -> nat -> nat -> 'a1 mat * 'a1 mat

val row_echelon_form :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1)
  -> 'a1 dec -> nat -> 'a1 mat -> nat -> ('a1 mat * 'a1 mat) option

val elem_change_up :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> nat -> 'a1 mat
  -> nat -> nat -> 'a1 mat * 'a1 mat

val fst_to_I :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> nat -> 'a1 mat
  -> nat -> 'a1 mat * 'a1 mat

val minv_gauss :
  ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1)
  -> 'a1 dec -> nat -> 'a1 mat -> 'a1 mat option

module DecidableElementTypeR :
 sig
  type coq_A = RbaseSymbolsImpl.coq_R

  val coq_Dec_Aeq : coq_A dec
 end

module type DecidableFieldElementType =
 sig
  type coq_A

  val coq_Azero : coq_A

  val coq_Aone : coq_A

  val coq_Aadd : coq_A -> coq_A -> coq_A

  val coq_Amul : coq_A -> coq_A -> coq_A

  val coq_Aopp : coq_A -> coq_A

  val coq_Ainv : coq_A -> coq_A

  val coq_Dec_Aeq : coq_A dec
 end

module DecidableFieldElementTypeR :
 sig
  type coq_A = RbaseSymbolsImpl.coq_R

  val coq_Azero : coq_A

  val coq_Aone : coq_A

  val coq_Aadd : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

  val coq_Aopp : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

  val coq_Amul : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

  val coq_Ainv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

  val coq_Dec_Aeq : DecidableElementTypeR.coq_A dec
 end

module DecidableFieldMatrixTheory :
 functor (E:DecidableFieldElementType) ->
 sig
  type mat = E.coq_A Coq__2.mat

  val f2m : nat -> nat -> (nat -> nat -> E.coq_A) -> mat

  val m2f : nat -> nat -> mat -> nat -> nat -> E.coq_A

  val mnth : nat -> nat -> mat -> nat -> nat -> E.coq_A

  val l2m : nat -> nat -> E.coq_A list list -> mat

  val m2l : nat -> nat -> mat -> E.coq_A list list

  val mcshl : nat -> nat -> mat -> nat -> mat

  val mcshr : nat -> nat -> mat -> nat -> mat

  val mclshl : nat -> nat -> mat -> nat -> mat

  val mclshr : nat -> nat -> mat -> nat -> mat

  val mk_diag : nat -> E.coq_A list -> E.coq_A Coq__2.mat

  val mconsr : nat -> nat -> mat -> mat -> mat

  val mconsc : nat -> nat -> mat -> mat -> mat

  val mappr : nat -> nat -> nat -> mat -> mat -> mat

  val mappc : nat -> nat -> nat -> mat -> mat -> mat

  val mk_mat_0_c : nat -> mat

  val mk_mat_1_1 : E.coq_A -> mat

  val mk_mat_1_2 : E.coq_A -> E.coq_A -> mat

  val mk_mat_1_3 : E.coq_A -> E.coq_A -> E.coq_A -> mat

  val mk_mat_1_4 : E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> mat

  val mk_mat_1_c : nat -> E.coq_A list -> mat

  val mk_mat_r_0 : nat -> mat

  val mk_mat_2_1 : E.coq_A -> E.coq_A -> mat

  val mk_mat_3_1 : E.coq_A -> E.coq_A -> E.coq_A -> mat

  val mk_mat_4_1 : E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> mat

  val mk_mat_r_1 : nat -> E.coq_A list -> mat

  val mk_mat_2_2 : E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> mat

  val mk_mat_3_3 :
    E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A ->
    E.coq_A -> mat

  val mk_mat_4_4 :
    E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A ->
    E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A -> E.coq_A ->
    mat

  val t2m_2_2 : E.coq_A t_2_2 -> mat

  val t2m_3_3 : E.coq_A t_3_3 -> mat

  val m2t_1_1 : mat -> E.coq_A

  val scalar_of_mat : mat -> E.coq_A

  val m2t_2_2 : mat -> E.coq_A t_2_2

  val m2t_3_3 : mat -> E.coq_A t_3_3

  val mmap : nat -> nat -> (E.coq_A -> E.coq_A) -> mat -> mat

  val mmap2 : nat -> nat -> (E.coq_A -> E.coq_A -> E.coq_A) -> mat -> mat -> mat

  val mtrans : nat -> nat -> mat -> mat

  val mat0 : nat -> nat -> mat

  val mat1 : nat -> mat

  val mtrace : nat -> E.coq_A Coq__2.mat -> E.coq_A

  val madd : nat -> nat -> mat -> mat -> mat

  val mopp : nat -> nat -> mat -> mat

  val msub : nat -> nat -> mat -> mat -> mat

  val mcmul : nat -> nat -> E.coq_A -> mat -> mat

  val mmulc : nat -> nat -> mat -> E.coq_A -> mat

  val mmul : nat -> nat -> nat -> mat -> mat -> mat

  val mhp : nat -> E.coq_A Coq__2.mat -> E.coq_A Coq__2.mat -> E.coq_A Coq__2.mat

  val mdet : nat -> E.coq_A Coq__2.mat -> E.coq_A

  val mdet1 : E.coq_A Coq__2.mat -> E.coq_A

  val mdet2 : E.coq_A Coq__2.mat -> E.coq_A

  val mdet3 : E.coq_A Coq__2.mat -> E.coq_A

  val madj : nat -> E.coq_A Coq__2.mat -> E.coq_A Coq__2.mat

  val mchgcol : nat -> E.coq_A Coq__2.mat -> nat -> mat -> E.coq_A Coq__2.mat

  val cramerRule : nat -> E.coq_A Coq__2.mat -> mat -> mat

  val minv : nat -> E.coq_A Coq__2.mat -> E.coq_A Coq__2.mat

  val minv1 : E.coq_A Coq__2.mat -> E.coq_A Coq__2.mat

  val minv2 : E.coq_A Coq__2.mat -> E.coq_A Coq__2.mat

  val minv3 : E.coq_A Coq__2.mat -> E.coq_A Coq__2.mat

  val minv4 : E.coq_A Coq__2.mat -> E.coq_A Coq__2.mat

  val meq_dec : nat -> nat -> mat dec

  val minv_gauss : nat -> mat -> mat option
 end

module MatrixTheoryR :
 sig
  type mat = DecidableFieldElementTypeR.coq_A Coq__2.mat

  val f2m : nat -> nat -> (nat -> nat -> DecidableFieldElementTypeR.coq_A) -> mat

  val m2f : nat -> nat -> mat -> nat -> nat -> DecidableFieldElementTypeR.coq_A

  val mnth : nat -> nat -> mat -> nat -> nat -> DecidableFieldElementTypeR.coq_A

  val l2m : nat -> nat -> DecidableFieldElementTypeR.coq_A list list -> mat

  val m2l : nat -> nat -> mat -> DecidableFieldElementTypeR.coq_A list list

  val mcshl : nat -> nat -> mat -> nat -> mat

  val mcshr : nat -> nat -> mat -> nat -> mat

  val mclshl : nat -> nat -> mat -> nat -> mat

  val mclshr : nat -> nat -> mat -> nat -> mat

  val mk_diag :
    nat -> DecidableFieldElementTypeR.coq_A list -> DecidableFieldElementTypeR.coq_A
    Coq__2.mat

  val mconsr : nat -> nat -> mat -> mat -> mat

  val mconsc : nat -> nat -> mat -> mat -> mat

  val mappr : nat -> nat -> nat -> mat -> mat -> mat

  val mappc : nat -> nat -> nat -> mat -> mat -> mat

  val mk_mat_0_c : nat -> mat

  val mk_mat_1_1 : DecidableFieldElementTypeR.coq_A -> mat

  val mk_mat_1_2 :
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A -> mat

  val mk_mat_1_3 :
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A ->
    DecidableFieldElementTypeR.coq_A -> mat

  val mk_mat_1_4 :
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A ->
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A -> mat

  val mk_mat_1_c : nat -> DecidableFieldElementTypeR.coq_A list -> mat

  val mk_mat_r_0 : nat -> mat

  val mk_mat_2_1 :
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A -> mat

  val mk_mat_3_1 :
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A ->
    DecidableFieldElementTypeR.coq_A -> mat

  val mk_mat_4_1 :
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A ->
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A -> mat

  val mk_mat_r_1 : nat -> DecidableFieldElementTypeR.coq_A list -> mat

  val mk_mat_2_2 :
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A ->
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A -> mat

  val mk_mat_3_3 :
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A ->
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A ->
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A ->
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A ->
    DecidableFieldElementTypeR.coq_A -> mat

  val mk_mat_4_4 :
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A ->
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A ->
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A ->
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A ->
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A ->
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A ->
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A ->
    DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A -> mat

  val t2m_2_2 : DecidableFieldElementTypeR.coq_A t_2_2 -> mat

  val t2m_3_3 : DecidableFieldElementTypeR.coq_A t_3_3 -> mat

  val m2t_1_1 : mat -> DecidableFieldElementTypeR.coq_A

  val scalar_of_mat : mat -> DecidableFieldElementTypeR.coq_A

  val m2t_2_2 : mat -> DecidableFieldElementTypeR.coq_A t_2_2

  val m2t_3_3 : mat -> DecidableFieldElementTypeR.coq_A t_3_3

  val mmap :
    nat -> nat -> (DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A) ->
    mat -> mat

  val mmap2 :
    nat -> nat -> (DecidableFieldElementTypeR.coq_A -> DecidableFieldElementTypeR.coq_A ->
    DecidableFieldElementTypeR.coq_A) -> mat -> mat -> mat

  val mtrans : nat -> nat -> mat -> mat

  val mat0 : nat -> nat -> mat

  val mat1 : nat -> mat

  val mtrace :
    nat -> DecidableFieldElementTypeR.coq_A Coq__2.mat -> DecidableFieldElementTypeR.coq_A

  val madd : nat -> nat -> mat -> mat -> mat

  val mopp : nat -> nat -> mat -> mat

  val msub : nat -> nat -> mat -> mat -> mat

  val mcmul : nat -> nat -> DecidableFieldElementTypeR.coq_A -> mat -> mat

  val mmulc : nat -> nat -> mat -> DecidableFieldElementTypeR.coq_A -> mat

  val mmul : nat -> nat -> nat -> mat -> mat -> mat

  val mhp :
    nat -> DecidableFieldElementTypeR.coq_A Coq__2.mat -> DecidableFieldElementTypeR.coq_A
    Coq__2.mat -> DecidableFieldElementTypeR.coq_A Coq__2.mat

  val mdet :
    nat -> DecidableFieldElementTypeR.coq_A Coq__2.mat -> DecidableFieldElementTypeR.coq_A

  val mdet1 : DecidableFieldElementTypeR.coq_A Coq__2.mat -> DecidableFieldElementTypeR.coq_A

  val mdet2 : DecidableFieldElementTypeR.coq_A Coq__2.mat -> DecidableFieldElementTypeR.coq_A

  val mdet3 : DecidableFieldElementTypeR.coq_A Coq__2.mat -> DecidableFieldElementTypeR.coq_A

  val madj :
    nat -> DecidableFieldElementTypeR.coq_A Coq__2.mat -> DecidableFieldElementTypeR.coq_A
    Coq__2.mat

  val mchgcol :
    nat -> DecidableFieldElementTypeR.coq_A Coq__2.mat -> nat -> mat ->
    DecidableFieldElementTypeR.coq_A Coq__2.mat

  val cramerRule : nat -> DecidableFieldElementTypeR.coq_A Coq__2.mat -> mat -> mat

  val minv :
    nat -> DecidableFieldElementTypeR.coq_A Coq__2.mat -> DecidableFieldElementTypeR.coq_A
    Coq__2.mat

  val minv1 :
    DecidableFieldElementTypeR.coq_A Coq__2.mat -> DecidableFieldElementTypeR.coq_A
    Coq__2.mat

  val minv2 :
    DecidableFieldElementTypeR.coq_A Coq__2.mat -> DecidableFieldElementTypeR.coq_A
    Coq__2.mat

  val minv3 :
    DecidableFieldElementTypeR.coq_A Coq__2.mat -> DecidableFieldElementTypeR.coq_A
    Coq__2.mat

  val minv4 :
    DecidableFieldElementTypeR.coq_A Coq__2.mat -> DecidableFieldElementTypeR.coq_A
    Coq__2.mat

  val meq_dec : nat -> nat -> mat dec

  val minv_gauss : nat -> mat -> mat option
 end
