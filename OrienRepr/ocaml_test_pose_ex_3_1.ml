
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add = (+)
end
include Coq__1

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Stdlib.Int.succ (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Stdlib.Int.succ 0)
      (fun m0 -> mul n (pow n m0))
      m
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p -> (match y with
               | XI q0 -> XI (add p q0)
               | XO q0 -> XO (add p q0)
               | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH -> (match y with
             | XI q0 -> XI (succ q0)
             | XO q0 -> XO (succ q0)
             | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val pow : positive -> positive -> positive **)

  let pow x =
    iter (mul x) XH

  (** val size_nat : positive -> int **)

  let rec size_nat = function
  | XI p0 -> Stdlib.Int.succ (size_nat p0)
  | XO p0 -> Stdlib.Int.succ (size_nat p0)
  | XH -> Stdlib.Int.succ 0

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val ggcdn : int -> positive -> positive -> positive * (positive * positive) **)

  let rec ggcdn n a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (XH, (a, b)))
      (fun n0 ->
      match a with
      | XI a' ->
        (match b with
         | XI b' ->
           (match compare a' b' with
            | Eq -> (a, (XH, XH))
            | Lt ->
              let (g, p) = ggcdn n0 (sub b' a') a in
              let (ba, aa) = p in (g, (aa, (add aa (XO ba))))
            | Gt ->
              let (g, p) = ggcdn n0 (sub a' b') b in
              let (ab, bb) = p in (g, ((add bb (XO ab)), bb)))
         | XO b0 -> let (g, p) = ggcdn n0 a b0 in let (aa, bb) = p in (g, (aa, (XO bb)))
         | XH -> (XH, (a, XH)))
      | XO a0 ->
        (match b with
         | XI _ -> let (g, p) = ggcdn n0 a0 b in let (aa, bb) = p in (g, ((XO aa), bb))
         | XO b0 -> let (g, p) = ggcdn n0 a0 b0 in ((XO g), p)
         | XH -> (XH, (a, XH)))
      | XH -> (XH, (XH, b)))
      n

  (** val ggcd : positive -> positive -> positive * (positive * positive) **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Stdlib.Int.succ 0)

  (** val of_nat : int -> positive **)

  let rec of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> XH)
        (fun _ -> succ (of_nat x))
        x)
      n

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x -> succ (of_succ_nat x))
      n
 end

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> default
              | x :: _ -> x)
    (fun m -> match l with
              | [] -> default
              | _ :: t -> nth m t default)
    n

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun len0 -> start :: (seq (Stdlib.Int.succ start) len0))
    len

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Coq_Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' -> (match y with
                  | Zneg y' -> compOpp (Coq_Pos.compare x' y')
                  | _ -> Lt)

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val min : z -> z -> z **)

  let min n m =
    match compare n m with
    | Gt -> m
    | _ -> n

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val to_nat : z -> int **)

  let to_nat = function
  | Zpos p -> Coq_Pos.to_nat p
  | _ -> 0

  (** val of_nat : int -> z **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Z0)
      (fun n0 -> Zpos (Coq_Pos.of_succ_nat n0))
      n

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val pos_div_eucl : positive -> z -> z * z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q0), r')
      else ((add (mul (Zpos (XO XH)) q0) (Zpos XH)), (sub r' b))
    | XO a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q0), r')
      else ((add (mul (Zpos (XO XH)) q0) (Zpos XH)), (sub r' b))
    | XH -> if leb (Zpos (XO XH)) b then (Z0, (Zpos XH)) else ((Zpos XH), Z0)

  (** val div_eucl : z -> z -> z * z **)

  let div_eucl a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let (q0, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> ((opp q0), Z0)
          | _ -> ((opp (add q0 (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ ->
         let (q0, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> ((opp q0), Z0)
          | _ -> ((opp (add q0 (Zpos XH))), (sub b r)))
       | Zneg b' -> let (q0, r) = pos_div_eucl a' (Zpos b') in (q0, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let (q0, _) = div_eucl a b in q0

  (** val ggcd : z -> z -> z * (z * z) **)

  let ggcd a b =
    match a with
    | Z0 -> ((abs b), (Z0, (sgn b)))
    | Zpos a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zpos aa), (Zneg bb))))
    | Zneg a0 ->
      (match b with
       | Z0 -> ((abs a), ((sgn a), Z0))
       | Zpos b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zpos bb)))
       | Zneg b0 ->
         let (g, p) = Coq_Pos.ggcd a0 b0 in
         let (aa, bb) = p in ((Zpos g), ((Zneg aa), (Zneg bb))))
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

module RbaseSymbolsImpl =
 struct
  type coq_R = float

  (** val coq_Rabst : cReal -> dReal **)

  let coq_Rabst = __

  (** val coq_Rrepr : dReal -> cReal **)

  let coq_Rrepr = __

  (** val coq_Rquot1 : __ **)

  let coq_Rquot1 =
    __

  (** val coq_Rquot2 : __ **)

  let coq_Rquot2 =
    __

  (** val coq_R0 : coq_R **)

  let coq_R0 = 0.0

  (** val coq_R1 : coq_R **)

  let coq_R1 = 1.0

  (** val coq_Rplus : coq_R -> coq_R -> coq_R **)

  let coq_Rplus = (+.)

  (** val coq_Rmult : coq_R -> coq_R -> coq_R **)

  let coq_Rmult = ( *. )

  (** val coq_Ropp : coq_R -> coq_R **)

  let coq_Ropp = fun a -> (0.0 -. a)

  type coq_Rlt = __

  (** val coq_R0_def : __ **)

  let coq_R0_def =
    __

  (** val coq_R1_def : __ **)

  let coq_R1_def =
    __

  (** val coq_Rplus_def : __ **)

  let coq_Rplus_def =
    __

  (** val coq_Rmult_def : __ **)

  let coq_Rmult_def =
    __

  (** val coq_Ropp_def : __ **)

  let coq_Ropp_def =
    __

  (** val coq_Rlt_def : __ **)

  let coq_Rlt_def =
    __
 end

(** val iPR_2 : positive -> RbaseSymbolsImpl.coq_R **)

let rec iPR_2 = function
| XI p0 ->
  RbaseSymbolsImpl.coq_Rmult
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1)
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 (iPR_2 p0))
| XO p0 ->
  RbaseSymbolsImpl.coq_Rmult
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1) (iPR_2 p0)
| XH -> RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1

(** val iPR : positive -> RbaseSymbolsImpl.coq_R **)

let iPR = function
| XI p0 -> RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 (iPR_2 p0)
| XO p0 -> iPR_2 p0
| XH -> RbaseSymbolsImpl.coq_R1

(** val iZR : z -> RbaseSymbolsImpl.coq_R **)

let iZR = function
| Z0 -> RbaseSymbolsImpl.coq_R0
| Zpos n -> iPR n
| Zneg n -> RbaseSymbolsImpl.coq_Ropp (iPR n)

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl =
 struct
  (** val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Rinv = fun a -> (1.0 /. a)

  (** val coq_Rinv_def : __ **)

  let coq_Rinv_def =
    __
 end

(** val rdiv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let rdiv r1 r2 =
  RbaseSymbolsImpl.coq_Rmult r1 (RinvImpl.coq_Rinv r2)

(** val cos : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let cos = Float.cos

(** val sin : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let sin = Float.sin

(** val pI : RbaseSymbolsImpl.coq_R **)

let pI = Float.pi

type 'tA dec = 'tA -> 'tA -> bool
  (* singleton inductive, whose constructor was Build_Dec *)

(** val dec0 : 'a1 dec -> 'a1 -> 'a1 -> bool **)

let dec0 dec1 =
  dec1

(** val nat_lt_Dec : int dec **)

let nat_lt_Dec =
  (<)

module NormedOrderedFieldElementTypeR =
 struct
  type tA = RbaseSymbolsImpl.coq_R

  (** val coq_Azero : tA **)

  let coq_Azero =
    iZR Z0

  (** val coq_Aadd :
      RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Aadd =
    RbaseSymbolsImpl.coq_Rplus

  (** val coq_Amul :
      RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Amul =
    RbaseSymbolsImpl.coq_Rmult
 end

type fin = int
  (* singleton inductive, whose constructor was Fin *)

(** val fin2nat : int -> fin -> int **)

let fin2nat _ f =
  f

(** val nat2finS : int -> int -> fin **)

let nat2finS n i =
  let s = dec0 nat_lt_Dec i (Stdlib.Int.succ n) in if s then i else 0

(** val nat2fin : int -> int -> fin **)

let nat2fin _ i =
  i

(** val finseq : int -> fin list **)

let finseq n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n0 -> map (nat2finS n0) (seq 0 n))
    n

(** val seqsumAux : ('a1 -> 'a1 -> 'a1) -> int -> (int -> 'a1) -> 'a1 -> 'a1 **)

let rec seqsumAux aadd n f acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> acc)
    (fun n' -> seqsumAux aadd n' f (aadd (f n') acc))
    n

(** val seqsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> (int -> 'a1) -> 'a1 **)

let seqsum aadd azero n f =
  seqsumAux aadd n f azero

type 'tA vec = fin -> 'tA

(** val vrepeat : int -> 'a1 -> 'a1 vec **)

let vrepeat _ a _ =
  a

(** val vzero : 'a1 -> int -> 'a1 vec **)

let vzero azero n =
  vrepeat n azero

(** val v2f : 'a1 -> int -> 'a1 vec -> int -> 'a1 **)

let v2f azero n a i =
  if dec0 nat_lt_Dec i n then a (nat2fin n i) else azero

(** val l2v : 'a1 -> int -> 'a1 list -> 'a1 vec **)

let l2v azero n l i =
  nth (fin2nat n i) l azero

(** val v2l : int -> 'a1 vec -> 'a1 list **)

let v2l n a =
  map a (finseq n)

(** val vmap2 : ('a1 -> 'a2 -> 'a3) -> int -> 'a1 vec -> 'a2 vec -> 'a3 vec **)

let vmap2 f _ a b i =
  f (a i) (b i)

(** val vsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1 vec -> 'a1 **)

let vsum aadd azero n a =
  seqsum aadd azero n (v2f azero n a)

(** val vadd : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec -> 'a1 vec **)

let vadd =
  vmap2

(** val vdot :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec -> 'a1 **)

let vdot aadd azero amul n a b =
  vsum aadd azero n (vmap2 amul n a b)

(** val l2m : 'a1 -> int -> int -> 'a1 list list -> 'a1 vec vec **)

let l2m azero r c d =
  l2v (vzero azero c) r (map (l2v azero c) d)

(** val mmulv :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 vec vec -> 'a1
    vec -> 'a1 vec **)

let mmulv aadd azero amul _ c m a i =
  vdot aadd azero amul c (m i) a

(** val v2l0 :
    int -> NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA list **)

let v2l0 =
  v2l

(** val l2v0 :
    int -> NormedOrderedFieldElementTypeR.tA list -> NormedOrderedFieldElementTypeR.tA vec **)

let l2v0 n l =
  l2v NormedOrderedFieldElementTypeR.coq_Azero n l

(** val l2m0 :
    int -> int -> NormedOrderedFieldElementTypeR.tA list list ->
    NormedOrderedFieldElementTypeR.tA vec vec **)

let l2m0 r c dl =
  l2m NormedOrderedFieldElementTypeR.coq_Azero r c dl

(** val vadd0 :
    int -> NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let vadd0 n a b =
  vadd NormedOrderedFieldElementTypeR.coq_Aadd n a b

(** val mmulv0 :
    int -> int -> NormedOrderedFieldElementTypeR.tA vec vec ->
    NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA vec **)

let mmulv0 r c m a =
  mmulv NormedOrderedFieldElementTypeR.coq_Aadd NormedOrderedFieldElementTypeR.coq_Azero
    NormedOrderedFieldElementTypeR.coq_Amul r c m a

(** val deg2rad : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let deg2rad d =
  rdiv (RbaseSymbolsImpl.coq_Rmult d pI) (iZR (Zpos (XO (XO (XI (XO (XI (XI (XO XH)))))))))

(** val rz : RbaseSymbolsImpl.coq_R -> NormedOrderedFieldElementTypeR.tA vec vec **)

let rz _UU03b8_ =
  l2m0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))
    (((cos _UU03b8_) :: ((RbaseSymbolsImpl.coq_Ropp (sin _UU03b8_)) :: ((iZR Z0) :: []))) :: ((
    (sin _UU03b8_) :: ((cos _UU03b8_) :: ((iZR Z0) :: []))) :: (((iZR Z0) :: ((iZR Z0) :: (
    (iZR (Zpos XH)) :: []))) :: [])))

type frame = int

type point =
  NormedOrderedFieldElementTypeR.tA vec
  (* singleton inductive, whose constructor was mkPoint *)

(** val pointVec : frame -> point -> NormedOrderedFieldElementTypeR.tA vec **)

let pointVec _ p =
  p

type orien =
  NormedOrderedFieldElementTypeR.tA vec vec
  (* singleton inductive, whose constructor was mkOrien *)

(** val orienMat : frame -> frame -> orien -> NormedOrderedFieldElementTypeR.tA vec vec **)

let orienMat _ _ o =
  o

type pose = { poseOrien : orien; poseOffset : point }

(** val trans : frame -> frame -> pose -> point -> point **)

let trans a b poseB2A0 pB0 =
  vadd0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
    (mmulv0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ 0))) (orienMat a b poseB2A0.poseOrien)
      (pointVec b pB0)) (pointVec a poseB2A0.poseOffset)

module Coq_ex_3_1 =
 struct
  (** val offsetB2A : frame -> point **)

  let offsetB2A _ =
    l2v0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
      ((iZR (Zpos (XO (XI (XO XH))))) :: ((iZR (Zpos (XI (XO XH)))) :: ((iZR Z0) :: [])))

  (** val orienB2A : frame -> frame -> orien **)

  let orienB2A _ _ =
    rz (deg2rad (iZR (Zpos (XO (XI (XI (XI XH)))))))

  (** val poseB2A : frame -> frame -> pose **)

  let poseB2A a b =
    { poseOrien = (orienB2A a b); poseOffset = (offsetB2A a) }

  (** val pB : frame -> point **)

  let pB _ =
    l2v0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
      ((iZR (Zpos (XI XH))) :: ((iZR (Zpos (XI (XI XH)))) :: ((iZR Z0) :: [])))

  (** val pA : frame -> frame -> point **)

  let pA a b =
    trans a b (poseB2A a b) (pB b)

  (** val pA_value : RbaseSymbolsImpl.coq_R list **)

  let pA_value =
    v2l0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (pointVec 0 (pA 0 0))
 end
