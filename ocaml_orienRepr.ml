
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



(** val pred : int -> int **)

let pred = fun n -> Stdlib.max 0 (n-1)

module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add = (+)
end
include Coq__1

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Int.succ (add p m))
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
      (fun _ -> Int.succ 0)
      (fun m0 -> mul n (pow n m0))
      m
 end

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
    | XO p ->
      (match y with
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
    | XH ->
      (match y with
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
  | XI p0 -> Int.succ (size_nat p0)
  | XO p0 -> Int.succ (size_nat p0)
  | XH -> Int.succ 0

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

  (** val ggcdn :
      int -> positive -> positive -> positive * (positive * positive) **)

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
         | XO b0 ->
           let (g, p) = ggcdn n0 a b0 in
           let (aa, bb) = p in (g, (aa, (XO bb)))
         | XH -> (XH, (a, XH)))
      | XO a0 ->
        (match b with
         | XI _ ->
           let (g, p) = ggcdn n0 a0 b in
           let (aa, bb) = p in (g, ((XO aa), bb))
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
    iter_op Coq__1.add x (Int.succ 0)

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
    (fun len0 -> start :: (seq (Int.succ start) len0))
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
    | Zneg x' ->
      (match y with
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

(** val rminus :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let rminus = (-.)

(** val iPR_2 : positive -> RbaseSymbolsImpl.coq_R **)

let rec iPR_2 = function
| XI p0 ->
  RbaseSymbolsImpl.coq_Rmult
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1
      RbaseSymbolsImpl.coq_R1)
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 (iPR_2 p0))
| XO p0 ->
  RbaseSymbolsImpl.coq_Rmult
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1
      RbaseSymbolsImpl.coq_R1) (iPR_2 p0)
| XH ->
  RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1

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

(** val total_order_T :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool option **)

let total_order_T = fun r1 r2 ->
  let c = Float.compare r1 r2 in
  if c < 0 then Some true
  else (if c = 0 then None else Some false)

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

(** val rdiv :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let rdiv r1 r2 =
  RbaseSymbolsImpl.coq_Rmult r1 (RinvImpl.coq_Rinv r2)

(** val pow0 : RbaseSymbolsImpl.coq_R -> int -> RbaseSymbolsImpl.coq_R **)

let rec pow0 r n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> iZR (Zpos XH))
    (fun n0 -> RbaseSymbolsImpl.coq_Rmult r (pow0 r n0))
    n

(** val rlt_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let rlt_dec r1 r2 =
  let s = total_order_T r1 r2 in (match s with
                                  | Some s0 -> s0
                                  | None -> false)

(** val rle_dec : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let rle_dec r1 r2 =
  let s = rlt_dec r2 r1 in if s then false else true

(** val rlt_le_dec :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let rlt_le_dec =
  rlt_dec

(** val rle_lt_dec :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let rle_lt_dec =
  rle_dec

(** val rsqr : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let rsqr r =
  RbaseSymbolsImpl.coq_Rmult r r

(** val cos : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let cos = Float.cos

(** val sin : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let sin = Float.sin

(** val pI : RbaseSymbolsImpl.coq_R **)

let pI = Float.pi

(** val sqrt : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let sqrt = Float.sqrt

(** val atan : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let atan = Float.atan

(** val asin : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let asin x =
  if rle_dec x (iZR (Zneg XH))
  then RbaseSymbolsImpl.coq_Ropp (rdiv pI (iZR (Zpos (XO XH))))
  else if rle_dec (iZR (Zpos XH)) x
       then rdiv pI (iZR (Zpos (XO XH)))
       else atan (rdiv x (sqrt (rminus (iZR (Zpos XH)) (rsqr x))))

(** val acos : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let acos = Float.acos

type 'tA dec =
  'tA -> 'tA -> bool
  (* singleton inductive, whose constructor was Build_Dec *)

(** val dec0 : 'a1 dec -> 'a1 -> 'a1 -> bool **)

let dec0 dec1 =
  dec1

(** val nat_eq_Dec : int dec **)

let nat_eq_Dec =
  (=)

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
      RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R ->
      RbaseSymbolsImpl.coq_R **)

  let coq_Aadd =
    RbaseSymbolsImpl.coq_Rplus

  (** val coq_Aone : tA **)

  let coq_Aone =
    iZR (Zpos XH)

  (** val coq_Aopp : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Aopp =
    RbaseSymbolsImpl.coq_Ropp

  (** val coq_Amul :
      RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R ->
      RbaseSymbolsImpl.coq_R **)

  let coq_Amul =
    RbaseSymbolsImpl.coq_Rmult
 end

(** val rleb : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let rleb r1 r2 =
  if rle_lt_dec r1 r2 then true else false

(** val rltb : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> bool **)

let rltb r1 r2 =
  if rlt_le_dec r1 r2 then true else false

(** val atan2 :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let atan2 y x =
  if rltb (iZR Z0) x
  then atan (rdiv y x)
  else if rltb x (iZR Z0)
       then if rleb (iZR Z0) y
            then RbaseSymbolsImpl.coq_Rplus (atan (rdiv y x)) pI
            else rminus (atan (rdiv y x)) pI
       else if rleb (iZR Z0) y
            then rdiv pI (iZR (Zpos (XO XH)))
            else rdiv (RbaseSymbolsImpl.coq_Ropp pI) (iZR (Zpos (XO XH)))

type fin = int
  (* singleton inductive, whose constructor was Fin *)

(** val fin2nat : int -> fin -> int **)

let fin2nat _ f =
  f

(** val nat2finS : int -> int -> fin **)

let nat2finS n i =
  let s = dec0 nat_lt_Dec i (Int.succ n) in if s then i else 0

(** val nat2fin : int -> int -> fin **)

let nat2fin _ i =
  i

(** val fSuccRange : int -> fin -> fin **)

let fSuccRange n i =
  nat2finS n (fin2nat n i)

(** val fPredRange : int -> fin -> fin **)

let fPredRange n i =
  nat2fin n (fin2nat (Int.succ n) i)

(** val fPredRangeP : int -> fin -> fin **)

let fPredRangeP n i =
  nat2fin n (pred (fin2nat (Int.succ n) i))

(** val fSuccRangeS : int -> fin -> fin **)

let fSuccRangeS n i =
  nat2fin (Int.succ n) (Int.succ (fin2nat n i))

(** val finseq : int -> fin list **)

let finseq n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n0 -> map (nat2finS n0) (seq 0 n))
    n

(** val seqsumAux :
    ('a1 -> 'a1 -> 'a1) -> int -> (int -> 'a1) -> 'a1 -> 'a1 **)

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

(** val mkvec3 : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 vec **)

let mkvec3 azero a1 a2 a3 =
  l2v azero (Int.succ (Int.succ (Int.succ 0))) (a1 :: (a2 :: (a3 :: [])))

(** val vmap : int -> ('a1 -> 'a2) -> 'a1 vec -> 'a2 vec **)

let vmap _ f a i =
  f (a i)

(** val vmap2 :
    int -> ('a1 -> 'a2 -> 'a3) -> 'a1 vec -> 'a2 vec -> 'a3 vec **)

let vmap2 _ f a b i =
  f (a i) (b i)

(** val vremoveH : int -> 'a1 vec -> 'a1 vec **)

let vremoveH n a i =
  a (fSuccRangeS n i)

(** val vremoveT : int -> 'a1 vec -> 'a1 vec **)

let vremoveT n a i =
  a (fSuccRange n i)

(** val vconsH : int -> 'a1 -> 'a1 vec -> 'a1 vec **)

let vconsH n x a i =
  let s = dec0 nat_eq_Dec (fin2nat (Int.succ n) i) 0 in
  if s then x else a (fPredRangeP n i)

(** val vconsT : int -> 'a1 vec -> 'a1 -> 'a1 vec **)

let vconsT n a x i =
  let s = dec0 nat_lt_Dec (fin2nat (Int.succ n) i) n in
  if s then a (fPredRange n i) else x

(** val vsum : ('a1 -> 'a1 -> 'a1) -> 'a1 -> int -> 'a1 vec -> 'a1 **)

let vsum aadd azero n a =
  seqsum aadd azero n (v2f azero n a)

(** val vadd : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec -> 'a1 vec **)

let vadd aadd n a b =
  vmap2 n aadd a b

(** val vopp : ('a1 -> 'a1) -> int -> 'a1 vec -> 'a1 vec **)

let vopp aopp n a =
  vmap n aopp a

(** val vscal : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 vec -> 'a1 vec **)

let vscal amul n x a =
  vmap n (amul x) a

(** val vdot :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> 'a1 vec ->
    'a1 vec -> 'a1 **)

let vdot aadd azero amul n a b =
  vsum aadd azero n (vmap2 n amul a b)

(** val m2l : int -> int -> 'a1 vec vec -> 'a1 list list **)

let m2l r c m =
  map (v2l c) (v2l r m)

(** val l2m : 'a1 -> int -> int -> 'a1 list list -> 'a1 vec vec **)

let l2m azero r c d =
  l2v (vzero azero c) r (map (l2v azero c) d)

(** val madd :
    ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 vec vec -> 'a1 vec vec -> 'a1
    vec vec **)

let madd aadd r c m n =
  vmap2 r (vmap2 c aadd) m n

(** val mat1 : 'a1 -> 'a1 -> int -> 'a1 vec vec **)

let mat1 azero aone n i j =
  if dec0 nat_eq_Dec (fin2nat n i) (fin2nat n j) then aone else azero

(** val mscal :
    ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1 -> 'a1 vec vec -> 'a1 vec vec **)

let mscal amul r c a m =
  vmap r (vmap c (amul a)) m

(** val mmul :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> int -> int ->
    'a1 vec vec -> 'a1 vec vec -> 'a1 vec vec **)

let mmul aadd azero amul _ c _ m n i j =
  vdot aadd azero amul c (m i) (fun k -> n k j)

(** val mmulv :
    ('a1 -> 'a1 -> 'a1) -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> int -> int -> 'a1
    vec vec -> 'a1 vec -> 'a1 vec **)

let mmulv aadd azero amul _ c m a i =
  vdot aadd azero amul c (m i) a

(** val v2l0 :
    int -> NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA list **)

let v2l0 =
  v2l

(** val l2v0 :
    int -> NormedOrderedFieldElementTypeR.tA list ->
    NormedOrderedFieldElementTypeR.tA vec **)

let l2v0 n l =
  l2v NormedOrderedFieldElementTypeR.coq_Azero n l

(** val mkvec0 :
    NormedOrderedFieldElementTypeR.tA -> NormedOrderedFieldElementTypeR.tA ->
    NormedOrderedFieldElementTypeR.tA -> NormedOrderedFieldElementTypeR.tA vec **)

let mkvec0 a1 a2 a3 =
  mkvec3 NormedOrderedFieldElementTypeR.coq_Azero a1 a2 a3

(** val vtail :
    int -> NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA **)

let vtail n a =
  a (nat2finS n n)

(** val vremoveH0 :
    int -> NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let vremoveH0 =
  vremoveH

(** val vremoveT0 :
    int -> NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let vremoveT0 =
  vremoveT

(** val vconsH0 :
    int -> NormedOrderedFieldElementTypeR.tA ->
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let vconsH0 =
  vconsH

(** val vconsT0 :
    int -> NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA -> NormedOrderedFieldElementTypeR.tA vec **)

let vconsT0 =
  vconsT

(** val l2m0 :
    int -> int -> NormedOrderedFieldElementTypeR.tA list list ->
    NormedOrderedFieldElementTypeR.tA vec vec **)

let l2m0 r c dl =
  l2m NormedOrderedFieldElementTypeR.coq_Azero r c dl

(** val m2l0 :
    int -> int -> NormedOrderedFieldElementTypeR.tA vec vec ->
    NormedOrderedFieldElementTypeR.tA list list **)

let m2l0 =
  m2l

(** val vadd0 :
    int -> NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let vadd0 n a b =
  vadd NormedOrderedFieldElementTypeR.coq_Aadd n a b

(** val madd0 :
    int -> int -> NormedOrderedFieldElementTypeR.tA vec vec ->
    NormedOrderedFieldElementTypeR.tA vec vec ->
    NormedOrderedFieldElementTypeR.tA vec vec **)

let madd0 r c m n =
  madd NormedOrderedFieldElementTypeR.coq_Aadd r c m n

(** val vopp0 :
    int -> NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let vopp0 n a =
  vopp NormedOrderedFieldElementTypeR.coq_Aopp n a

(** val vscal0 :
    int -> NormedOrderedFieldElementTypeR.tA ->
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let vscal0 n x a =
  vscal NormedOrderedFieldElementTypeR.coq_Amul n x a

(** val vdot0 :
    int -> NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec -> NormedOrderedFieldElementTypeR.tA **)

let vdot0 n a b =
  vdot NormedOrderedFieldElementTypeR.coq_Aadd
    NormedOrderedFieldElementTypeR.coq_Azero
    NormedOrderedFieldElementTypeR.coq_Amul n a b

(** val mat0 : int -> NormedOrderedFieldElementTypeR.tA vec vec **)

let mat0 n =
  mat1 NormedOrderedFieldElementTypeR.coq_Azero
    NormedOrderedFieldElementTypeR.coq_Aone n

(** val mscal0 :
    int -> int -> NormedOrderedFieldElementTypeR.tA ->
    NormedOrderedFieldElementTypeR.tA vec vec ->
    NormedOrderedFieldElementTypeR.tA vec vec **)

let mscal0 r c x m =
  mscal NormedOrderedFieldElementTypeR.coq_Amul r c x m

(** val mmul0 :
    int -> int -> int -> NormedOrderedFieldElementTypeR.tA vec vec ->
    NormedOrderedFieldElementTypeR.tA vec vec ->
    NormedOrderedFieldElementTypeR.tA vec vec **)

let mmul0 r c s m n =
  mmul NormedOrderedFieldElementTypeR.coq_Aadd
    NormedOrderedFieldElementTypeR.coq_Azero
    NormedOrderedFieldElementTypeR.coq_Amul r c s m n

(** val mmulv0 :
    int -> int -> NormedOrderedFieldElementTypeR.tA vec vec ->
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let mmulv0 r c m a =
  mmulv NormedOrderedFieldElementTypeR.coq_Aadd
    NormedOrderedFieldElementTypeR.coq_Azero
    NormedOrderedFieldElementTypeR.coq_Amul r c m a

(** val v3cross :
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let v3cross a b =
  mkvec0
    (rminus
      (RbaseSymbolsImpl.coq_Rmult
        (a (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0)))
        (b (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0)))))
      (RbaseSymbolsImpl.coq_Rmult
        (a (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0))))
        (b (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0)))))
    (rminus
      (RbaseSymbolsImpl.coq_Rmult
        (a (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0))))
        (b (nat2finS (Int.succ (Int.succ 0)) 0)))
      (RbaseSymbolsImpl.coq_Rmult (a (nat2finS (Int.succ (Int.succ 0)) 0))
        (b (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0))))))
    (rminus
      (RbaseSymbolsImpl.coq_Rmult (a (nat2finS (Int.succ (Int.succ 0)) 0))
        (b (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0))))
      (RbaseSymbolsImpl.coq_Rmult
        (a (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0)))
        (b (nat2finS (Int.succ (Int.succ 0)) 0))))

(** val skew3 :
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec vec **)

let skew3 a =
  l2m0 (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ (Int.succ 0)))
    (((iZR Z0) :: ((RbaseSymbolsImpl.coq_Ropp
                     (a
                       (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ
                         0))))) :: ((a
                                      (nat2finS (Int.succ (Int.succ 0))
                                        (Int.succ 0))) :: []))) :: ((
    (a (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0)))) :: (
    (iZR Z0) :: ((RbaseSymbolsImpl.coq_Ropp
                   (a (nat2finS (Int.succ (Int.succ 0)) 0))) :: []))) :: ((
    (RbaseSymbolsImpl.coq_Ropp
      (a (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0)))) :: ((a
                                                                 (nat2finS
                                                                   (Int.succ
                                                                   (Int.succ
                                                                   0)) 0)) :: (
    (iZR Z0) :: []))) :: [])))

type axisAngle = { aaAxis : NormedOrderedFieldElementTypeR.tA vec;
                   aaAngle : RbaseSymbolsImpl.coq_R }

(** val v2aa : NormedOrderedFieldElementTypeR.tA vec -> axisAngle **)

let v2aa v =
  { aaAxis = (vremoveT0 (Int.succ (Int.succ (Int.succ 0))) v); aaAngle =
    (vtail (Int.succ (Int.succ (Int.succ 0))) v) }

(** val aa2v : axisAngle -> NormedOrderedFieldElementTypeR.tA vec **)

let aa2v aa =
  vconsT0 (Int.succ (Int.succ (Int.succ 0))) aa.aaAxis aa.aaAngle

(** val rotaa :
    axisAngle -> NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let rotaa aa a =
  let { aaAxis = n; aaAngle = _UU03b8_ } = aa in
  vadd0 (Int.succ (Int.succ (Int.succ 0)))
    (vadd0 (Int.succ (Int.succ (Int.succ 0)))
      (vscal0 (Int.succ (Int.succ (Int.succ 0))) (cos _UU03b8_)
        (vadd0 (Int.succ (Int.succ (Int.succ 0))) a
          (vopp0 (Int.succ (Int.succ (Int.succ 0)))
            (vscal0 (Int.succ (Int.succ (Int.succ 0)))
              (vdot0 (Int.succ (Int.succ (Int.succ 0))) a n) n))))
      (vscal0 (Int.succ (Int.succ (Int.succ 0))) (sin _UU03b8_) (v3cross n a)))
    (vscal0 (Int.succ (Int.succ (Int.succ 0)))
      (vdot0 (Int.succ (Int.succ (Int.succ 0))) a n) n)

(** val aa2mat : axisAngle -> NormedOrderedFieldElementTypeR.tA vec vec **)

let aa2mat aa =
  let { aaAxis = n; aaAngle = _UU03b8_ } = aa in
  let k = skew3 n in
  madd0 (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ (Int.succ 0)))
    (madd0 (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ (Int.succ
      0))) (mat0 (Int.succ (Int.succ (Int.succ 0))))
      (mscal0 (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ
        (Int.succ 0))) (sin _UU03b8_) k))
    (mscal0 (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ (Int.succ
      0))) (rminus (iZR (Zpos XH)) (cos _UU03b8_))
      (mmul0 (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ (Int.succ
        0))) (Int.succ (Int.succ (Int.succ 0))) k k))

(** val rx :
    RbaseSymbolsImpl.coq_R -> NormedOrderedFieldElementTypeR.tA vec vec **)

let rx _UU03b8_ =
  l2m0 (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ (Int.succ 0)))
    (((iZR (Zpos XH)) :: ((iZR Z0) :: ((iZR Z0) :: []))) :: (((iZR Z0) :: (
    (cos _UU03b8_) :: ((RbaseSymbolsImpl.coq_Ropp (sin _UU03b8_)) :: []))) :: ((
    (iZR Z0) :: ((sin _UU03b8_) :: ((cos _UU03b8_) :: []))) :: [])))

(** val ry :
    RbaseSymbolsImpl.coq_R -> NormedOrderedFieldElementTypeR.tA vec vec **)

let ry _UU03b8_ =
  l2m0 (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ (Int.succ 0)))
    (((cos _UU03b8_) :: ((iZR Z0) :: ((sin _UU03b8_) :: []))) :: (((iZR Z0) :: (
    (iZR (Zpos XH)) :: ((iZR Z0) :: []))) :: (((RbaseSymbolsImpl.coq_Ropp
                                                 (sin _UU03b8_)) :: (
    (iZR Z0) :: ((cos _UU03b8_) :: []))) :: [])))

(** val rz :
    RbaseSymbolsImpl.coq_R -> NormedOrderedFieldElementTypeR.tA vec vec **)

let rz _UU03b8_ =
  l2m0 (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ (Int.succ 0)))
    (((cos _UU03b8_) :: ((RbaseSymbolsImpl.coq_Ropp (sin _UU03b8_)) :: (
    (iZR Z0) :: []))) :: (((sin _UU03b8_) :: ((cos _UU03b8_) :: ((iZR Z0) :: []))) :: ((
    (iZR Z0) :: ((iZR Z0) :: ((iZR (Zpos XH)) :: []))) :: [])))

(** val s123 :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R ->
    RbaseSymbolsImpl.coq_R -> NormedOrderedFieldElementTypeR.tA vec vec **)

let s123 _UU03b8_1 _UU03b8_2 _UU03b8_3 =
  l2m0 (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ (Int.succ 0)))
    (((RbaseSymbolsImpl.coq_Rmult (cos _UU03b8_2) (cos _UU03b8_3)) :: (
    (rminus
      (RbaseSymbolsImpl.coq_Rmult
        (RbaseSymbolsImpl.coq_Rmult (sin _UU03b8_1) (sin _UU03b8_2))
        (cos _UU03b8_3))
      (RbaseSymbolsImpl.coq_Rmult (sin _UU03b8_3) (cos _UU03b8_1))) :: (
    (RbaseSymbolsImpl.coq_Rplus
      (RbaseSymbolsImpl.coq_Rmult
        (RbaseSymbolsImpl.coq_Rmult (cos _UU03b8_1) (sin _UU03b8_2))
        (cos _UU03b8_3))
      (RbaseSymbolsImpl.coq_Rmult (sin _UU03b8_3) (sin _UU03b8_1))) :: []))) :: ((
    (RbaseSymbolsImpl.coq_Rmult (cos _UU03b8_2) (sin _UU03b8_3)) :: (
    (RbaseSymbolsImpl.coq_Rplus
      (RbaseSymbolsImpl.coq_Rmult
        (RbaseSymbolsImpl.coq_Rmult (sin _UU03b8_1) (sin _UU03b8_2))
        (sin _UU03b8_3))
      (RbaseSymbolsImpl.coq_Rmult (cos _UU03b8_3) (cos _UU03b8_1))) :: (
    (rminus
      (RbaseSymbolsImpl.coq_Rmult
        (RbaseSymbolsImpl.coq_Rmult (cos _UU03b8_1) (sin _UU03b8_2))
        (sin _UU03b8_3))
      (RbaseSymbolsImpl.coq_Rmult (cos _UU03b8_3) (sin _UU03b8_1))) :: []))) :: ((
    (RbaseSymbolsImpl.coq_Ropp (sin _UU03b8_2)) :: ((RbaseSymbolsImpl.coq_Rmult
                                                      (sin _UU03b8_1)
                                                      (cos _UU03b8_2)) :: (
    (RbaseSymbolsImpl.coq_Rmult (cos _UU03b8_1) (cos _UU03b8_2)) :: []))) :: [])))

module R2Euler_S123 =
 struct
  module Coq_alg2 =
   struct
    (** val _UU03d5_' :
        NormedOrderedFieldElementTypeR.tA vec vec -> RbaseSymbolsImpl.coq_R **)

    let _UU03d5_' c =
      atan2
        (c (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0)))
          (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0)))
        (c (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0)))
          (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0))))

    (** val _UU03b8_' :
        NormedOrderedFieldElementTypeR.tA vec vec -> RbaseSymbolsImpl.coq_R **)

    let _UU03b8_' c =
      asin
        (RbaseSymbolsImpl.coq_Ropp
          (c (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0)))
            (nat2finS (Int.succ (Int.succ 0)) 0)))

    (** val _UU03c8_' :
        NormedOrderedFieldElementTypeR.tA vec vec -> RbaseSymbolsImpl.coq_R **)

    let _UU03c8_' c =
      atan2
        (c (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0))
          (nat2finS (Int.succ (Int.succ 0)) 0))
        (c (nat2finS (Int.succ (Int.succ 0)) 0)
          (nat2finS (Int.succ (Int.succ 0)) 0))
   end
 end

type quat = NormedOrderedFieldElementTypeR.tA vec

(** val si2q :
    RbaseSymbolsImpl.coq_R -> NormedOrderedFieldElementTypeR.tA vec -> quat **)

let si2q w v =
  vconsH0 (Int.succ (Int.succ (Int.succ 0))) w v

(** val q2im : quat -> NormedOrderedFieldElementTypeR.tA vec **)

let q2im q0 =
  vremoveH0 (Int.succ (Int.succ (Int.succ 0))) q0

(** val im2q : NormedOrderedFieldElementTypeR.tA vec -> quat **)

let im2q v =
  vconsH0 (Int.succ (Int.succ (Int.succ 0))) (iZR Z0) v

(** val qmul : quat -> quat -> quat **)

let qmul q1 q2 =
  l2v0 (Int.succ (Int.succ (Int.succ (Int.succ 0))))
    ((rminus
       (rminus
         (rminus
           (RbaseSymbolsImpl.coq_Rmult
             (q1 (nat2finS (Int.succ (Int.succ (Int.succ 0))) 0))
             (q2 (nat2finS (Int.succ (Int.succ (Int.succ 0))) 0)))
           (RbaseSymbolsImpl.coq_Rmult
             (q1 (nat2finS (Int.succ (Int.succ (Int.succ 0))) (Int.succ 0)))
             (q2 (nat2finS (Int.succ (Int.succ (Int.succ 0))) (Int.succ 0)))))
         (RbaseSymbolsImpl.coq_Rmult
           (q1
             (nat2finS (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ
               0))))
           (q2
             (nat2finS (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ
               0))))))
       (RbaseSymbolsImpl.coq_Rmult
         (q1
           (nat2finS (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ
             (Int.succ 0)))))
         (q2
           (nat2finS (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ
             (Int.succ 0))))))) :: ((rminus
                                      (RbaseSymbolsImpl.coq_Rplus
                                        (RbaseSymbolsImpl.coq_Rplus
                                          (RbaseSymbolsImpl.coq_Rmult
                                            (q1
                                              (nat2finS (Int.succ (Int.succ
                                                (Int.succ 0))) 0))
                                            (q2
                                              (nat2finS (Int.succ (Int.succ
                                                (Int.succ 0))) (Int.succ 0))))
                                          (RbaseSymbolsImpl.coq_Rmult
                                            (q1
                                              (nat2finS (Int.succ (Int.succ
                                                (Int.succ 0))) (Int.succ 0)))
                                            (q2
                                              (nat2finS (Int.succ (Int.succ
                                                (Int.succ 0))) 0))))
                                        (RbaseSymbolsImpl.coq_Rmult
                                          (q1
                                            (nat2finS (Int.succ (Int.succ
                                              (Int.succ 0))) (Int.succ
                                              (Int.succ 0))))
                                          (q2
                                            (nat2finS (Int.succ (Int.succ
                                              (Int.succ 0))) (Int.succ
                                              (Int.succ (Int.succ 0)))))))
                                      (RbaseSymbolsImpl.coq_Rmult
                                        (q1
                                          (nat2finS (Int.succ (Int.succ
                                            (Int.succ 0))) (Int.succ
                                            (Int.succ (Int.succ 0)))))
                                        (q2
                                          (nat2finS (Int.succ (Int.succ
                                            (Int.succ 0))) (Int.succ
                                            (Int.succ 0)))))) :: ((RbaseSymbolsImpl.coq_Rplus
                                                                    (RbaseSymbolsImpl.coq_Rplus
                                                                    (rminus
                                                                    (RbaseSymbolsImpl.coq_Rmult
                                                                    (q1
                                                                    (nat2finS
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    0))) 0))
                                                                    (q2
                                                                    (nat2finS
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    0)))
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    0)))))
                                                                    (RbaseSymbolsImpl.coq_Rmult
                                                                    (q1
                                                                    (nat2finS
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    0)))
                                                                    (Int.succ
                                                                    0)))
                                                                    (q2
                                                                    (nat2finS
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    0)))
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    0)))))))
                                                                    (RbaseSymbolsImpl.coq_Rmult
                                                                    (q1
                                                                    (nat2finS
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    0)))
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    0))))
                                                                    (q2
                                                                    (nat2finS
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    0))) 0))))
                                                                    (RbaseSymbolsImpl.coq_Rmult
                                                                    (q1
                                                                    (nat2finS
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    0)))
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    0)))))
                                                                    (q2
                                                                    (nat2finS
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    (Int.succ
                                                                    0)))
                                                                    (Int.succ
                                                                    0))))) :: (
    (RbaseSymbolsImpl.coq_Rplus
      (rminus
        (RbaseSymbolsImpl.coq_Rplus
          (RbaseSymbolsImpl.coq_Rmult
            (q1 (nat2finS (Int.succ (Int.succ (Int.succ 0))) 0))
            (q2
              (nat2finS (Int.succ (Int.succ (Int.succ 0))) (Int.succ
                (Int.succ (Int.succ 0))))))
          (RbaseSymbolsImpl.coq_Rmult
            (q1 (nat2finS (Int.succ (Int.succ (Int.succ 0))) (Int.succ 0)))
            (q2
              (nat2finS (Int.succ (Int.succ (Int.succ 0))) (Int.succ
                (Int.succ 0))))))
        (RbaseSymbolsImpl.coq_Rmult
          (q1
            (nat2finS (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ
              0))))
          (q2 (nat2finS (Int.succ (Int.succ (Int.succ 0))) (Int.succ 0)))))
      (RbaseSymbolsImpl.coq_Rmult
        (q1
          (nat2finS (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ
            (Int.succ 0)))))
        (q2 (nat2finS (Int.succ (Int.succ (Int.succ 0))) 0)))) :: []))))

(** val qconj : quat -> quat **)

let qconj q0 =
  si2q (q0 (nat2finS (Int.succ (Int.succ (Int.succ 0))) 0))
    (vopp0 (Int.succ (Int.succ (Int.succ 0))) (q2im q0))

(** val aa2quat : axisAngle -> quat **)

let aa2quat aa =
  let { aaAxis = n; aaAngle = _UU03b8_ } = aa in
  si2q (cos (rdiv _UU03b8_ (iZR (Zpos (XO XH)))))
    (vscal0 (Int.succ (Int.succ (Int.succ 0)))
      (sin (rdiv _UU03b8_ (iZR (Zpos (XO XH))))) n)

(** val quat2aa : quat -> axisAngle **)

let quat2aa q0 =
  let _UU03b8_ =
    RbaseSymbolsImpl.coq_Rmult (iZR (Zpos (XO XH)))
      (acos (q0 (nat2finS (Int.succ (Int.succ (Int.succ 0))) 0)))
  in
  let n =
    vscal0 (Int.succ (Int.succ (Int.succ 0)))
      (rdiv (iZR (Zpos XH))
        (sqrt
          (rminus (iZR (Zpos XH))
            (rsqr (q0 (nat2finS (Int.succ (Int.succ (Int.succ 0))) 0))))))
      (q2im q0)
  in
  { aaAxis = n; aaAngle = _UU03b8_ }

(** val qrot : quat -> quat -> quat **)

let qrot q0 v =
  qmul (qmul q0 v) (qconj q0)

(** val qrotv :
    quat -> NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let qrotv q0 v =
  q2im (qrot q0 (im2q v))

(** val q2m : quat -> NormedOrderedFieldElementTypeR.tA vec vec **)

let q2m q0 =
  let p = (((q0 (nat2finS (Int.succ (Int.succ (Int.succ 0))) 0)),
    (q0 (nat2finS (Int.succ (Int.succ (Int.succ 0))) (Int.succ 0)))),
    (q0 (nat2finS (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ 0)))))
  in
  let z0 =
    q0
      (nat2finS (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ
        (Int.succ 0))))
  in
  let (p0, y) = p in
  let (w, x) = p0 in
  l2m0 (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ (Int.succ 0)))
    (((rminus
        (rminus
          (RbaseSymbolsImpl.coq_Rplus (pow0 w (Int.succ (Int.succ 0)))
            (pow0 x (Int.succ (Int.succ 0))))
          (pow0 y (Int.succ (Int.succ 0)))) (pow0 z0 (Int.succ (Int.succ 0)))) :: (
    (rminus
      (RbaseSymbolsImpl.coq_Rmult
        (RbaseSymbolsImpl.coq_Rmult (iZR (Zpos (XO XH))) x) y)
      (RbaseSymbolsImpl.coq_Rmult
        (RbaseSymbolsImpl.coq_Rmult (iZR (Zpos (XO XH))) w) z0)) :: (
    (RbaseSymbolsImpl.coq_Rplus
      (RbaseSymbolsImpl.coq_Rmult
        (RbaseSymbolsImpl.coq_Rmult (iZR (Zpos (XO XH))) x) z0)
      (RbaseSymbolsImpl.coq_Rmult
        (RbaseSymbolsImpl.coq_Rmult (iZR (Zpos (XO XH))) w) y)) :: []))) :: ((
    (RbaseSymbolsImpl.coq_Rplus
      (RbaseSymbolsImpl.coq_Rmult
        (RbaseSymbolsImpl.coq_Rmult (iZR (Zpos (XO XH))) x) y)
      (RbaseSymbolsImpl.coq_Rmult
        (RbaseSymbolsImpl.coq_Rmult (iZR (Zpos (XO XH))) w) z0)) :: (
    (rminus
      (RbaseSymbolsImpl.coq_Rplus
        (rminus (pow0 w (Int.succ (Int.succ 0)))
          (pow0 x (Int.succ (Int.succ 0)))) (pow0 y (Int.succ (Int.succ 0))))
      (pow0 z0 (Int.succ (Int.succ 0)))) :: ((rminus
                                               (RbaseSymbolsImpl.coq_Rmult
                                                 (RbaseSymbolsImpl.coq_Rmult
                                                   (iZR (Zpos (XO XH))) y) z0)
                                               (RbaseSymbolsImpl.coq_Rmult
                                                 (RbaseSymbolsImpl.coq_Rmult
                                                   (iZR (Zpos (XO XH))) w) x)) :: []))) :: ((
    (rminus
      (RbaseSymbolsImpl.coq_Rmult
        (RbaseSymbolsImpl.coq_Rmult (iZR (Zpos (XO XH))) x) z0)
      (RbaseSymbolsImpl.coq_Rmult
        (RbaseSymbolsImpl.coq_Rmult (iZR (Zpos (XO XH))) w) y)) :: ((RbaseSymbolsImpl.coq_Rplus
                                                                    (RbaseSymbolsImpl.coq_Rmult
                                                                    (RbaseSymbolsImpl.coq_Rmult
                                                                    (iZR
                                                                    (Zpos (XO
                                                                    XH))) y)
                                                                    z0)
                                                                    (RbaseSymbolsImpl.coq_Rmult
                                                                    (RbaseSymbolsImpl.coq_Rmult
                                                                    (iZR
                                                                    (Zpos (XO
                                                                    XH))) w)
                                                                    x)) :: (
    (RbaseSymbolsImpl.coq_Rplus
      (rminus
        (rminus (pow0 w (Int.succ (Int.succ 0)))
          (pow0 x (Int.succ (Int.succ 0)))) (pow0 y (Int.succ (Int.succ 0))))
      (pow0 z0 (Int.succ (Int.succ 0)))) :: []))) :: [])))

(** val rsign : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let rsign r =
  if rleb (iZR Z0) r then iZR (Zpos XH) else iZR (Zneg XH)

(** val m2q : NormedOrderedFieldElementTypeR.tA vec vec -> quat **)

let m2q m =
  let sign0 = iZR (Zpos XH) in
  let sign1 =
    RbaseSymbolsImpl.coq_Rmult sign0
      (rsign
        (rminus
          (m (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0)))
            (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0)))
          (m (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0))
            (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0))))))
  in
  let sign2 =
    RbaseSymbolsImpl.coq_Rmult sign0
      (rsign
        (rminus
          (m (nat2finS (Int.succ (Int.succ 0)) 0)
            (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0))))
          (m (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0)))
            (nat2finS (Int.succ (Int.succ 0)) 0))))
  in
  let sign3 =
    RbaseSymbolsImpl.coq_Rmult sign0
      (rsign
        (rminus
          (m (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0))
            (nat2finS (Int.succ (Int.succ 0)) 0))
          (m (nat2finS (Int.succ (Int.succ 0)) 0)
            (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0)))))
  in
  l2v0 (Int.succ (Int.succ (Int.succ (Int.succ 0))))
    ((RbaseSymbolsImpl.coq_Rmult
       (RbaseSymbolsImpl.coq_Rmult sign0
         (rdiv (iZR (Zpos XH)) (iZR (Zpos (XO XH)))))
       (sqrt
         (RbaseSymbolsImpl.coq_Rplus
           (RbaseSymbolsImpl.coq_Rplus
             (RbaseSymbolsImpl.coq_Rplus (iZR (Zpos XH))
               (m (nat2finS (Int.succ (Int.succ 0)) 0)
                 (nat2finS (Int.succ (Int.succ 0)) 0)))
             (m (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0))
               (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0))))
           (m (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0)))
             (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0))))))) :: (
    (RbaseSymbolsImpl.coq_Rmult
      (RbaseSymbolsImpl.coq_Rmult sign1
        (rdiv (iZR (Zpos XH)) (iZR (Zpos (XO XH)))))
      (sqrt
        (rminus
          (rminus
            (RbaseSymbolsImpl.coq_Rplus (iZR (Zpos XH))
              (m (nat2finS (Int.succ (Int.succ 0)) 0)
                (nat2finS (Int.succ (Int.succ 0)) 0)))
            (m (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0))
              (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0))))
          (m (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0)))
            (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0))))))) :: (
    (RbaseSymbolsImpl.coq_Rmult
      (RbaseSymbolsImpl.coq_Rmult sign2
        (rdiv (iZR (Zpos XH)) (iZR (Zpos (XO XH)))))
      (sqrt
        (rminus
          (RbaseSymbolsImpl.coq_Rplus
            (rminus (iZR (Zpos XH))
              (m (nat2finS (Int.succ (Int.succ 0)) 0)
                (nat2finS (Int.succ (Int.succ 0)) 0)))
            (m (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0))
              (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0))))
          (m (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0)))
            (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0))))))) :: (
    (RbaseSymbolsImpl.coq_Rmult
      (RbaseSymbolsImpl.coq_Rmult sign3
        (rdiv (iZR (Zpos XH)) (iZR (Zpos (XO XH)))))
      (sqrt
        (RbaseSymbolsImpl.coq_Rplus
          (rminus
            (rminus (iZR (Zpos XH))
              (m (nat2finS (Int.succ (Int.succ 0)) 0)
                (nat2finS (Int.succ (Int.succ 0)) 0)))
            (m (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0))
              (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0))))
          (m (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0)))
            (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0))))))) :: []))))

(** val rotx :
    RbaseSymbolsImpl.coq_R -> NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let rotx ang v =
  mmulv0 (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ (Int.succ
    0))) (rx ang) v

(** val roty :
    RbaseSymbolsImpl.coq_R -> NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let roty ang v =
  mmulv0 (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ (Int.succ
    0))) (ry ang) v

(** val rotz :
    RbaseSymbolsImpl.coq_R -> NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let rotz ang v =
  mmulv0 (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ (Int.succ
    0))) (rz ang) v

(** val rotaa0 :
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let rotaa0 aa v =
  rotaa (v2aa aa) v

(** val rotByM :
    NormedOrderedFieldElementTypeR.tA vec vec ->
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let rotByM m v =
  mmulv0 (Int.succ (Int.succ (Int.succ 0))) (Int.succ (Int.succ (Int.succ
    0))) m v

(** val rotByQ :
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let rotByQ =
  qrotv

(** val rot2ByQ :
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let rot2ByQ q1 q2 v =
  qrotv (qmul q2 q1) v

(** val e2m :
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec vec **)

let e2m euler =
  s123 (euler (nat2finS (Int.succ (Int.succ 0)) 0))
    (euler (nat2finS (Int.succ (Int.succ 0)) (Int.succ 0)))
    (euler (nat2finS (Int.succ (Int.succ 0)) (Int.succ (Int.succ 0))))

(** val m2e :
    NormedOrderedFieldElementTypeR.tA vec vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let m2e m =
  l2v0 (Int.succ (Int.succ (Int.succ 0)))
    ((R2Euler_S123.Coq_alg2._UU03d5_' m) :: ((R2Euler_S123.Coq_alg2._UU03b8_'
                                               m) :: ((R2Euler_S123.Coq_alg2._UU03c8_'
                                                        m) :: [])))

(** val a2m :
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec vec **)

let a2m aa =
  aa2mat (v2aa aa)

(** val a2e :
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let a2e aa =
  m2e (a2m aa)

(** val q2e :
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let q2e q0 =
  m2e (q2m q0)

(** val e2q :
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let e2q e =
  m2q (e2m e)

(** val q2a :
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let q2a q0 =
  aa2v (quat2aa q0)

(** val a2q :
    NormedOrderedFieldElementTypeR.tA vec ->
    NormedOrderedFieldElementTypeR.tA vec **)

let a2q aa =
  aa2quat (v2aa aa)
