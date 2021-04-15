(*****************************************************************************)
(*                                                                           *)
(*                      complex.ml - opetopic complexes                      *)
(*                                                                           *)
(*****************************************************************************)

open Idt
open Base
    
type 'a cmplx =
  | Base of 'a nst
  | Adjoin of 'a cmplx * 'a nst 

type 'a cmplx_zipper =
  | BaseZ of 'a nst_zipper
  | AdjoinZ of 'a cmplx_zipper * 'a nst_zipper

let rec map_cmplx (c : 'a cmplx) ~f:(f : 'a -> 'b) : 'b cmplx =
  match c with
  | Base obs -> Base (map_nst obs ~f:f)
  | Adjoin (frm,cls) ->
    let frm' = map_cmplx frm ~f:f in
    let cls' = map_nst cls ~f:f in
    Adjoin (frm',cls')

(*****************************************************************************)
(*                             Nesting Operations                            *)
(*****************************************************************************)

let rec spine (n : 'a nst) (d : 'a lazy_tr_deriv) : 'a tr =
  match n with
  | Lf a -> plug_idt_deriv (Lazy.force d) a
  | Nd (_,ash) -> shell_spine ash

and shell_spine (sh : 'a nst tr) : 'a tr =
  idt_join (map_tr_with_deriv sh ~f:(spine))

let rec total_canopy (n : 'a nst) (d : 'a nst lazy_tr_deriv) : 'a nst tr =
  match n with
  | Lf a -> plug_idt_deriv (Lazy.force d) (Lf a)
  | Nd (_,ash) ->
    idt_join (map_tr_with_deriv ash ~f:total_canopy)

(* let rec canopy_with_guide : 'b tree -> 'a nesting ldm -> 'a nesting -> 'a canopy m =
 *   fun g ldm n ->
 *   match (n, g) with
 *     (_, Lf) -> Lazy.force ldm >>= fun d -> return (plug_tree_deriv d n)
 *   | (Box (_, cn), Nd (_, sh)) ->
 *     let f nn gg _ dd = canopy_with_guide gg (lazy (return (Lazy.force dd))) nn
 *     in TM.lazy_match f cn sh >>= T.tree_join
 *   | _ -> throw "Bad canopy" *)

(* let rec excise_with : 'b tree -> 'a nesting ldm -> 'a nesting -> ('a nesting * 'a canopy) m =
 *   fun g ldm n ->
 *   match (n, g) with
 *     (_, Lf) -> let v = base_value n
 *     in total_canopy ldm n >>= fun cn ->
 *     Lazy.force ldm >>= fun d -> 
 *     return (Dot v, plug_tree_deriv d (Box (v, cn)))
 *   | (Box (a, cn), Nd (_, sh)) ->
 *     let f nn tt _ dd = excise_with tt (lazy (return (Lazy.force dd))) nn
 *     in TM.lazy_match f cn sh >>= fun p ->
 *     let (ncn, toJn) = T.tree_unzip p
 *     in T.tree_join toJn >>= fun jn ->
 *     return (Box (a, ncn), jn)
 *   | _ -> throw "Error during excision" *)

(* let rec compress_with : 'b tree_shell -> 'a nesting ldm -> 'a nesting -> 'a nesting m =
 *   fun s ldm n ->
 *   match s with
 *     Nd (Lf, sh) -> T.root_value sh >>= fun r ->
 *     compress_with r ldm n >>= fun nn ->
 *     Lazy.force ldm >>= fun d -> 
 *     return (Box (base_value n, plug_tree_deriv d nn))
 *   | Nd (sk, sh) -> canopy_with_guide sk ldm n >>= fun cn ->
 *     let f nn gg _ dd = compress_with gg (lazy (return (Lazy.force dd))) nn
 *     in TM.lazy_match f cn sh >>= fun rn ->
 *     return (Box (base_value n, rn))
 *   | Lf -> return n *)


