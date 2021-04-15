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

let base_value (n : 'a nst) : 'a =
  match n with
  | Lf a -> a
  | Nd (a,_) -> a

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

let rec canopy_with_guide
    (n : 'a nst) (g : 'b tr)
    (d : 'a nst lazy_tr_deriv) : 'a nst tr =
  match (n, g) with
  | (_ , Lf _) -> plug_idt_deriv (Lazy.force d) n
  | (Nd (_, nsh), Nd (_, gsh))  ->
    let ntt = match_tr_with_deriv nsh gsh
        ~f:(canopy_with_guide) in
    idt_join ntt
  | _ -> raise (ShapeError "Mismatch in canopy_with_guide")

let rec excise_with
    (n : 'a nst) (g : 'b tr)
    (d : 'a nst lazy_tr_deriv) : ('a nst * 'a nst tr) =
  match (n, g) with
  | (_, Lf _) ->
    let v = base_value n in
    let tc = total_canopy n d in
    (Lf v, plug_idt_deriv (Lazy.force d) (Nd (v,tc)))
  | (Nd (a, ash), Nd (_, gsh)) ->
    let (ash',jtr) = intertwine ash gsh excise_with in 
    (Nd (a,ash'), idt_join jtr)
  | _ -> raise (ShapeError "Mismatch in excise_with")
           
let rec compress_with
    (n : 'a nst) (gsh : 'b tr_shell)
    (d : 'a nst lazy_tr_deriv) : 'a nst =
  match gsh with
  | Lf _ -> n
  | Nd (Lf _, sh) ->
    let v = root_value sh in
    let n' = compress_with n v d in
    Nd (base_value n, plug_idt_deriv (Lazy.force d) n')
  | Nd (sk, sh) ->
    let cnp = canopy_with_guide n sk d in 
    let nsh = match_tr_with_deriv cnp sh ~f:compress_with in
    Nd (base_value n, nsh)
