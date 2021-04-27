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

(* Better syntax ... *)
let (~>) n = Base n
(* aiee ... used as function applicaton? *)
let (|>) t h = Adjoin (t,h)

type 'a cmplx_zipper =
  | BaseZip of 'a nst_zipper
  | AdjoinZip of 'a cmplx_zipper * 'a nst_zipper

let rec map_cmplx (c : 'a cmplx) ~f:(f : 'a -> 'b) : 'b cmplx =
  match c with
  | Base obs -> Base (map_nst obs ~f:f)
  | Adjoin (frm,cls) ->
    let frm' = map_cmplx frm ~f:f in
    let cls' = map_nst cls ~f:f in
    Adjoin (frm',cls')

let head_of (c : 'a cmplx) : 'a nst =
  match c with 
  | Base n -> n
  | Adjoin (_,n) -> n
    
let with_head (c : 'a cmplx) (n : 'a nst) : 'a cmplx =
  match c with
  | Base _ -> Base n
  | Adjoin (frm,_) -> Adjoin (frm,n)

let rec mk_cmplx_zipper (c : 'a cmplx) : 'a cmplx_zipper =
  match c with
  | Base n -> BaseZip (mk_zipper n)
  | Adjoin (frm,n) ->
    AdjoinZip (mk_cmplx_zipper frm, mk_zipper n) 
           
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

(*****************************************************************************)
(*                         Complex Zipper Operations                         *)
(*****************************************************************************)

exception CmplxZipperError of string

let head_zip (z : 'a cmplx_zipper) : 'a nst_zipper =
  match z with
  | BaseZip nz -> nz
  | AdjoinZip (_,nz) -> nz

let tail_zip (z : 'a cmplx_zipper) : 'a cmplx_zipper =
  match z with
  | BaseZip _ -> raise (ShapeError "tail zip on base")
  | AdjoinZip (tl,_) -> tl
    
let focus_of (z : 'a cmplx_zipper) : 'a nst =
  match z with
  | BaseZip ((n,_)) -> n 
  | AdjoinZip (_,(n,_)) -> n

let with_head_zip (z : 'a cmplx_zipper) (n : 'a nst_zipper) : 'a cmplx_zipper =
  match z with 
  | BaseZip _ -> BaseZip n
  | AdjoinZip (fz,_) -> AdjoinZip (fz,n)
  
let with_focus (z : 'a cmplx_zipper) (n : 'a nst) : 'a cmplx_zipper =
  match z with
  | BaseZip ((_,g)) -> BaseZip ((n,g))
  | AdjoinZip (fz,(_,g)) -> AdjoinZip (fz,(n,g))
                              
let rec focus_deriv : 'a 'b. 'a cmplx_zipper -> 'b tr_deriv =
  function 
  (* FIXME: What is the derivative of an object? *)
  | BaseZip ((_,_)) -> deriv_of_sh (Lf ())
  | AdjoinZip (fz,(n,_)) ->
    begin match n with
    | Lf _ -> deriv_of_sh (focus_canopy fz)
    | Nd (_,sh) ->
      let sp = shell_spine sh in
      let fcs = focus_of fz in
      let cnp = canopy_with_guide fcs sp
          (lazy (focus_deriv fz)) in
      deriv_of_sh cnp 
    end

and focus_canopy (z : 'a cmplx_zipper) : 'a nst tr =
  match focus_of z with
  | Lf _ -> raise (CmplxZipperError "Leaf in focus_canopy")
  | Nd (_,sh) -> sh 

let focus_spine (z : 'a cmplx_zipper) : 'a tr =
  match focus_of z with
  | Lf a -> plug_idt_deriv (focus_deriv z) a
  | Nd (_,ash) -> shell_spine ash 

(* yikes, might need to debug this .... *)
let rec extract : 'a 'b. 'a cmplx_zipper -> 'b tr -> 'a cmplx =
  fun z g ->
  match z with
  | BaseZip ((n,_)) ->
    let (n',_) = excise_with n g (lazy (deriv_of_sh (Lf ())))
    in Base n'
  | AdjoinZip (fz,(n,_)) ->
    let (excsd,bxtr) = excise_with n g (lazy (focus_deriv z)) in
    let (_,cmprsr) = split_with bxtr
        (function
          | Lf a -> (a , Lf ())
          | Nd (a,ash) -> (a, ash)) in 
    let g' = idt_join cmprsr in
    let frm = extract fz g' in
    let hd' = compress_with (head_of frm) cmprsr
        (lazy (focus_deriv (mk_cmplx_zipper frm))) in

    Adjoin (with_head frm hd',excsd)
    
let focus_face (z : 'a cmplx_zipper) : 'a cmplx =
  match z with
  | BaseZip ((n,_)) -> Base (Nd (base_value n, Lf ()))
  | AdjoinZip (fz,(n,_)) ->
    let sp = focus_spine z in
    let d = focus_deriv z in
    let frm = extract fz sp in
    let hd' = compress_with (head_of frm)
        (plug_idt_deriv d sp)
        (lazy (focus_deriv (mk_cmplx_zipper frm))) in
    
    Adjoin (with_head frm hd', Lf (base_value n))

let rec close_cmplx (z : 'a cmplx_zipper) : 'a cmplx =
  match z with
  | BaseZip nz ->
    Base (close nz)
  | AdjoinZip (fz,nz) ->
    Adjoin (close_cmplx fz, close nz)

let rec visit_cmplx (z : 'a cmplx_zipper) (dir : dir) : 'a cmplx_zipper =
  match (z, dir) with
  | (BaseZip nz,_) -> BaseZip (visit nz dir)
  | (AdjoinZip (fz, nz), Dir []) ->
    (* We are entering a box at the root.  The lower
       dimensions will not change, so just visit in 
       the head zipper and return.
    *)
    AdjoinZip (fz, visit nz dir)
  | (_, Dir (d::ds)) ->
    
    let zp = visit_cmplx z (Dir ds) in
    let sib = sibling (head_zip zp) d in
    let sp = focus_spine zp in
    begin match sp with
      | Lf _ -> with_head_zip zp sib
      | Nd (_,sh) ->
        let exts = extents sh in
        let addr = element_at exts (addr_of d) in
        let ntl = seek_cmplx (tail_zip zp) addr in
        AdjoinZip (ntl,sib)
    end
  
and seek_cmplx (z : 'a cmplx_zipper) (addr : addr) : 'a cmplx_zipper =
  match addr with
  | [] -> z
  | (d::ds) ->
    visit_cmplx (seek_cmplx z ds) d 

(*****************************************************************************)
(*                             Complex Validation                            *)
(*****************************************************************************)

let validate (c : 'a cmplx) : unit =

  let rec validate_obj_nst (n : 'a nst) : unit =
    match n with
    | Lf _ -> ()
    | Nd (_,Nd (br,Lf ())) ->
      validate_obj_nst br
    | _ -> raise (ShapeError "Invalid object nesting") in 
             
  let rec validate_local (c : 'a cmplx) : 'a tr * 'a tr_deriv = 
    match c with
    | Base n ->
      validate_obj_nst n;
      (as_tr n, mk_deriv (Nd (Lf (), Lf ())))
    | Adjoin (tl,hd) ->
      let (t,d) = validate_local tl in
      let sp = spine hd (lazy d) in
      match_shape t sp; 
      (as_tr hd, deriv_of_sh sp)
      
  in match c with
  | Base (Lf _) -> ()
  | Adjoin (f, Lf _) ->
    let _ = validate_local f in ()
  | _ -> raise (ShapeError "Opetopic complex is not closed")
    





