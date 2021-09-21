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

let rec dim_cmplx (c : 'a cmplx) : int =
  match c with
  | Base _ -> 0
  | Adjoin (c',_) -> dim_cmplx c' + 1

let is_base (c : 'a cmplx) : bool =
  match c with
  | Base _ -> true
  | _ -> false

let top_value (c : 'a cmplx) : 'a =
  match c with
  | Base n -> base_value n
  | Adjoin (_,n) -> base_value n
                      
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

let tail_of (c : 'a cmplx) : 'a cmplx =
  match c with
  | Base _ -> raise (ShapeError "tail of base complex")
  | Adjoin (c',_) -> c'
    
let with_head (c : 'a cmplx) (n : 'a nst) : 'a cmplx =
  match c with
  | Base _ -> Base n
  | Adjoin (frm,_) -> Adjoin (frm,n)

let rec labels (c : 'a cmplx) : 'a list =
  match c with
  | Base n -> nodes_nst n
  | Adjoin (tl,hd) ->
    List.append (labels tl) (nodes_nst hd) 

(* face addresses *)
type face_addr = int * addr
                 
let map_cmplx_with_addr (c : 'a cmplx)
    ~f:(f : 'a -> face_addr -> 'b) : 'b cmplx =

  let rec go c codim =
    let do_map n = map_nst_with_addr n
        ~f:(fun a addr -> f a (codim,addr)) in 
    match c with
    | Base n -> Base (do_map n)
    | Adjoin (c',n) ->
      Adjoin (go c' (codim+1), do_map n)

  in go c 0 

let rec match_cmplx (c : 'a cmplx) (d : 'b cmplx)
    ~f:(f : 'a -> 'b -> 'c) : 'c cmplx =
  match (c , d) with
  | (Base u, Base v) ->
    Base (match_nst u v ~f:f)
  | (Adjoin (s,u), Adjoin (t,v)) ->
    let tl = match_cmplx s t ~f:f in
    let hd = match_nst u v ~f:f in
    Adjoin (tl,hd) 
  | _ -> raise (ShapeError "match failed for complexes")

(*****************************************************************************)
(*                                 Equality                                  *)
(*****************************************************************************)

let rec cmplx_eq (eq : 'a -> 'a -> bool)
    (ca : 'a cmplx) (cb : 'a cmplx) : bool =
  match (ca,cb) with
  | (Base na , Base nb) -> nst_eq eq na nb
  | (Adjoin (ta,na) , Adjoin (tb,nb)) ->
    if (nst_eq eq na nb) then
      cmplx_eq eq ta tb
    else false
  | _ -> false 

(*****************************************************************************)
(*                             Complex Traversal                             *)
(*****************************************************************************)

module ComplexTraverse (A : Applicative.Basic) = struct

  module AI = Applicative.Make(A)
  module TT = TreeTraverse(A) 
  
  module AppSyntax = struct
    let (let+) x f = AI.map ~f:f x
    let (and+) p q = AI.both p q 
  end

  let rec traverse_cmplx (c : 'a cmplx) ~f:(f : 'a -> 'b A.t) : 'b cmplx A.t =
    let open AppSyntax in 
    match c with
    | Base n ->
      let+ n' = TT.traverse_nst n ~f:f in 
      Base n'
    | Adjoin (t,n) -> 
      let+ t' = traverse_cmplx t ~f:f 
      and+ n' = TT.traverse_nst n ~f:f in
      Adjoin (t',n')

  let traverse_cmplx_with_addr (c : 'a cmplx)
      ~f:(f : 'a -> face_addr -> 'b A.t) : 'b cmplx A.t =
    let open AppSyntax in
    let rec go c codim = 
      match c with
      | Base n ->
        let+ n' = TT.traverse_nst_with_addr n
            ~f:(fun a addr -> f a (codim,addr)) in
        Base n'
      | Adjoin (t,n) ->
        let+ t' = go t (codim+1) 
        and+ n' = TT.traverse_nst_with_addr n
            ~f:(fun a addr -> f a (codim,addr)) in
        Adjoin (t',n')

    in go c 0 

  let sequence (c : 'a A.t cmplx) : 'a cmplx A.t =
    traverse_cmplx c ~f:(fun x -> x)
      
end

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)

let rec pp_cmplx_raw (pp_a : 'a Fmt.t) : 'a cmplx Fmt.t =
  fun ppf c ->
  match c with
  | Base n ->
    Fmt.pf ppf "~> @[%a@]" (pp_nst pp_a) n
  | Adjoin (f,n) ->
    Fmt.pf ppf "%a@,|> @[%a@]"
      (pp_cmplx_raw pp_a) f (pp_nst pp_a) n

let pp_cmplx (pp_a : 'a Fmt.t) : 'a cmplx Fmt.t =
  Fmt.vbox (pp_cmplx_raw pp_a)

(*****************************************************************************)
(*                         Complex Zipper Operations                         *)
(*****************************************************************************)

type 'a cmplx_zipper =
  | BaseZip of 'a nst_zipper
  | AdjoinZip of 'a cmplx_zipper * 'a nst_zipper

let rec mk_cmplx_zipper (c : 'a cmplx) : 'a cmplx_zipper =
  match c with
  | Base n -> BaseZip (mk_zipper n)
  | Adjoin (frm,n) ->
    AdjoinZip (mk_cmplx_zipper frm, mk_zipper n) 

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
  | BaseZip ((n,_)) -> Base (Lf (base_value n)) 
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

let rec face_at (c : 'a cmplx) (fa : face_addr) : 'a cmplx =
  if (fst fa <= 0) then
    focus_face (seek_cmplx (mk_cmplx_zipper c) (snd fa))
  else face_at (tail_of c) (fst fa - 1, snd fa)

let face_cmplx (c : 'a cmplx) : 'a cmplx cmplx =
  map_cmplx_with_addr c
    ~f:(fun _ fa -> face_at c fa)

let faces (c : 'a cmplx) : 'a cmplx list =
  labels (face_cmplx c)

let rec apply_at  (c : 'a cmplx) ((codim,addr) : face_addr)
    (f : 'a -> 'a) : 'a cmplx =
  if (codim <= 0) then
    let z = seek_cmplx (mk_cmplx_zipper c) addr in
    let n = focus_of z in 
    let z' = with_focus z (with_base_value n (f (base_value n))) in
    close_cmplx z'
  else match c with
    | Base _ -> raise (ShapeError "Invalid replacement address")
    | Adjoin (t,n) ->
      let t' = apply_at t (codim-1,addr) f in
      Adjoin (t',n)

let replace_at (c : 'a cmplx) (fa : face_addr) (a : 'a) : 'a cmplx =
  apply_at c fa (fun _ -> a)

(*****************************************************************************)
(*                             Complex Validation                            *)
(*****************************************************************************)

let rec validate_linear (n : 'a nst) : unit =
  match n with
  | Lf _ -> ()
  | Nd (_,Nd (br,Lf ())) ->
    validate_linear br
  | _ -> raise (ShapeError "Invalid object nesting") 

let rec validate_bonds (c : 'a cmplx) : 'a tr * 'a tr_deriv = 
  match c with
  | Base n ->
    validate_linear n;
    (as_tr n, mk_deriv (Nd (Lf (), Lf ())))
  | Adjoin (tl,hd) ->
    let (t,d) = validate_bonds tl in
    let sp = spine hd (lazy d) in
    match_shape t sp; 
    (as_tr hd, deriv_of_sh sp)

let validate (c : 'a cmplx) : unit =
  let _ = validate_bonds c in ()

let validate_frame (c : 'a cmplx) : unit =
  let (c,_) = validate_bonds c in
  if (is_corolla c) then ()
  else raise (ShapeError "Boundary is not a corolla")

let validate_opetope (c : 'a cmplx) : unit = 
  match c with
  | Base (Lf _) -> ()
  | Adjoin (f, Lf _) -> validate_frame f
  | _ -> raise (ShapeError "Opetopic complex is not closed")

(*****************************************************************************)
(*                                 Labelling                                 *)
(*****************************************************************************)

let numerate (c : 'a cmplx) : (int cmplx * int) = 
  let i = ref 0 in
  let c' = map_cmplx c 
      ~f:(fun _ -> let v = ! i in
           i := v + 1; v)
  in (c' , ! i) 

