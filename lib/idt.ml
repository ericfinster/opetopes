(*****************************************************************************)
(*                                                                           *)
(*                    idt.ml - infinite dimensional trees                    *)
(*                                                                           *)
(*****************************************************************************)

open Base

(** infinite dimensional trees with nodes labelled by ['a]
    and leaves labelled by ['b] *)
type ('a , 'b) idt =
  | Lf of 'b
  | Nd of 'a * (('a , 'b) idt , unit) idt
[@@ deriving sexp ]

type 'a tr = ('a , unit) idt
type 'a nst = ('a , 'a) idt

type ('a, 'b) idt_shell = ('a, 'b) idt tr
type 'a tr_shell = ('a, unit) idt_shell

(** Directions and Addresses *)
type dir = Dir of addr
and addr = dir list

let corolla : 'a. 'a -> 'a tr =
  fun a -> Nd (a, Lf ()) 

(** [true] if this tree is a leaf *)
let is_leaf (t : ('a , 'b) idt) : bool =
  match t with
  | Lf _ -> true
  | Nd _ -> false

(** [true] if this tree is a node *)
let is_node (t : ('a , 'b) idt) : bool =
  match t with
  | Lf _ -> false
  | Nd _ -> true

(** general functorial action *)
let map (t : ('a , 'b) idt) ~nd:(nd : 'a -> 'c) ~lf:(lf : 'b -> 'd) : ('c , 'd) idt =
  let rec go : 'a 'b 'c 'd. ('a , 'b) idt -> ('a -> 'c) -> ('b -> 'd) -> ('c , 'd) idt =
    fun t n l ->
      match t with
      | Lf b -> Lf (l b)
      | Nd (a,sh) ->
        let a' = n a in
        let sh' = go sh
            (fun br -> go br n l)
            (fun _ -> ())
        in Nd (a',sh') 
  in go t nd lf

(** [map] specialized for trees *)
let map_tr (t : 'a tr) ~f:(f : 'a -> 'b) : 'b tr =
  map t ~nd:f ~lf:(fun _ -> ())

(** [map] specialized for nestings *)
let map_nst (n : 'a nst) ~f:(f : 'a -> 'b) : 'b nst =
  map n ~nd:f ~lf:f

(*****************************************************************************)
(*                          Zippers and Derivatives                          *)
(*****************************************************************************)

module IdtZipper = struct

  type ('a, 'b) idt_deriv = IdtD of ('a, 'b) idt_shell * ('a, 'b) idt_ctxt
  and ('a, 'b) idt_ctxt = IdtG of ('a * (('a, 'b) idt, unit) idt_deriv) list

  type ('a, 'b) idt_lazy_deriv = ('a, 'b) idt_deriv Lazy.t
  type ('a, 'b) idt_zipper = ('a, 'b) idt * ('a, 'b) idt_ctxt
  
  type 'a tr_deriv = ('a, unit) idt_deriv
  type 'a tr_ctxt = ('a, unit) idt_ctxt
  type 'a tr_lazy_deriv = ('a, unit) idt_lazy_deriv
  type 'a tr_zipper = ('a, unit) idt_zipper

  exception ZipperError of string
      
  let rec plug_idt_deriv : 'a 'b. ('a, 'b) idt_deriv -> 'a -> ('a, 'b) idt =
    fun d a ->
    match d with
    | IdtD (sh,gma) -> close_idt_ctxt gma (Nd (a, sh))

  and close_idt_ctxt : 'a 'b. ('a, 'b) idt_ctxt -> ('a, 'b) idt -> ('a, 'b) idt =
    fun gma tr ->
    match gma with
    | IdtG [] -> tr
    | IdtG ((a,d)::gs) ->
      close_idt_ctxt (IdtG gs) (Nd (a, plug_idt_deriv d tr))

  let mk_deriv : 'a 'b. ('a , 'b) idt_shell -> ('a , 'b) idt_deriv =
    fun sh -> IdtD (sh, IdtG [])

  let mk_zipper (t : ('a , 'b) idt) : ('a , 'b) idt_zipper =
    (t, IdtG [])

  let focus_of (z : ('a , 'b) idt_zipper) : ('a , 'b) idt =
    fst z
  
  let ctxt_of (z : ('a , 'b) idt_zipper) : ('a * (('a, 'b) idt, unit) idt_deriv) list =
    match z with
    | (_, IdtG gma) -> gma
  
  let close (z : ('a, 'b) idt_zipper) : ('a, 'b) idt =
    close_idt_ctxt (snd z) (fst z)
  
  let close_with (tr : ('a, 'b) idt) (z : ('a, 'b) idt_zipper) : ('a, 'b) idt =
    close_idt_ctxt (snd z) tr 

  let pred (z : ('a, 'b) idt_zipper) : ('a, 'b) idt_zipper =
    match z with 
    | (_, IdtG []) -> raise (ZipperError "Zipper has no predecessor")
    | (fcs, IdtG ((a, IdtD(ts,g))::gs)) ->
      Nd (a, close_idt_ctxt g (Nd (fcs, ts))), IdtG gs
  
  let rec pred_which (z : ('a, 'b) idt_zipper) (p : 'a -> bool) : ('a, 'b) idt_zipper =
    match z with
    | (_, IdtG []) -> raise (ZipperError "Zipper has no predecessor")
    | (fcs, IdtG ((a, IdtD(ts,g))::gs)) ->
      let pz = (Nd (a, close_idt_ctxt g (Nd (fcs, ts))), IdtG gs)
      in if (p a) then pz else pred_which pz p
  
  let rec visit (z : ('a, 'b) idt_zipper) (d : dir) : ('a, 'b) idt_zipper =
    match (focus_of z, d) with
    | (Lf _, _) -> raise (ZipperError "Cannot visit a leaf")
    | (Nd (a, sh), Dir ds) ->
      let z' = seek (mk_zipper sh) ds in
      begin match z' with
        | (Lf _, _) -> raise (ZipperError "Leaf in shell during visit")
        | (Nd (t, ts), g) -> (t, IdtG ((a, IdtD(ts, g)) :: ctxt_of z))
      end
  
  and seek : 'a 'b. ('a, 'b) idt_zipper -> addr -> ('a, 'b) idt_zipper =
    fun z a -> 
    match a with
    | [] -> z
    | d :: ds -> visit (seek z ds) d 
  
  let seek_to (t : ('a, 'b) idt) (a : addr) : ('a, 'b) idt_zipper =
    seek (mk_zipper t) a 
  
  let element_at (t : ('a, 'b) idt) (a : addr) : 'a =
    match focus_of (seek_to t a) with
    | Nd (x,_) -> x
    | _ -> raise (ZipperError "no element at given address")
  
end

(*****************************************************************************)
(*                     Utils for Encoding Lists and Trees                    *)
(*****************************************************************************)

module IdtConv = struct

  (** lists as linear trees *)
  let rec of_list (l : 'a list) : 'a tr =
    match l with
    | [] -> Lf ()
    | x::xs ->
      Nd (x,Nd(of_list xs,Lf ()))

  (* planar trees *)
  type 'a planar_tr =
    | Leaf
    | Node of ('a * 'a planar_tr list)

  (** encode planar trees *)
  let rec of_planar_tr (p : 'a planar_tr) : 'a tr =
    match p with
    | Leaf -> Lf ()
    | Node (x,brs) ->
      let trs = List.map brs ~f:of_planar_tr in 
      Nd (x, of_list trs)

end
