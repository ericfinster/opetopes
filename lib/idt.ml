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

  type ('a, 'b) idt_deriv = TrD of ('a, 'b) idt_shell * ('a, 'b) idt_ctxt
  and ('a, 'b) idt_ctxt = TrG of ('a * (('a, 'b) idt, unit) idt_deriv) list

  type ('a, 'b) idt_lazy_deriv = ('a, 'b) idt_deriv Lazy.t
  type ('a, 'b) idt_zipper = ('a, 'b) idt * ('a, 'b) idt_ctxt
  
  type 'a tr_deriv = ('a, unit) idt_deriv
  type 'a tr_ctxt = ('a, unit) idt_ctxt
  type 'a tr_lazy_deriv = ('a, unit) idt_lazy_deriv
  type 'a tr_zipper = ('a, unit) idt_zipper
  
  (* let rec plug_tree_deriv : 'a 'b. ('a, 'b) gtree_deriv -> 'a -> ('a, 'b) gtree =
   *   fun d a -> match d with
   *       TrD (sh,g) -> close_tree_ctxt g (Nd (a, sh))
   * and close_tree_ctxt : 'a 'b. ('a, 'b) gtree_ctxt -> ('a, 'b) gtree -> ('a, 'b) gtree =
   *   fun c t -> match c with
   *       TrG [] -> t
   *     | TrG ((a,d)::gs) -> close_tree_ctxt (TrG gs) (Nd (a, plug_tree_deriv d t))
   * 
   * 
   * let mk_deriv : 'a. 'a tree_shell -> 'a tree_deriv =
   *   fun sh -> TrD (sh, TrG [])
   * 
   * let sh_deriv : 'a 'b. 'a tree -> 'b tree_deriv =
   *   fun t -> mk_deriv (as_shell t) *)

end



(*****************************************************************************)
(*                     Utils for Encoding Lists and Trees                    *)
(*****************************************************************************)
            
let rec of_list (l : 'a list) : 'a tr =
  match l with
  | [] -> Lf ()
  | x::xs ->
    Nd (x,Nd(of_list xs,Lf ()))

(* planar trees *)
type 'a planar_tr =
  | Leaf
  | Node of ('a * 'a planar_tr list)

let rec of_planar_tr (p : 'a planar_tr) : 'a tr =
  match p with
  | Leaf -> Lf ()
  | Node (x,brs) ->
    let trs = List.map brs ~f:of_planar_tr in 
    Nd (x, of_list trs)

