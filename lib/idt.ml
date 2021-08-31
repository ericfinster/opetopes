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

let (<|) : addr -> addr -> addr =
  fun dir addr -> ((Dir dir)::addr)

let addr_of (d : dir) : addr
  = match d with
  | Dir a -> a

(** Signals malformed or unexpected 
    tree conditions *)
exception ShapeError of string

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
        let sh' = go sh
            (fun br -> go br n l)
            (fun _ -> ()) in 
        let a' = n a in
        Nd (a',sh') 
  in go t nd lf

(** [map] specialized for trees *)
let map_tr (t : 'a tr) ~f:(f : 'a -> 'b) : 'b tr =
  map t ~nd:f ~lf:(fun _ -> ())

(** [map] specialized for nestings *)
let map_nst (n : 'a nst) ~f:(f : 'a -> 'b) : 'b nst =
  map n ~nd:f ~lf:f

(** [map] with tree address in context *)
let map_with_addr (t : ('a , 'b) idt)
    ~nd:(nd : 'a -> addr -> 'c)
    ~lf:(lf : 'b -> addr -> 'd) : ('c , 'd) idt =
  
  let rec go : 'a 'b 'c 'd. ('a , 'b) idt -> addr
    -> ('a -> addr -> 'c)
    -> ('b -> addr -> 'd)
    -> ('c , 'd) idt =
    fun t addr n l ->
      match t with
      | Lf b -> Lf (l b addr)
      | Nd (a,sh) ->
        let a' = n a addr in
        let sh' = go sh []
            (fun br dir -> go br (dir <| addr) n l)
            (fun _ _ -> ())
        in Nd (a',sh')
          
  in go t [] nd lf

(** [map_with_addr] on trees *)
let map_tr_with_addr (t : 'a tr) ~f:(f : 'a -> addr -> 'b) : 'b tr =
  map_with_addr t ~nd:f ~lf:(fun _ _ -> ())

let map_nst_with_addr (t : 'a nst) ~f:(f : 'a -> addr -> 'b) : 'b nst =
  map_with_addr t ~nd:f ~lf:f

(** extract the value at the root of the tree *)
let root_value : ('a , 'b) idt -> 'a =
  function
  | Lf _ -> raise (ShapeError "root value on leaf")
  | Nd (a, _) -> a

(** split the given tree into two using the provided function *)
let rec split_with : 'a 'b 'c 'd. 
  ('a , 'd) idt
  -> ('a -> ('b * 'c))
  -> (('b,'d) idt * ('c,'d) idt) = fun t f ->
  match t with
  | Lf d -> (Lf d, Lf d)
  | Nd (a, sh) -> let (b , c) = f a in
    let (bsh, csh) = split_with sh (fun b -> split_with b f) in
    (Nd (b, bsh) , Nd (c, csh))
      
let idt_unzip : 'a 'b 'c. ('a * 'b , 'c) idt
  -> (('a , 'c) idt * ('b , 'c) idt) =
  fun t -> split_with t (fun p -> p)

let as_tr (t : ('a,'b) idt) : 'a tr =
  map t ~nd:(fun a -> a) ~lf:(fun _ -> ())

let rec nodes : 'a 'b. ('a, 'b) idt -> 'a list =
  fun t -> 
  match t with
  | Lf _ -> []
  | Nd (a,sh) ->
    let brs = map_tr sh ~f:nodes in
    let brs_nds = List.concat (nodes brs) in 
    a :: brs_nds

let is_corolla (t : ('a, 'b) idt) : bool =
  match t with
  | Lf _ -> false
  | Nd (_, sh) -> List.for_all (nodes sh) ~f:is_leaf

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)

let rec pp_idt : 'a 'b. 'a Fmt.t -> 'b Fmt.t
  -> ('a, 'b) idt Fmt.t =
  fun pp_a pp_b ppf t ->
  match t with
  | Lf b -> Fmt.pf ppf "Lf @[%a@]" pp_b b
  | Nd (a,sh) -> 
    Fmt.pf ppf "Nd (@[%a@],@, @[%a@])"
      pp_a a (pp_tr (pp_idt pp_a pp_b)) sh

and pp_tr : 'a. 'a Fmt.t -> 'a tr Fmt.t =
  fun pp_a ppf t ->
  pp_idt pp_a (Fmt.any "()") ppf t 

let pp_nst : 'a Fmt.t -> 'a nst Fmt.t =
  fun pp_a ppf n ->
  pp_idt pp_a pp_a ppf n 

(*****************************************************************************)
(*                          Zippers and Derivatives                          *)
(*****************************************************************************)

type ('a, 'b) idt_deriv = IdtD of ('a, 'b) idt_shell * ('a, 'b) idt_ctxt
and ('a, 'b) idt_ctxt = IdtG of ('a * (('a, 'b) idt, unit) idt_deriv) list
type ('a, 'b) idt_zipper = ('a, 'b) idt * ('a, 'b) idt_ctxt

type 'a tr_deriv = ('a, unit) idt_deriv
type 'a lazy_tr_deriv = 'a tr_deriv Lazy.t
type 'a tr_ctxt = ('a, unit) idt_ctxt
type 'a tr_zipper = ('a, unit) idt_zipper

type 'a nst_deriv = ('a, 'a) idt_deriv
type 'a nst_ctx = ('a, 'a) idt_ctxt
type 'a nst_zipper = ('a, 'a) idt_zipper
    
exception IdtZipperError of string

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

let deriv_of_sh : 'a 'b. 'a tr -> 'b tr_deriv =
  fun tr -> mk_deriv (map_tr tr ~f:(fun _ -> Lf ()))

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
  | (_, IdtG []) -> raise (IdtZipperError "Zipper has no predecessor")
  | (fcs, IdtG ((a, IdtD(ts,g))::gs)) ->
    Nd (a, close_idt_ctxt g (Nd (fcs, ts))), IdtG gs

let rec pred_which (z : ('a, 'b) idt_zipper) (p : 'a -> bool) : ('a, 'b) idt_zipper =
  match z with
  | (_, IdtG []) -> raise (IdtZipperError "Zipper has no predecessor")
  | (fcs, IdtG ((a, IdtD(ts,g))::gs)) ->
    let pz = (Nd (a, close_idt_ctxt g (Nd (fcs, ts))), IdtG gs)
    in if (p a) then pz else pred_which pz p

let rec visit (z : ('a, 'b) idt_zipper) (d : dir) : ('a, 'b) idt_zipper =
  match (focus_of z, d) with
  | (Lf _, _) -> raise (IdtZipperError "Cannot visit a leaf")
  | (Nd (a, sh), Dir ds) ->
    let z' = seek (mk_zipper sh) ds in
    begin match z' with
      | (Lf _, _) -> raise (IdtZipperError "Leaf in shell during visit")
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
  | _ -> raise (IdtZipperError "no element at given address")

let sibling : 'a 'b. ('a, 'b) idt_zipper -> dir -> ('a, 'b) idt_zipper =
  fun (fcs,ctx) dir ->
  match ctx with
  | IdtG [] -> raise (IdtZipperError "no sibling in empty context")
  | IdtG ((a, IdtD (vs, IdtG hcn))::cs) ->
    let vzip = seek_to vs (addr_of dir) in
    match focus_of vzip with
    | Lf _ -> raise (IdtZipperError "horizontal leaf in sibling")
    | Nd (Lf _,_) -> raise (IdtZipperError "vertical leaf in sibling")
    | Nd (Nd (nfcs,vrem),hmsk) ->
      let vctx = IdtG ((fcs, IdtD (hmsk, snd vzip)) :: hcn) in
      let nctx = IdtG ((a, IdtD (vrem, vctx))::cs) in 
      (nfcs, nctx)

(*****************************************************************************)
(*                         Maps including derivatives                        *)
(*****************************************************************************)

let map_with_addr_and_deriv (t : ('a, 'b) idt)
    ~nd:(nd : 'a -> addr -> 'c tr_deriv Lazy.t -> 'd)
    ~lf:(lf : 'b -> addr -> 'e) =

  let rec go : 'a 'b 'c 'd 'e.
    ('a , 'b) idt
    -> addr 
    -> ('a -> addr -> 'c tr_deriv Lazy.t -> 'd)
    -> ('b -> addr -> 'e)
    -> ('d , 'e) idt =
    fun t addr nd lf ->
      match t with
      | Lf b -> Lf (lf b addr)
      | Nd (a,ash) -> 
        let d = nd a addr (lazy (deriv_of_sh ash)) in
        let dsh = go ash []
            (fun br dir _ ->
               go br (dir <| addr) nd lf)
            (fun _ _ -> ()) in
        Nd (d,dsh)
          
  in go t [] nd lf 

let map_tr_with_addr_and_deriv (t : 'a tr)
    ~f:(f : 'a -> addr -> 'b tr_deriv Lazy.t -> 'c) : 'c tr =
  map_with_addr_and_deriv t
    ~nd:f ~lf:(fun _ _ -> ())
    
let map_with_deriv (t : ('a, 'b) idt)
    ~nd:(nd : 'a -> 'c tr_deriv Lazy.t -> 'd)
    ~lf:(lf : 'b -> 'e) =
  
  let rec go : 'a 'b 'c 'd 'e.
    ('a , 'b) idt
    -> ('a -> 'c tr_deriv Lazy.t -> 'd)
    -> ('b -> 'e)
    -> ('d , 'e) idt =
    fun t nd lf ->
      match t with
      | Lf b -> Lf (lf b)
      | Nd (a,ash) ->
        let d = nd a (lazy (deriv_of_sh ash)) in
        let dsh = go ash (fun br _ -> go br nd lf)
            (fun _ -> ()) in 
        Nd (d,dsh)

  in go t nd lf

let map_tr_with_deriv (t : 'a tr)
    ~f:(f : 'a -> 'b tr_deriv Lazy.t -> 'c) =
  map_with_deriv t ~nd:f ~lf:(fun _ -> ())

let match_with_deriv (u : ('a, 'b) idt) (v : ('c, 'd) idt)
    ~nd:(nd : 'a -> 'c -> 'e lazy_tr_deriv -> 'f)
    ~lf:(lf : 'b -> 'd -> 'g) : ('f, 'g) idt =
  
  let rec go : 'a 'b 'c 'd 'e 'f 'g. 
    ('a, 'b) idt
    -> ('c, 'd) idt
    -> ('a -> 'c -> 'e lazy_tr_deriv -> 'f)
    -> ('b -> 'd -> 'g)
    -> ('f , 'g) idt =
    fun u v nd lf ->
      match (u,v) with
      | (Lf b , Lf d) -> Lf (lf b d)
      | (Nd (a,ash), Nd (c,csh)) ->
        let fsh = go ash csh
            (fun abr cbr _ -> go abr cbr nd lf)
            (fun _ _ -> ()) in
        let f = nd a c (lazy (deriv_of_sh fsh)) in 
        Nd (f,fsh)
      | _ -> raise (ShapeError "Match failed")

  in go u v nd lf 

let match_tr_with_deriv (u : 'a tr) (v : 'b tr)
    ~f:(f : 'a -> 'b -> 'c lazy_tr_deriv -> 'd) =
  match_with_deriv u v ~nd:f
    ~lf:(fun _ _ -> ())

(** match for effect *)
let match_shape (u : ('a,'b) idt) (v : ('c,'d) idt) : unit =
  let _ = match_with_deriv u v
      ~nd:(fun _ _ _ -> ())
      ~lf:(fun _ _ -> ()) in ()


(*****************************************************************************)
(*                          Applicative Instance                             *)
(*****************************************************************************)

module TreeBasic =
struct

  type 'a t = 'a tr

  let return a = Nd (a, Lf ())
  let map = `Custom map_tr
  let rec apply : 'a 'b. ('a -> 'b , unit) idt
    -> ('a , unit) idt
    -> ('b , unit) idt =
    fun f t -> 
    match (f,t) with
    | (Lf (),_) -> Lf ()
    | (_,Lf ()) -> Lf () 
    | (Nd (f,fsh),Nd(a,ash)) ->
      let fsh' = map_tr fsh ~f:apply in 
      (Nd (f a , apply fsh' ash))
    
end

module NestingBasic =
struct
  
  type 'a t = 'a nst

  let return a = Lf a
  let map = `Custom map_nst
  let rec apply : 'a 'b. ('a -> 'b) nst 
    -> 'a nst -> 'b nst = 
    fun nf t -> 
    match (nf,t) with
    | (Lf f , Lf a) -> Lf (f a)
    | (Lf f, Nd (a,_)) -> Lf (f a)
    | (Nd (f,_), Lf a) -> Lf (f a)
    | (Nd (f,fsh),Nd(a,ash)) ->
      let fsh' = map_tr fsh ~f:apply in 
      (Nd (f a , TreeBasic.apply fsh' ash))

end

module TreeApplicative = Applicative.Make(TreeBasic)
module NestingApplicative = Applicative.Make(NestingBasic)


(*****************************************************************************)
(*                          Tree Traversal Routines                          *)
(*****************************************************************************)

module TreeTraverse (A : Applicative.Basic) = struct

  module AI = Applicative.Make(A)

  module AppSyntax = struct
    let (let+) x f = AI.map ~f:f x
    let (and+) p q = AI.both p q 
  end
  
  (** Basic traversal *)
  let rec traverse : 'a 'b 'c 'd. ('a, 'b) idt
    -> ('a -> 'c A.t)
    -> ('b -> 'd A.t)
    -> ('c,'d) idt A.t = fun t nd lf ->
    let open AppSyntax in 
    match t with
    | Lf b -> let+ d = lf b in Lf d
    | Nd (a,sh) ->
      let+ b = nd a
      and+ sh' = traverse_tr sh
          ~f:(fun br -> traverse br nd lf)
      in Nd (b,sh')

  and traverse_tr (t : 'a tr) ~f:(f : 'a -> 'b A.t) : 'b tr A.t =
    traverse t f (fun _ -> A.return ())

  let traverse_nst (t : 'a nst) ~f:(f : 'a -> 'b A.t) : 'b nst A.t =
    traverse t f f
  
  (** Traverse with address in scope *)
  let rec traverse_with_addr : 'a 'b 'c 'd. ('a, 'b) idt
    -> ('a -> addr -> 'c A.t)
    -> ('b -> addr -> 'd A.t)
    -> addr -> ('c, 'd) idt A.t =
    fun t nd lf addr ->
    let open AppSyntax in 
    match t with
    | Lf b -> let+ d = lf b addr in Lf d
    | Nd (a,ash) ->
      let+ b = nd a addr 
      and+ bsh = traverse_with_addr ash
          (fun br dir -> traverse_with_addr br nd lf (dir <| addr))
          (fun _ _ -> A.return ()) [] in
      Nd (b,bsh)

  (** Traverse a tree with address in scope *)
  and traverse_tr_with_addr (t : 'a tr)
      ~f:(f : 'a -> addr -> 'b A.t) : 'b tr A.t =
    traverse_with_addr t f (fun _ _ -> A.return ()) []

  (** Traverse a nesting with address in scope *)
  let traverse_nst_with_addr (n : 'a nst)
      ~f:(f : 'a -> addr -> 'b A.t) : 'b nst A.t =
    traverse_with_addr n f f [] 

  let sequence (t : ('a A.t , 'b A.t) idt) : ('a , 'b) idt A.t =
    traverse t (fun x -> x) (fun x -> x)

  let seqeunce_tr (t : 'a A.t tr) : 'a tr A.t =
    traverse t (fun x -> x) (fun _ -> A.return ())

  let sequence_nst (n : 'a A.t nst) : 'a nst A.t =
    traverse n (fun x -> x) (fun x -> x) 
    
end

(* I cannot get the Base functor system to work, so I'm putting 
   this default instance here for options even though, in principle,
   you should be able to define it on the fly .... *)
module OptionTraverse = TreeTraverse(struct
    type 'a t = 'a option
    let map = `Custom Option.map
    let return = Option.return
    let apply og oa =
      match (og,oa) with
      | (None,_) -> None
      | (_, None) -> None
      | (Some g,Some a) -> Some (g a)
  end)

(*****************************************************************************)
(*                       Folding, Grafting and Joining                       *)
(*****************************************************************************)

let rec intertwine : 'a 'b 'c 'd 'e. 'a tr -> 'b tr
  -> ('a -> 'b -> 'c tr_deriv Lazy.t -> ('d * 'e))
  -> 'd tr * 'e tr =
  fun s t f ->
  match (s , t) with
  | (Lf _ , Lf _) -> (Lf (), Lf ())
  | (Nd (a, ash) , Nd (c , csh)) ->
    let (esh , fsh) =
      intertwine ash csh 
        (fun abr cbr _ -> intertwine abr cbr f) in 
    let (e , f) = f a c (lazy (deriv_of_sh ash)) in
    (Nd (e,esh) , Nd (f,fsh))
  | _ -> raise (ShapeError "Mismatch in intertwine")

let rec split_with_addr_and_deriv : 'a 'b 'c 'd.
  ('a , 'b) idt
  -> addr 
  -> ('a -> addr -> addr tr_deriv Lazy.t -> 'c * 'd)
  -> (('c, 'b) idt * ('d, 'b) idt) =
  fun t addr f -> 
  match t with
  | Lf b -> (Lf b , Lf b)
  | Nd (a,ash) ->
    let (c,d) = f a addr (lazy (deriv_of_sh ash)) in
    let (csh,dsh) =
      split_with_addr_and_deriv ash []
        (fun br dir _ ->
           split_with_addr_and_deriv br (dir <| addr) f) in
    (Nd (c,csh), Nd (d,dsh))

let rec idt_fold (t : ('a, 'b) idt)
    ~lf:(lf : ('b -> addr -> 'c))
    ~nd:(nd : ('a -> 'c tr -> 'c)) : 'c =

  let rec idt_fold_impl : 'a 'b 'c 'd. ('a, 'b) idt
    -> ('b -> addr -> 'c)
    -> ('a -> 'c tr -> 'c) -> 'c =
    fun tr lf nd ->
      match tr with
      | Lf b -> lf b []
      | Nd (a, Lf u) -> nd a (Lf u)
      | Nd (a, Nd (v, h)) -> 
        fst (init_vertical a lf nd v h)

  and fold_pass : 'a 'b 'c. ('b -> addr -> 'c)                  
    -> ('a -> 'c tr -> 'c)
    -> ('a, 'b) idt tr
    -> addr -> addr tr_deriv Lazy.t
    -> ('c tr * addr tr) =
    fun lf nd h addr dr ->
      match h with
      | Lf _ -> (Lf () , plug_idt_deriv (Lazy.force dr) addr)
      | Nd (Lf b, hs) ->
        let (csh,atr) = split_with_addr_and_deriv hs []
            (fun sh dir der ->
               fold_pass lf nd sh (dir <| addr) der) in
        let c = lf b addr in 
        (Nd (c,csh), idt_join atr)
      | Nd (Nd (a,vs), hs) ->
        let (btr,atr) = fold_pass lf nd vs addr dr in
        let (csh,atr') = intertwine hs atr
            (fold_pass lf nd) in
        let c = nd a btr in 
        (Nd (c,csh) , idt_join atr')

  and init_horizontal : 'a 'b 'c. 'a
    -> ('b -> addr -> 'c)
    -> ('a -> 'c tr -> 'c)
    -> ('a, 'b) idt tr tr
    -> 'c * addr tr
    -> 'c * addr tr =
    fun a lf nd hs (c , atr) ->
      let (csh,atr') = intertwine hs atr
          (fold_pass lf nd) in
      (nd a (Nd (c, csh)), idt_join atr')

  and init_vertical : 'a 'b 'c. 'a
    -> ('b -> addr -> 'c)
    -> ('a -> 'c tr -> 'c)
    -> ('a, 'b) idt
    -> ('a, 'b) idt tr tr
    -> 'c * addr tr =
    fun a lf nd v h ->
      match v with
      | Lf b ->
        let atr = map_tr_with_addr h
            ~f:(fun _ dir -> dir <| []) in
        let c = lf b [] in
        init_horizontal a lf nd h (c,atr) 
      | Nd (a, Lf _) ->
        let atr = map_tr h ~f:(fun _ -> []) in 
        let c = nd a (Lf ()) in 
        init_horizontal a lf nd h (c,atr)
      | Nd (a, Nd(v,h)) ->
        init_horizontal a lf nd h (init_vertical a lf nd v h)

  in idt_fold_impl t lf nd
    
and idt_graft : 'a 'b 'c. ('a, 'b) idt -> ('a, 'c) idt_shell -> ('a, 'c) idt =
  fun t sh -> idt_fold t
    ~lf:(fun _ addr -> element_at sh addr)
    ~nd:(fun a ash -> Nd (a, ash))

and idt_join : 'a 'b. (('a , 'b) idt , 'b) idt -> ('a, 'b) idt =
  function
  | Lf b -> Lf b
  | Nd (t, tsh) ->
    idt_graft t
      (map_tr tsh ~f:idt_join)

(*****************************************************************************)
(*                               Shell Extents                               *)
(*****************************************************************************)

(* I think this could be simplified if the fold routine was extended
   to have derivatives.  This clearly would have the advantage that
   one could calculate the canopy of a tree with a single fold, right?
   Anyway ....
*)
      
let extents (sh : 'a tr tr) : addr tr =

  let rec go : 'a tr tr -> addr -> addr tr =
    fun sh addr -> 
    let jsh = map_tr_with_addr_and_deriv sh
        ~f:(fun br dir rho ->
            match br with
            | Lf _ -> plug_idt_deriv (Lazy.force rho) (dir <| addr)
            | Nd (_, sh') -> go sh' (dir <| addr)) in 
    idt_join jsh

  in go sh [] 

(*****************************************************************************)
(*                           Operations on Nestings                          *)
(*****************************************************************************)
    
let rec nodes_nst : 'a. 'a nst -> 'a list =
  fun n -> 
  match n with
  | Lf a -> [a]
  | Nd (a,sh) ->
    let brs = map_tr sh ~f:nodes_nst in
    let brs_nds = List.concat (nodes brs) in 
    a :: brs_nds

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

  (***************************************************************************)
  (*                             Tree Expressions                            *)
  (***************************************************************************)

  (* FIXME: naming could use some cleanup here ... *)
        
  (** possibly ill-typed tree expressions *)
  type 'a tr_expr =
    | UnitE
    | ValueE of 'a 
    | LeafE of 'a tr_expr
    | NodeE of 'a tr_expr * 'a tr_expr

  exception TreeExprError of string
      
  let to_unit (t : 'a tr_expr) : unit = 
    match t with
    | UnitE -> ()
    | _ -> raise (TreeExprError "Expected a unit")

  let to_value (t : 'a tr_expr) : 'a =
    match t with
    | ValueE a -> a
    | _ -> raise (TreeExprError "Expected a value")

  let rec to_idt : 'a 'b 'c. 'c tr_expr
    -> ('c tr_expr -> 'a)
    -> ('c tr_expr -> 'b)
    -> ('a, 'b) idt = fun t nd lf ->
    match t with
    | UnitE -> raise (TreeExprError "Unit is not a tree")
    | ValueE _ -> raise (TreeExprError "Value is not a tree")
    | LeafE t' -> Lf (lf t')
    | NodeE (t',sh') ->
      let a = nd t' in
      let sh = to_idt sh' 
          (fun br -> to_idt br nd lf)
          to_unit in
      Nd (a,sh)

  let to_nst (t : 'a tr_expr) : 'a nst =
    to_idt t to_value to_value
      
  let rec of_idt : 'a 'b 'c. ('a, 'b) idt
    -> ('a -> 'c tr_expr)
    -> ('b -> 'c tr_expr)
    -> 'c tr_expr = fun t nd lf ->
    match t with
    | Lf b -> lf b
    | Nd (a,sh) ->
      let sh_expr =
        of_idt sh
          (fun br -> of_idt br nd lf) 
          (fun _ -> UnitE) in 
      NodeE (nd a, sh_expr)

  let of_nst (n : 'a nst) : 'a tr_expr =
    let mk_val a = ValueE a in 
    of_idt n mk_val mk_val
  
  let rec pp_tr_expr pp_a ppf t =
    match t with
    | UnitE -> Fmt.pf ppf "tt"
    | ValueE a -> Fmt.pf ppf "{ %a }" pp_a a
    | LeafE te -> Fmt.pf ppf "lf %a" (pp_tr_expr pp_a) te
    | NodeE (te,sh) ->
      Fmt.pf ppf "nd %a %a"
        (pp_tr_expr_parens pp_a te) te
        (pp_tr_expr_parens pp_a sh) sh 

  and pp_tr_expr_parens pp_a te =
    match te with
    | LeafE _ -> Fmt.parens (pp_tr_expr pp_a)
    | NodeE _ -> Fmt.parens (pp_tr_expr pp_a)
    | _ -> pp_tr_expr pp_a
  
end



