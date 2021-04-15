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
            (fun br dir -> go br ((Dir dir)::addr) n l)
            (fun _ _ -> ())
        in Nd (a',sh')
          
  in go t [] nd lf

(** [map_with_addr] on trees *)
let map_tr_with_addr (t : 'a tr) ~f:(f : 'a -> addr -> 'b) : 'b tr =
  map_with_addr t ~nd:f ~lf:(fun _ _ -> ())

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


(*****************************************************************************)
(*                         Maps including derivatives                        *)
(*****************************************************************************)

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
      | _ -> raise (ShapeError "Mismatch in go")

  in go u v nd lf 

let match_tr_with_deriv (u : 'a tr) (v : 'b tr)
    ~f:(f : 'a -> 'b -> 'c lazy_tr_deriv -> 'd) =
  match_with_deriv u v ~nd:f
    ~lf:(fun _ _ -> ())

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
           split_with_addr_and_deriv br ((Dir dir)::addr) f) in
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
               fold_pass lf nd sh ((Dir dir) :: addr) der) in
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
            ~f:(fun _ dir -> [Dir dir]) in
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
