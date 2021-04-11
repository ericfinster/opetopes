(*****************************************************************************)
(*                                                                           *)
(*                    tree.ml - infinite dimensional trees                   *)
(*                                                                           *)
(*****************************************************************************)

(* Find some place to put this .... *)
(* let (???) : 'a. 'a = failwith "bot" *)

(** This module defines infinite dimensional trees as an inductive
    type and provides a number of important operations on them 
    such as grafting and substitution as well as zippers and 
    useful traversal functions. *)

(** Basic tree datatype *)
type 'a tree =
  | Lf
  | Nd of 'a * 'a tree tree
            
type 'a tree_shell =
  'a tree tree

(** Tree addresses *)
type dir = Dir of addr
and addr = dir list
    
(** Tree Applicative Instance *)
module TreeApplicativeBasic : Base.Applicative.Basic
  with type 'a t = 'a tree = struct

  type 'a t = 'a tree
      
  let map_tree (t : 'a tree) ~f:(f : 'a -> 'b) : 'b tree =
    let rec go : 'a 'b. 'a tree -> ('a -> 'b) -> 'b tree =
      fun t f -> match t with
        | Lf -> Lf
        | Nd (a, sh) -> Nd (f a, go sh (fun br -> go br f)) 
    in go t f
      
  let map = `Custom map_tree 
  let return x = Nd (x,Lf)

  (* FIXME: This could be useful. Make globally visible? *)
  let rec zip_with : 'a 'b 'c. 'a tree -> 'b tree -> ('a -> 'b -> 'c) ->  'c tree =
    fun s t f ->
    match (s , t) with
    | (Lf, Lf) -> Lf
    | (Lf, Nd _) -> Lf
    | (Nd _, Lf) -> Lf
    | (Nd (a,ash), Nd (b,bsh)) ->
      let csh = zip_with ash bsh
          (fun abr bbr -> zip_with abr bbr f) in 
      Nd (f a b, csh)
  
  let rec apply_tree : 'a 'b. ('a -> 'b) tree -> 'a tree -> 'b tree =
    fun ft vt -> 
    match (ft, vt) with
    | (Lf, Lf) -> Lf
    | (Lf, Nd _) -> Lf
    | (Nd _, Lf) -> Lf
    | (Nd (f,fsh), Nd (v,vsh)) ->
      let v' = f v in
      let vsh' = zip_with fsh vsh
          (fun fbr vbr -> apply_tree fbr vbr) in 
      Nd (v',vsh')
        
  let apply ft vt = apply_tree ft vt 
    
end

module TrApp = Base.Applicative.Make(TreeApplicativeBasic)

(*****************************************************************************)
(*                         Applicative Syntax Module                         *)
(*****************************************************************************)
      
(* Where to put this? *)
module AppSyntax (A : Base.Applicative.Basic) = struct

  module AI = Base.Applicative.Make(A)
      
  let (let+) x f = AI.map ~f:f x
  let (and+) p q = AI.both p q 
  
end

(*****************************************************************************)
(*                         Basic Opertaions on Trees                         *)
(*****************************************************************************)

open Result
type 'a str_err = ('a , string) result

exception TreeException of string 

(** true if the given tree is a leaf *)
let is_leaf t =
  match t with
  | Lf -> true
  | Nd (_, _) -> false 

(** true if the given leaf is a node *)
let is_node t =
  match t with
  | Lf -> false
  | Nd (_, _) -> true

(** view the given tree as a shell consisting of leaves *)
let as_shell : 'a 'b. 'a tree -> 'b tree_shell =
  fun t -> TrApp.map t ~f:(fun _ -> Lf)

let as_leaf : 'a tree -> unit str_err =
  function
  | Lf -> Ok ()
  | Nd (_, _) -> Error "Leaf force failed"

let as_node : 'a tree -> ('a * 'a tree_shell) str_err =
  function
  | Lf -> Error "Node force failed"
  | Nd (a, sh) -> Ok (a, sh)

(** extract the value at the root of the tree *)
let root_value : 'a tree -> 'a str_err =
  function
  | Lf -> Error "No root value"
  | Nd (a, _) -> Ok a

(** split the given tree into two using the provided function *)
let rec split_with : 'a 'b 'c. ('a -> ('b * 'c)) -> 'a tree -> ('b tree * 'c tree) =
  fun f t ->
  match t with
  | Lf -> (Lf, Lf)
  | Nd (a, sh) -> let (b , c) = f a in
    let (bsh, csh) = split_with (split_with f) sh in
    (Nd (b, bsh) , Nd (c, csh))

let tree_unzip : 'a 'b. ('a * 'b) tree -> ('a tree * 'b tree) =
  fun t -> split_with (fun p -> p) t

(*****************************************************************************)
(*                     Derivatives, Contexts and Zippers                     *)
(*****************************************************************************)

module TreeZipper = struct
  
  type 'a tr_deriv = TrD of 'a tree_shell * 'a tree_ctxt
  and 'a tree_ctxt = TrG of ('a * 'a tree tr_deriv) list

  type 'a lazy_deriv = 'a tr_deriv Lazy.t                         
  type 'a tree_zipper = 'a tree * 'a tree_ctxt

  exception TreeZipperError of string 
  
  let mk_deriv : 'a. 'a tree_shell -> 'a tr_deriv =
    fun sh -> TrD (sh, TrG [])

  let sh_deriv : 'a tree -> 'b tr_deriv =
    fun t -> mk_deriv (as_shell t)

  let rec plug_tr_deriv : 'a. 'a tr_deriv -> 'a -> 'a tree = fun d a ->
    match d with
      TrD (sh,g) -> close_tree_ctxt g (Nd (a, sh))

  and close_tree_ctxt : 'a. 'a tree_ctxt -> 'a tree -> 'a tree = fun c t ->
    match c with
    | TrG [] -> t
    | TrG ((a,d)::gs) -> close_tree_ctxt (TrG gs) (Nd (a, plug_tr_deriv d t))

  let focus_of (z : 'a tree_zipper) : 'a tree =
    fst z

  let ctxt_of (z : 'a tree_zipper) : ('a * 'a tree tr_deriv) list =
    match z with
    | (_, TrG g) -> g

  let mk_zipper (t : 'a tree) : 'a tree_zipper =
    (t, TrG [])

  let close : 'a tree_zipper -> 'a tree =
    function (fcs, ctxt) -> close_tree_ctxt ctxt fcs

  let close_with : 'a tree -> 'a tree_zipper -> 'a tree =
    fun t z ->
    match z with
      (_, ctxt) -> close_tree_ctxt ctxt t

  let pred (z : 'a tree_zipper) : 'a tree_zipper =
    match z with 
    | (_, TrG []) -> raise (TreeZipperError "Zipper has no predecessor")
    | (fcs, TrG ((a, TrD(ts,g))::gs)) ->
      Nd (a, close_tree_ctxt g (Nd (fcs, ts))), TrG gs

  let rec pred_which (z : 'a tree_zipper) (p : 'a -> bool) : 'a tree_zipper =
    match z with
    | (_, TrG []) -> raise (TreeZipperError "Zipper has no predecessor")
    | (fcs, TrG ((a, TrD(ts,g))::gs)) ->
      let pz = (Nd (a, close_tree_ctxt g (Nd (fcs, ts))), TrG gs)
      in if (p a) then pz else pred_which pz p

  let rec visit (z : 'a tree_zipper) (d : dir) : 'a tree_zipper =
    match (focus_of z, d) with
    | (Lf, _) -> raise (TreeZipperError "Cannot visit a leaf")
    | (Nd (a, sh), Dir ds) ->
      let z' = seek (mk_zipper sh) ds in
      begin match z' with
        | (Lf, _) -> raise (TreeZipperError "Leaf in shell during visit")
        | (Nd (t, ts), g) -> (t, TrG ((a, TrD(ts, g)) :: ctxt_of z))
      end

  and seek : 'a. 'a tree_zipper -> addr -> 'a tree_zipper =
    fun z a -> 
    match a with
    | [] -> z
    | d :: ds -> visit (seek z ds) d 

  let seek_to (t : 'a tree) (a : addr) : 'a tree_zipper =
    seek (mk_zipper t) a 

  let element_at (t : 'a tree) (a : addr) : 'a str_err =
    root_value (focus_of (seek_to t a))
  
end

(*****************************************************************************)
(*                          Tree Traversal Routines                          *)
(*****************************************************************************)

module TreeTraverse (A : Base.Applicative.Basic) = struct

  open TreeZipper
  
  (** Basic tree traversal *)
  let rec traverse : 'a 'b. 'a tree -> ('a -> 'b A.t) -> 'b tree A.t =
    fun t f -> let open AppSyntax(A) in 
      match t with
      | Lf -> A.return Lf
      | Nd (a,sh) ->
        let+ b = f a
        and+ sh' = traverse sh (fun br -> traverse br f)
        in Nd (b,sh')

  (** Traverse with address in scope *)
  let rec traverse_with_addr : 'a 'b. 'a tree ->
    ('a -> addr -> 'b A.t) -> 'b tree A.t = fun t f -> 
    let open AppSyntax(A) in 
    let rec go t addr =
      match t with
      | Lf -> A.return Lf
      | Nd (a,sh) ->
        let+ b = f a addr
        and+ sh' = traverse_with_addr sh
            (fun br dir -> go br ((Dir dir)::addr))
        in Nd (b,sh')
        
    in go t []

  (** Traverse with local derivative in scope *)
  let rec traverse_with_deriv : 'a 'b 'c. 'a tree ->
    ('a -> 'b tr_deriv -> 'c A.t) -> 'c tree A.t = fun t f ->
    let open AppSyntax(A) in 
    match t with
    | Lf -> A.return Lf
    | Nd (a,sh) ->
      let+ b = f a (sh_deriv sh)
      and+ sh' = traverse sh
          (fun br -> traverse_with_deriv br f)
      in Nd (b,sh')

  (* FIXME: Actually, the derivative here should really be lazy, since
     most of the time we don't actually use it.... *)
  
  (** Traverse with both addres and local derivative
      in scope *)
  let traverse_with_addr_and_deriv : 'a 'b 'c. 'a tree 
    -> ('a -> addr -> 'b tr_deriv -> 'c A.t)
    -> 'c tree A.t = fun t f -> 
    let open AppSyntax(A) in 
    let rec go t addr =
      match t with
      | Lf -> A.return Lf
      | Nd (a,sh) ->
        let+ b = f a addr (sh_deriv sh)
        and+ sh' = traverse_with_addr sh
            (fun br dir -> go br ((Dir dir)::addr))
        in Nd (b,sh')
        
    in go t []
    
end

(*****************************************************************************)
(*                       Folding, Grafting and Joining                       *)
(*****************************************************************************)

(* So, you never use the monadic capabilities of this fold.  Should we just 
   get rid of them? *)

(* let rec tree_fold : 'a 'b. (addr -> 'b) -> ('a -> 'b tree -> 'b) -> 'a tree -> 'b str_err =
 *   fun lr nr t ->
 *   match t with
 *     Lf -> lr []
 *   | Nd (a, Lf) -> nr a Lf
 *   | Nd (a, Nd (v, hs)) ->
 * 
 *     let unzip_and_join : 'a 'b. ('b tree * addr tree) tree -> ('b tree_shell * addr tree) m = 
 *         fun t -> let (bs, adJn) = tree_unzip t
 *           in tree_join adJn >>= fun at -> Ok (bs, at) in
 * 
 *     let unzip_join_append : 'a 'b. ('b tree * addr tree) tree -> 'b m -> ('b tree * addr tree) m = 
 *         fun t mb -> unzip_and_join t >>= function
 *             (bs, at) -> mb >>= fun b -> Ok (Nd (b, bs), at) in
 * 
 *     let rec fold_pass : 'a 'b. 'a tree_shell -> addr -> addr tr_deriv -> ('b tree * addr tree) m = 
 *         fun h addr d ->
 *           match h with
 *             Lf -> Ok (Lf, plug_tr_deriv d addr)
 *           | Nd (Lf, hs) -> let f = fun hbr dir deriv -> fold_pass hbr ((Dir dir) :: addr) deriv
 *             in  traverse_with_local f hs >>= fun hr ->
 *             unzip_join_append hr (lr addr)
 *           | Nd (Nd (a, vs), hs) -> fold_pass vs addr d >>= function
 *               (bs, at) -> TM.match_with_deriv fold_pass hs at >>= fun mr ->
 *               unzip_join_append mr (nr a bs) in
 * 
 *     let init_horizontal : 'a 'b. 'a -> 'a tree_shell tree -> ('b * addr tree) m -> ('b * addr tree) m =
 *         fun a h m -> m >>= function (c, at) -> TM.match_with_deriv fold_pass h at >>=
 *             unzip_and_join >>= function
 *               (cs, atr) -> nr a (Nd (c, cs)) >>= fun b ->
 *               Ok (b , at) in
 * 
 *     let rec init_vertical : 'a 'b. 'a -> 'a tree -> 'a tree_shell tree -> ('b * addr tree) m = 
 *         fun a v h ->
 *           match v with
 *             Lf -> let h' = map_with_addr (fun _ dir -> ((Dir dir) :: [])) h
 *             in init_horizontal a h (lr [] >>= fun b -> Ok (b, h'))
 *           | Nd (aa, Lf) -> init_horizontal a h (nr aa Lf >>= fun b -> Ok (b, map (fun _ -> []) h))
 *           | Nd (aa, Nd (vv, hh)) -> init_horizontal a h (init_vertical aa vv hh)
 * 
 *     in init_vertical a v hs >>= function (r, _) -> Ok r
 * 
 * and tree_graft : 'a. 'a tree -> 'a tree_shell -> 'a tree str_err =
 *   fun t sh -> tree_fold (fun a -> element_at a sh) (fun a ash -> Ok (Nd (a, ash))) t
 * 
 * and tree_join : 'a. 'a tree_shell -> 'a tree str_err =
 *   function
 *     Lf -> Ok Lf
 *   | Nd (a, ash) -> traverse tree_join ash >>= fun r ->
 *     tree_graft a r *)


(* module TreeOps (M: MonadError with type e = string) = struct
 *   open M
 *      
 *   module Z = TreeZipperOps(M)
 *   open Z
 *            
 *   module T = TreeTraverse(M)
 *   open T
 * 
 *   module TM = TreeMatch(M)
 *      
 *   let as_leaf : 'a tree -> unit m =
 *     function
 *       Lf -> Ok ()
 *     | Nd (_, _) -> Error "Leaf force failed"
 * 
 *   let as_node : 'a tree -> ('a * 'a tree_shell) m =
 *     function
 *       Lf -> Error "Node force failed"
 *     | Nd (a, sh) -> Ok (a, sh)
 * 
 *   let root_value : 'a tree -> 'a m =
 *     function
 *       Lf -> Error "No root value"
 *     | Nd (a, sh) -> Ok a
 * 
 *   let seek_to : addr -> 'a tree -> 'a tree_zipper m =
 *     fun a t -> seek a (mk_zipper t)
 *              
 *   let element_at : addr -> 'a tree -> 'a m =
 *     fun a t -> seek_to a t >>= fun z ->
 *                root_value (focus_of z)
 * 
 *   let rec split_with : 'a 'b 'c. ('a -> ('b * 'c)) -> 'a tree -> ('b tree * 'c tree) =
 *     fun f t ->
 *     match t with
 *       Lf -> (Lf, Lf)
 *     | Nd (a, sh) -> let (b , c) = f a in
 *                     let (bsh, csh) = split_with (split_with f) sh in
 *                     (Nd (b, bsh) , Nd (c, csh))
 * 
 *   let tree_unzip : 'a 'b. ('a * 'b) tree -> ('a tree * 'b tree) =
 *     fun t -> split_with (fun p -> p) t
 *                   
 *   let rec tree_fold : 'a 'b. (addr -> 'b m) -> ('a -> 'b tree -> 'b m) -> 'a tree -> 'b m =
 *     fun lr nr t ->
 *     match t with
 *       Lf -> lr []
 *     | Nd (a, Lf) -> nr a Lf
 *     | Nd (a, Nd (v, hs)) ->
 * 
 *        let unzip_and_join = (\* 'a 'b. ('b tree * addr tree) tree -> ('b tree_shell * addr tree) m *\)
 *          fun t -> let (bs, adJn) = tree_unzip t
 *                   in tree_join adJn >>= fun at -> Ok (bs, at) in
 * 
 *        let unzip_join_append = (\* 'a 'b. ('b tree * addr tree) tree -> 'b m -> ('b tree * addr tree) m *\)
 *          fun t mb -> unzip_and_join t >>= function
 *                        (bs, at) -> mb >>= fun b -> Ok (Nd (b, bs), at) in
 * 
 *        let rec fold_pass = (\* 'a 'b. 'a tree_shell -> addr -> addr tr_deriv -> ('b tree * addr tree) m *\)
 *          fun h addr d ->
 *          match h with
 *            Lf -> Ok (Lf, plug_tr_deriv d addr)
 *          | Nd (Lf, hs) -> let f = fun hbr dir deriv -> fold_pass hbr ((Dir dir) :: addr) deriv
 *                           in  traverse_with_local f hs >>= fun hr ->
 *                               unzip_join_append hr (lr addr)
 *          | Nd (Nd (a, vs), hs) -> fold_pass vs addr d >>= function
 *                                     (bs, at) -> TM.match_with_deriv fold_pass hs at >>= fun mr ->
 *                                                 unzip_join_append mr (nr a bs) in
 * 
 *        let init_horizontal = (\* 'a 'b. 'a -> 'a tree_shell tree -> ('b * addr tree) m -> ('b * addr tree) m *\)
 *          fun a h m -> m >>= function (c, at) -> TM.match_with_deriv fold_pass h at >>=
 *                                                   unzip_and_join >>= function
 *                                                   (cs, atr) -> nr a (Nd (c, cs)) >>= fun b ->
 *                                                                Ok (b , at) in
 *        
 *        let rec init_vertical = (\* 'a 'b. 'a -> 'a tree -> 'a tree_shell tree -> ('b * addr tree) m *\)
 *          fun a v h ->
 *          match v with
 *            Lf -> let h' = map_with_addr (fun _ dir -> ((Dir dir) :: [])) h
 *                  in init_horizontal a h (lr [] >>= fun b -> Ok (b, h'))
 *          | Nd (aa, Lf) -> init_horizontal a h (nr aa Lf >>= fun b -> Ok (b, map (fun _ -> []) h))
 *          | Nd (aa, Nd (vv, hh)) -> init_horizontal a h (init_vertical aa vv hh)
 * 
 *        in init_vertical a v hs >>= function (r, _) -> Ok r
 * 
 *   and tree_graft : 'a. 'a tree -> 'a tree_shell -> 'a tree m =
 *     fun t sh -> tree_fold (fun a -> element_at a sh) (fun a ash -> Ok (Nd (a, ash))) t
 * 
 *   and tree_join : 'a. 'a tree_shell -> 'a tree m =
 *     function
 *       Lf -> Ok Lf
 *     | Nd (a, ash) -> traverse tree_join ash >>= fun r ->
 *                      tree_graft a r
 *                           
 * end *)


(* module TreeMatchImpl (M : MonadError with type e = string)
 *        : MatchBase with type 'a t = 'a tree
 *        with type 'a m = 'a M.m
 *        with type ta = addr
 *        with type 'a td = 'a tr_deriv = struct
 *                    
 *   open M
 *                                   
 *   type 'a t = 'a tree
 *   type 'a m = 'a M.m
 *   type ta = addr
 *   type 'a td = 'a tr_deriv
 * 
 *   type la = addr Lazy.t
 *   type 'a ld = 'a tr_deriv Lazy.t
 *              
 *   let rec lazy_match_impl : 'a 'b 'c 'd. la -> ('a -> 'b -> la -> 'c ld -> 'd m) -> 'a t -> 'b t -> 'd t m =
 *     fun la f s t ->
 *     match (s, t) with
 *       (Lf, Lf) -> Ok Lf
 *     | (Nd (a, ash), Nd (b, bsh)) ->
 *        let f' sb tb dir drv = let lla = lazy ((Dir (Lazy.force dir)) :: (Lazy.force la))
 *                               in lazy_match_impl lla f sb tb
 *        in lazy_match_impl (lazy []) f' ash bsh >>= fun ds ->
 *           f a b la (lazy (sh_deriv ash)) >>= fun d ->
 *           Ok (Nd (d, ds))
 *     | (_, _) -> Error "Match error"
 * 
 *   let lazy_match : ('a -> 'b -> ta Lazy.t -> 'c td Lazy.t -> 'd m) -> 'a t -> 'b t -> 'd t m =
 *     fun f s t -> lazy_match_impl (lazy []) f s t
 * 
 * end
 * 
 * module TreeMatch (M : MonadError with type e = string) 
 *        : MatchTraverse with type 'a t = 'a tree
 *        with type 'a m = 'a M.m
 *        with type ta = addr
 *        with type 'a td = 'a tr_deriv = MakeMatch(M)(TreeMatchImpl(M)) *)
