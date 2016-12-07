(*
 *  nesting.ml - nestings in ocaml
 *)

open Tree
open Monad
open Traverse
open Applicative

type 'a nesting = ('a, 'a) gtree

let base_value : 'a nesting -> 'a =
  function
    Lf a -> a
  | Nd (a, _) -> a

let with_base : 'a -> 'a nesting -> 'a nesting =
  fun a n ->
  match n with
    Lf _ -> Lf a
  | Nd (_, cn) -> Nd (a, cn)

let rec is_valid_obj_nesting : 'a nesting -> bool =
  function
    Lf _ -> true
  | Nd (_, Nd (n, Lf ())) -> is_valid_obj_nesting n
  | _ -> false
       
type 'a canopy = ('a, 'a) gtree_shell
type 'a nesting_ctxt = ('a, 'a) gtree_ctxt
type 'a nesting_deriv = ('a, 'a) gtree_deriv
type 'a nesting_zipper = ('a, 'a) gtree_zipper

let mk_nesting_zipper : 'a nesting -> 'a nesting_zipper =
  fun n -> (n, TrG [])
         
let rec plug_nesting_deriv : 'a. 'a nesting_deriv -> 'a -> 'a nesting =
  fun d a ->
  match d with
    TrD (cn, g) -> close_nesting_ctxt g (Nd (a, cn))

and close_nesting_ctxt : 'a. 'a nesting_ctxt -> 'a nesting -> 'a nesting =
  fun g n ->
  match g with
    TrG [] -> n
  | TrG ((a,d)::gs) -> close_nesting_ctxt (TrG gs) (Nd (a, plug_tree_deriv d n))
                       
module NestingZipperOps (M: MonadError with type e = string) = struct

  open M
  module TZ = TreeZipperOps(M)
  module T = TreeOps(M)
            
  let focus_of : 'a nesting_zipper -> 'a nesting =
    function (fcs, _) -> fcs
           
  let close : 'a nesting_zipper -> 'a nesting =
    function (fcs, g) -> close_nesting_ctxt g fcs

  let close_with : 'a nesting -> 'a nesting_zipper -> 'a nesting =
    fun n z ->
    match z with
      (_, g) -> close_nesting_ctxt g n

  let visit : dir -> 'a nesting_zipper -> 'a nesting_zipper m =
    fun d z -> 
    match (z, d) with
      ((Lf _, _), _) -> throw "Encountered dot in nesting visit"
    | ((Nd (a, cn), TrG ctxt), Dir ds) ->
       T.seek_to ds cn >>= function
         (Lf (), _) -> throw "Encountered leaf in nesting visit"
       | (Nd (n, sh), g) -> return (n, TrG ((a, TrD (sh, g)) :: ctxt))

  let rec seek : addr -> 'a nesting_zipper -> 'a nesting_zipper m =
    fun addr z ->
    match addr with
      [] -> return z
    | d :: ds -> seek ds z >>= fun zz ->
                 visit d zz 

  let sibling : dir -> 'a nesting_zipper -> 'a nesting_zipper m =
    fun d z ->
    match (d, z) with
      (_, (_, TrG [])) -> throw "No sibling in empty context"
    | (Dir dir, (fcs, TrG ((a, TrD (vs, TrG hcn)) :: cs))) ->
       T.seek_to dir vs >>= fun vzip ->
       match vzip with
         (Lf (), _) -> throw "Leaf in sibling"
       | (Nd (Lf (), _), _) -> throw "Leaf in sibling"
       | (Nd (Nd (nfcs, vrem), hmask), ctxt) ->
          let drv = TrD (vrem, TrG ((fcs, TrD (hmask, ctxt)) :: hcn))
          in return (nfcs, TrG ((a, drv) :: cs))
       
  let parent : 'a nesting_zipper -> 'a nesting_zipper m =
    function
      (fcs, TrG []) -> throw "No parent in empty context"
    | (fcs, TrG ((a, d) :: cs)) -> return (Nd (a, plug_tree_deriv d fcs), TrG cs)
       
  let predecessor : 'a nesting_zipper -> 'a nesting_zipper m =
    function
      (fcs, TrG ((a, TrD (verts, TrG ((pred, deriv) :: vs))) :: cs)) ->
      let drv = TrD (plug_tree_deriv deriv (Nd (fcs, verts)), TrG vs)
      in return (pred, TrG ((a, drv) :: cs))
    | _ -> throw "No predecessor"

  let rec predecessor_which : ('a -> bool) -> 'a nesting_zipper -> 'a nesting_zipper m =
    fun f z -> if (f (base_value (focus_of z)))
               then return z
               else predecessor z >>= predecessor_which f 
              
end

module NestingTraverseImpl (A : Applicative) : LocalBase
       with type 'a t = 'a nesting
       with type 'a m = 'a A.m
       with type ta = addr
       with type 'a td = 'a tree_deriv = struct
    
  open A

  module T = TreeTraverse(A)
     
  type 'a t = 'a nesting
  type 'a m = 'a A.m
  type ta = addr
  type 'a td = 'a tree_deriv
             
  type la = addr Lazy.t
  type 'a ld = 'a tree_deriv Lazy.t

  let mkDot a = Lf a
  let mkBox a cn = Nd (a, cn)
                 
  let rec lazy_traverse_impl : 'a 'b 'c. la -> 'b ld -> ('a -> la -> 'b ld -> 'c m) -> 'a t -> 'c t m =
    fun ba bd f n ->
    match n with
      Lf a -> mkDot <$> (f a ba bd)
    | Nd (a, cn) -> let r = f a ba bd in
                     let f' nn la ld =
                       let lla = lazy ((Dir (Lazy.force la)) :: (Lazy.force ba))
                       in lazy_traverse_impl lla ld f n in
                     let rc = T.lazy_traverse f' cn
                     in mkBox <$> r <*> rc

  let lazy_traverse : 'a 'b 'c. ('a -> la -> 'b ld -> 'c m) -> 'a t -> 'c t m =
    fun f t -> lazy_traverse_impl (lazy []) (lazy (mk_deriv (Nd (Lf (), Lf ())))) f t

end

module NestingTraverse (A : Applicative) : LocalTraverse
       with type 'a t = 'a nesting
       with type 'a m = 'a A.m
       with type ta = addr
       with type 'a td = 'a tree_deriv
                         = MakeLocal
                             (struct
                               type 'a s = 'a nesting
                               type sa = addr
                               type 'a sd = 'a tree_deriv
                             end)(NestingTraverseImpl)(A)

module NestingMatchImpl (M : MonadError with type e = string)
       : MatchBase with type 'a t = 'a nesting
       with type 'a m = 'a M.m
       with type ta = addr
       with type 'a td = 'a tree_deriv = struct
                   
  open M
  module TM = TreeMatch(M)
                                  
  type 'a t = 'a nesting
  type 'a m = 'a M.m
  type ta = addr
  type 'a td = 'a tree_deriv

  type la = addr Lazy.t
  type 'a ld = 'a tree_deriv Lazy.t
             
  let rec lazy_match_impl : 'a 'b 'c 'd. la -> 'c ld -> ('a -> 'b -> la -> 'c ld -> 'd m) -> 'a t -> 'b t -> 'd t m =
    fun la ld f m n ->
    match (m, n) with
      (Lf a, Lf b) -> f a b la ld >>= fun d -> return (Lf d)
    | (Nd (a, acn), Nd (b, bcn)) -> 
       let f' mm nn dir drv = let lla = lazy ((Dir (Lazy.force dir)) :: (Lazy.force la))
                              in lazy_match_impl lla drv f mm nn
       in TM.lazy_match f' acn bcn >>= fun dcn ->
          f a b la ld >>= fun d ->
          return (Nd (d, dcn))
    | _ -> throw "Mismatch in nesting"

  let lazy_match : ('a -> 'b -> ta Lazy.t -> 'c td Lazy.t -> 'd m) -> 'a t -> 'b t -> 'd t m =
    fun f s t -> lazy_match_impl (lazy []) (lazy (mk_deriv (Nd (Lf (), Lf ())))) f s t

end

module NestingMatch (M : MonadError with type e = string) 
       : MatchTraverse with type 'a t = 'a nesting
       with type 'a m = 'a M.m
       with type ta = addr
       with type 'a td = 'a tree_deriv = MakeMatch(M)(NestingMatchImpl(M))
     
module NestingOps (M: MonadError with type e = string) = struct
  open M

  module TT = TreeTraverse(M)
  module TM = TreeMatch(M)
  module T = TreeOps(M)

  let as_dot : 'a nesting -> 'a m = 
    function
      Lf a -> return a
    | _ -> throw "Not a dot"

  let as_box : 'a nesting -> ('a * 'a canopy) m =
    function
      Nd (a, cn) -> return (a, cn)
    | _ -> throw "Not a box"

  let rec fold_nesting : ('a -> 'b) -> ('a -> 'b tree -> 'b) -> 'a nesting -> 'b =
    fun dr br n ->
    match n with
      Lf a -> dr a
    | Nd (a, cn) -> br a (TT.map (fold_nesting dr br) cn)

  let to_tree : 'a nesting -> 'a tree = 
    fun n -> fold_nesting (fun _ -> Lf ()) (fun a sh -> Nd (a, sh)) n

  type 'a ldm = 'a tree_deriv m Lazy.t
              
  let rec spine : 'a ldm -> 'a nesting -> 'a tree m =
    fun ldm n ->
    match n with
      Lf a -> Lazy.force ldm >>= fun d -> return (plug_tree_deriv d a)
    | Nd (a, cn) -> canopy_spine cn
  and canopy_spine : 'a canopy -> 'a tree m =
    fun cn -> let f nst _ drv = spine (lazy (return (Lazy.force drv))) nst 
              in TT.lazy_traverse f cn >>= T.tree_join

  let rec total_canopy : 'a nesting ldm -> 'a nesting -> 'a canopy m =
    fun ldm n ->
    match n with
      Lf a -> Lazy.force ldm >>= fun d -> return (plug_tree_deriv d (Lf a))
    | Nd (a, cn) ->
       let f nst _ drv = total_canopy (lazy (return (Lazy.force drv))) nst
       in TT.lazy_traverse f cn >>= T.tree_join
                   
  let rec canopy_with_guide : 'b tree -> 'a nesting ldm -> 'a nesting -> 'a canopy m =
    fun g ldm n ->
    match (n, g) with
      (_, Lf ()) -> Lazy.force ldm >>= fun d -> return (plug_tree_deriv d n)
    | (Nd (_, cn), Nd (_, sh)) ->
       let f nn gg _ dd = canopy_with_guide gg (lazy (return (Lazy.force dd))) nn
       in TM.lazy_match f cn sh >>= T.tree_join
    | _ -> throw "Bad canopy"
         
  let rec excise_with : 'b tree -> 'a nesting ldm -> 'a nesting -> ('a nesting * 'a canopy) m =
    fun g ldm n ->
    match (n, g) with
      (_, Lf ()) -> let v = base_value n
                 in total_canopy ldm n >>= fun cn ->
                    Lazy.force ldm >>= fun d -> 
                    return (Lf v, plug_tree_deriv d (Nd (v, cn)))
    | (Nd (a, cn), Nd (_, sh)) ->
       let f nn tt _ dd = excise_with tt (lazy (return (Lazy.force dd))) nn
       in TM.lazy_match f cn sh >>= fun p ->
          let (ncn, toJn) = T.tree_unzip p
          in T.tree_join toJn >>= fun jn ->
             return (Nd (a, ncn), jn)
    | _ -> throw "Error during excision"
         
  let rec compress_with : 'b tree_shell -> 'a nesting ldm -> 'a nesting -> 'a nesting m =
    fun s ldm n ->
    match s with
      Nd (Lf (), sh) -> T.root_value sh >>= fun r ->
                     compress_with r ldm n >>= fun nn ->
                     Lazy.force ldm >>= fun d -> 
                     return (Nd (base_value n, plug_tree_deriv d nn))
    | Nd (sk, sh) -> canopy_with_guide sk ldm n >>= fun cn ->
                     let f nn gg _ dd = compress_with gg (lazy (return (Lazy.force dd))) nn
                     in TM.lazy_match f cn sh >>= fun rn ->
                        return (Nd (base_value n, rn))
    | Lf () -> return n
         
end
