(*
 *  traverse.ml - generic traversals
 *)

open Monad
open Applicative

module type Base = sig
  type 'a t
  type 'a m
  val traverse : ('a -> 'b m) -> 'a t -> 'b t m
end

module type Traverse = sig
  include Base
  val map : ('a -> 'b) -> 'a t -> 'b t
end

module Make (S : sig type 'a s end)
            (F : functor (A: Applicative)
                 -> Base with type 'a m = 'a A.m
                    with type 'a t = 'a S.s)
            (A : Applicative) = struct

  include S
  include F(A)

  module MapInstance = F(Monad.Identity)

  let map : ('a -> 'b) -> 'a s -> 'b s =
    MapInstance.traverse
              
end

module type LocalBase = sig
        
  type 'a t
  type 'a m

  type ta
  type 'a td

  val lazy_traverse : ('a -> ta Lazy.t -> 'b td Lazy.t -> 'c m) -> 'a t -> 'c t m
    
end
                          
module type LocalTraverse = sig

  include LocalBase

  val map : ('a -> 'b) -> 'a t -> 'b t
  val map_with_addr : ('a -> ta -> 'b) -> 'a t -> 'b t
  val map_with_deriv : ('a -> 'b td -> 'c) -> 'a t -> 'c t
  val map_with_local : ('a -> ta -> 'b td -> 'c) -> 'a t -> 'c t 

  val traverse : ('a -> 'b m) -> 'a t -> 'b t m
  val traverse_with_local : ('a -> ta -> 'b td -> 'c m) -> 'a t -> 'c t m
  val traverse_with_addr : ('a -> ta -> 'b m) -> 'a t -> 'b t m
  val traverse_with_deriv : ('a -> 'b td -> 'c m) -> 'a t -> 'c t m
    
end
                  
module MakeLocal
         (S: sig type 'a s ;; type sa ;; type 'a sd end)
         (F: functor (A: Applicative) -> LocalBase with type 'a m = 'a A.m
                                         with type 'a t = 'a S.s
                                         with type ta = S.sa
                                         with type 'a td = 'a S.sd)
         (A : Applicative)
       : LocalTraverse with type 'a m = 'a A.m
       with type 'a t = 'a S.s
       with type ta = S.sa
       with type 'a td = 'a S.sd = struct

  include S
  include F(A)

  module MapInstance = F(Monad.Identity)

  let map : ('a -> 'b) -> 'a s -> 'b s =
    fun f t -> let f' a _ _ = f a
               in MapInstance.lazy_traverse f' t

  let map_with_addr : ('a -> sa -> 'b) -> 'a s -> 'b s =
    fun f t -> let f' a laddr _ = f a (Lazy.force laddr)
               in MapInstance.lazy_traverse f' t
    
  let map_with_deriv : ('a -> 'b sd -> 'c) -> 'a s -> 'c s =
    fun f t -> let f' a _ lderiv = f a (Lazy.force lderiv)
               in MapInstance.lazy_traverse f' t

  let map_with_local : ('a -> sa -> 'b sd -> 'c) -> 'a s -> 'c s =
    fun f t -> let f' a laddr lderiv = f a (Lazy.force laddr) (Lazy.force lderiv)
               in MapInstance.lazy_traverse f' t

  let traverse : ('a -> 'b m) -> 'a t -> ('b t) m =
    fun f t -> let f' a _ _ = f a
               in lazy_traverse f' t
                
  let traverse_with_addr : ('a -> sa -> 'b m) -> 'a t -> ('b t) m =
    fun f t -> let f' a laddr _ = f a (Lazy.force laddr)
               in lazy_traverse f' t

  let traverse_with_deriv : ('a -> 'b sd -> 'c m) -> 'a t -> 'c t m =
    fun f t -> let f' a _ lderiv = f a (Lazy.force lderiv)
               in lazy_traverse f' t

  let traverse_with_local : ('a -> sa -> 'b sd -> 'c m) -> 'a t -> 'c t m =
    fun f t -> let f' a laddr lderiv = f a (Lazy.force laddr) (Lazy.force lderiv)
               in lazy_traverse f' t
    
end

module type MatchBase = sig

  type 'a t
  type 'a m
  type ta
  type 'a td

  val lazy_match : ('a -> 'b -> ta Lazy.t -> 'c td Lazy.t -> 'd m) -> 'a t -> 'b t -> 'd t m

end
     
module type MatchTraverse = sig

  include MatchBase

  val match_zip : 'a t -> 'b t -> ('a * 'b) t m
  val match_traverse : ('a -> 'b -> 'c m) -> 'a t -> 'b t -> 'c t m
  val match_with_deriv : ('a -> 'b -> 'c td -> 'd m) -> 'a t -> 'b t -> 'd t m
  val match_with_addr : ('a -> 'b -> ta -> 'c m) -> 'a t -> 'b t -> 'c t m
  val match_with_local : ('a -> 'b -> ta -> 'c td -> 'd m) -> 'a t -> 'b t -> 'd t m
               
end

module MakeMatch (M: MonadError with type e = string)
                 (B : MatchBase with type 'a m = 'a M.m)
       : MatchTraverse with type 'a t = 'a B.t
       with type 'a m = 'a M.m
       with type ta = B.ta
       with type 'a td = 'a B.td = struct

  include B
  open M
     
  let match_zip : 'a t -> 'b t -> ('a * 'b) t m =
    fun s t -> lazy_match (fun a b _ _ -> return (a, b)) s t
    
  let match_traverse : ('a -> 'b -> 'c m) -> 'a t -> 'b t -> 'c t m =
    fun f s t -> let f' a b _ _ = f a b in
                 lazy_match f' s t
                 
  let match_with_deriv : ('a -> 'b -> 'c td -> 'd m) -> 'a t -> 'b t -> 'd t m =
    fun f s t -> let f' a b _ dr = f a b (Lazy.force dr) in
                 lazy_match f' s t
                 
  let match_with_addr : ('a -> 'b -> ta -> 'c m) -> 'a t -> 'b t -> 'c t m =
    fun f s t -> let f' a b ad _ = f a b (Lazy.force ad) in
                 lazy_match f' s t

  let match_with_local : ('a -> 'b -> ta -> 'c td -> 'd m) -> 'a t -> 'b t -> 'd t m =
    fun f s t -> let f' a b ad drv = f a b (Lazy.force ad) (Lazy.force drv) in
                 lazy_match f' s t
                 
end
