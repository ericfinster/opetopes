(*
 * monad.ml - monads in ocaml
 *)

module type Base = sig
  type 'a m
  val bind : 'a m -> ('a -> 'b m) -> 'b m
  val return: 'a -> 'a m
end

module type BasePlus =
sig
  include Base
  val zero : unit -> 'a m
  val plus : 'a m -> 'a m -> 'a m
  val null : 'a m -> bool
end

module type Monad = sig
  include Base
  include Applicative.Applicative with type 'a m := 'a m

  val (>>=)    : 'a m -> ('a -> 'b m) -> 'b m
  val (>=>) : ('a -> 'b m) -> ('b -> 'c m) -> ('a -> 'c m)
  val (<=<) : ('b -> 'c m) -> ('a -> 'b m) -> ('a -> 'c m)
  val join     : 'a m m -> 'a m
  val onlyif : bool -> unit m -> unit m
  val unless : bool -> unit m -> unit m
  val ignore : 'a m -> unit m
end

module type MonadPlus =
sig
  include BasePlus
  include Monad with type 'a m := 'a m
  val filter  : ('a -> bool) -> 'a m -> 'a m
  val of_list : 'a list -> 'a m
  val sum       : 'a list m -> 'a m
  val msum      : 'a m list -> 'a m
  val guard     : bool -> unit m
end
                  
module type MonadError = sig
  include Monad
  type e
  val throw : e -> 'a m
  val catch : 'a m -> (e -> 'b m) -> 'b m
end

module Make(M : Base) = struct
  include M

  let (>>=)       = bind
  let (>=>) g f x = g x >>= f
  let (<=<) f g x = g x >>= f

  let lift1 f x     = x >>= fun x -> return (f x)
  let lift2 f x y   = x >>= fun x -> lift1 (f x) y

  module Ap =
    Applicative.Make(struct
      include M
      let (<*>) f x  = lift2 (fun f x -> f x) f x
    end)

  include (Ap : Applicative.Applicative with type 'a m := 'a m)

  let join     m = m >>= (fun x -> x)
  let ignore m   = lift1 (fun _ -> ()) m
  let onlyif b m = if b then m else return ()
  let unless b m = if b then return () else m
end
  
module MakePlus(M : BasePlus) =
struct
  include Make(M)
  let zero ()  = M.zero ()
  let plus     = M.plus
  let null     = M.null
  let filter p xs =
    xs >>= fun x -> if p x then return x else zero ()
  let of_list xs = List.fold_left
    (fun x y -> plus x (return y))
    (zero  ()) xs
  let sum xs =
    xs >>=
      (fun xs -> List.fold_right plus (List.map return xs) (zero ()))
  let msum xs = List.fold_left plus (zero ()) xs

  let guard b = if b then return () else zero ()
end

module Identity : Monad with type 'a m = 'a = Make(struct
  type 'a m = 'a
  let bind a f = f a
  let return a = a
end)

module Error(E : sig type e val defaultError : e end) =
struct
  type 'a err = Error  of E.e
              | Result of 'a
  include MakePlus(struct
                    type 'a m = 'a err
                    let return x = Result x
                    let bind x f = match x with
                        Error  e -> Error e
                      | Result x -> f x
                    let zero ()  = Error E.defaultError
                    let plus x y = match x with
                        Error  e -> y
                      | Result x -> Result x
                    let null x   = match x with
                        Error _  -> true
                      | _        -> false
                  end)

  let throw e = Error e

  let catch x handler =
    match x with
      Error e  -> handler e
    | Result x -> return x

  let run_error err = err
end

                        
