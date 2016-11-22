(*
 *  complex.ml - opetopic complexes
 *)

open Tree
open Monad
open Nesting
open Traverse
open Applicative

type 'a complex = 'a nesting list
type 'a complex_zipper = 'a nesting_zipper list

let mk_complex_zipper : 'a complex -> 'a complex_zipper =
  fun c -> List.map (fun n -> mk_nesting_zipper n) c
         
(*  You know, one idea for the zipper is the following:
    in each dimension, you could store the derivative 
    for the leaves of the given guy as a lazy value.
    This way, you would avoid having to do all the weird
    computation you do for the edge cases where you have
    dots.  The reason this makes sense is that calculating
    these guys at initialization time seems pretty easy.
    And if they were lazy, it wouldn't cost anything except
    when you used them ....
 *)

type face_addr =
  ThisDim of addr
| PrevDim of face_addr

let rec codim : face_addr -> int =
  function
    ThisDim _ -> 0
  | PrevDim fa -> codim fa + 1

let rec address_of : face_addr -> addr =
  function
    ThisDim a -> a
  | PrevDim fa -> address_of fa
                
module ComplexZipperOps (M: MonadError with type e = string) = struct

  open M

  module T = TreeOps(M)
  module N = NestingOps(M)
           
  let focus: 'a complex_zipper -> 'a nesting m =
    function
      [] -> throw "Empty complex"
    | (n, _) :: _ -> return n

  let with_focus : 'a nesting -> 'a complex_zipper -> 'a complex_zipper =
    fun n z ->
    match z with
      [] -> []
    | (_, g) :: zs -> (n, g) :: zs

  (* I think the laziness looks okay here, but it
     could use some testing ... *)
  let rec focus_deriv : 'a 'b. 'a complex_zipper -> 'b tree_deriv m =
    function
      [] -> throw "No derivative for empty zipper"
    | (fcs, ctx) :: zs ->
       match fcs with
         Dot _ -> focus_canopy zs >>= fun tc ->
                  return (sh_deriv tc)
       | Box (_, cn) -> N.canopy_spine cn >>= fun sp ->
                        focus zs >>= fun fc ->
                        N.canopy_with_guide sp (lazy (focus_deriv zs)) fc >>= fun dsh ->
                        return (sh_deriv dsh)

  and focus_canopy : 'a. 'a complex_zipper -> 'a canopy m =
    function
      [] -> throw "No canopy for empty zipper"
    | (Dot _, _) :: zs -> throw "No canopy for dot"
    | (Box (_, cn), _) :: zs -> return cn

  let focus_spine : 'a. 'a complex_zipper -> 'a tree m =
    fun z -> 
    match z with 
      [] -> throw "No spine for empty zipper"
    | (Dot a, _) :: _ -> focus_deriv z >>= fun d ->
                         return (plug_tree_deriv d a)
    | (Box (a, cn), _) :: _ -> N.canopy_spine cn

  let rec extract : 'a 'b. 'b tree -> 'a complex_zipper -> 'a complex m =
    fun g z ->
    match z with
      [] -> throw "Cannot extract from empty zipper"
    | [(fcs, ctx)] -> let f (n, _) = return [n]
                      in N.excise_with g (lazy (return (mk_deriv Lf))) fcs >>= f
    | (fcs, ctx) :: zs ->
       N.excise_with g (lazy (focus_deriv z)) fcs >>= function
         (excised, boxTr) -> let s = function
                                 Dot a -> (a, Lf)
                               | Box (a, cn) -> (a, cn) in
                             let (localSpine, compressor) = T.split_with s boxTr
                             in T.tree_join compressor >>= fun sp ->
                                extract sp zs >>= fun c ->
                                match c with
                                  [] -> throw "Empty complex in extract"
                                | ch :: ct -> let ld = lazy (focus_deriv (mk_complex_zipper c)) in
                                              N.compress_with compressor ld ch >>= fun nh ->
                                              return (excised :: nh :: ct)

  let focus_face : 'a. 'a complex_zipper -> 'a complex m =
    fun z ->
    match z with
      [] -> throw "Exmple zipper has no faces"
    | (fcs, ctx) :: zs -> focus_spine z >>= fun sp ->
           focus_deriv z >>= fun d ->
           extract sp zs >>= fun c ->
           match c with
             [] -> throw "Empty complex in face calculation"
           | ch :: ct -> let ld = lazy (focus_deriv (mk_complex_zipper c)) in
                         N.compress_with (plug_tree_deriv d sp) ld ch >>= fun nh ->
                         return ((Dot (base_value fcs)) :: nh :: ct)
       
end
                                                             
module ComplexOps (M : MonadError with type e = string) = struct

  open M

  module T = TreeOps(M)
  module TM = TreeMatch(M)
  module N = NestingOps(M)
           
  let rec check_bonds : 'a complex -> ('a tree * 'a tree_deriv) m =
    function
      [] -> return (Lf, mk_deriv Lf)  (* Dummy *)
    | [objs] -> if (is_valid_obj_nesting objs)
                then return (N.to_tree objs, mk_deriv (Nd (Lf, Lf)))
                else throw "Object nesting is not linear"
    | n :: ns -> check_bonds ns >>= function
                   (t, d) -> N.spine (lazy (return d)) n >>= fun sp ->
                             TM.match_zip t sp >>= fun _ ->
                             return (N.to_tree n, mk_deriv (as_shell sp))
        
  let rec is_bonded : 'a complex -> bool m = 
    fun c -> catch (check_bonds c) (fun _ -> return false) >>=
               fun _ -> return true

  let is_opetope : 'a complex -> bool m =
    fun c -> match c with
             | (Dot _) :: ns -> is_bonded c
             | _ ->  return false
    
end

                
