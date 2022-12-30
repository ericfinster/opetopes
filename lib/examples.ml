(*****************************************************************************)
(*                                  Examples                                 *)
(*****************************************************************************)

open Idt
open Complex     

let obj : int cmplx =
  ~> (Lf 0)

let arrow : int cmplx =
  ~> (Nd (1, Nd (Lf 0, Lf ())))
  |> (Lf 2)

let loop : int cmplx =
  ~> (Lf 0)
  |> (Nd (1, Lf ()))
  |> (Lf 2)  

let disc : int cmplx =
  ~> (Nd (1, Nd (Lf 0, Lf ())))
  |> (Nd (3, Nd (Lf 2, Nd (Lf (), Lf ()))))
  |> (Lf 4)  

let simplex : int cmplx =
  ~> (Nd (2, Nd (Nd (1, Nd (Lf 0, Lf ())), Lf ())))
  |> (Nd (5, Nd (Lf 4, Nd (Nd (Lf 3, Nd (Lf (), Lf ())), Lf ()))))
  |> (Lf 6)  

let lefty : int cmplx =
  ~> (Nd (2, Nd (Nd (1, Nd (Lf 0, Lf ())), Lf ())))
  |> (Nd (6, Nd (Lf 5, Nd (Nd (Nd (4, Nd (Lf 3, Nd (Lf (), Lf ()))), Nd (Lf (), Lf ())), Lf ()))))
  |> (Nd (9, Nd (Lf 8, Nd (Lf (), Nd (Nd (Nd (Lf 7, Nd (Lf (), Nd (Lf (), Lf ()))), Nd (Lf (), Lf ())), Lf ())))))
  |> (Lf 10)  

let bigguy : int cmplx = 
  ~> (Nd (2, Nd (Nd (1, Nd (Lf 0, Lf ())), Lf ())))
  |> (Nd (8, Nd (Nd (7, Nd (Lf 6, Nd (Nd (Nd (5, Lf ()), Nd (Lf (), Lf ())), Lf ()))),
                 Nd (Nd (Nd (4, Nd (Lf 3, Nd (Lf (), Lf ()))), Nd (Lf (), Lf ())), Lf ()))))
  |> (Nd (14, Nd (Nd (13, Nd (Lf 12, Nd (Nd (Lf 11, Nd (Lf (), Nd (Nd (Lf (), Nd (Lf (), Lf ())), Lf ()))),
                                         Nd (Nd (Lf (), Nd (Lf (), Lf ())), Lf ())))),
                  Nd (Lf (), Nd (Nd (Nd (Lf 10, Lf ()), Nd (Nd (Nd (Lf 9, Nd (Lf (), Nd (Lf (), Lf ()))), Nd (Lf (), Lf ())), Lf ())), Lf ())))))
  |> (Nd (18, Nd (Lf 17, Nd (Nd (Lf 16, Nd (Lf (), Nd (Nd (Lf (), Nd (Lf (), Nd (Nd (Lf (), Nd (Lf (), Lf ())), Lf ()))),
                                                       Nd (Nd (Lf (), Nd (Lf (), Lf ())), Lf ())))),
                             Nd (Lf (), Nd (Nd (Nd (Lf (), Lf ()),
                                                Nd (Nd (Nd (Nd (Nd (15, Lf ()), Nd (Lf (), Nd (Lf (), Nd (Lf (), Lf ())))),
                                                            Nd (Lf (), Nd (Lf (), Lf ()))), Nd (Lf (), Lf ())), Lf ())), Lf ()))))))
  |> (Nd (21, Nd (Lf 20, Nd (Lf (), Nd (Nd (Lf (), Nd (Lf (), Nd (Nd (Lf (), Nd (Lf (), Nd (Nd (Lf (), Nd (Lf (), Lf ())), Lf ()))),
                                                                  Nd (Nd (Lf (), Nd (Lf (), Lf ())), Lf ())))),
                                        Nd (Lf (), Nd (Nd (Nd (Lf (), Lf ()),
                                                           Nd (Nd (Nd (Nd (Nd (Lf 19, Lf ()),
                                                                           Nd (Lf (), Nd (Lf (), Nd (Lf (), Lf ())))),
                                                                       Nd (Lf (), Nd (Lf (), Lf ()))), Nd (Lf (), Lf ())), Lf ())), Lf ())))))))
  |> (Lf 22)
