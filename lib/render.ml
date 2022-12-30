(*****************************************************************************)
(*                                                                           *)
(*                    render.ml - rendering opetopes                         *) 
(*                                                                           *)
(*****************************************************************************)

open Idt
open Base

type bounding_box = 
  { pos_x : float
  ; pos_y : float
  ; height : float
  ; width : float
  }

type segment =
  { mutable start_x : float
  ; mutable start_y : float
  ; mutable end_x : float 
  ; mutable end_y : float
  }

type rendered_branch =
  { height : float
  ; left_subtree_margin : float
  ; left_internal_margin : float
  ; right_subtree_margin : float
  ; right_internal_margin : float
  ; edges : segment nst
  ; boxes : bounding_box nst tr         
  } 

type layout_config =
  { stroke_width : float
  ; internal_padding : float
  ; external_padding : float
  ; leaf_width : float
  ; corner_radius : float 
  }

let default_box =
  { pos_x = 0.0
  ; pos_y = 0.0
  ; height = 0.0
  ; width = 0.0
  }

let default_segment =
  { start_x = 0.0
  ; start_y = 0.0
  ; end_x = 0.0
  ; end_y = 0.0
  }

let empty_rendered_branch =
  { height = 0.0
  ; left_subtree_margin = 0.0
  ; left_internal_margin = 0.0
  ; right_subtree_margin = 0.0
  ; right_internal_margin = 0.0
  ; edges = Lf default_segment
  ; boxes = Lf () 
  }

module type Bounded = sig
  type el
  val bounds : el -> bounding_box
end  

module LayoutContext (B : Bounded) = struct

  open B

  (* Translate elements of a finished branch *) 
  let translate_branch br x_off y_off =
    iter_nst br.edges ~f:(fun seg ->
        seg.start_x <- seg.start_x +. x_off; 
        seg.end_x <- seg.end_x +. x_off; 
        seg.start_y <- seg.start_y +. y_off; 
        seg.end_y <- seg.end_y +. y_off 
      )
  
  let rec layout (cfg : layout_config) (nst : el nst) (lvs : rendered_branch tr) : bounding_box =
    match nst with
    | Lf lbl ->
      
      let lf_markers = nodes lvs in
      let lf_count = List.length lf_markers in
      let lbl_bounds = bounds lbl in 
      
      if (lf_count = 0) then

        (* This is a drop. Simply return the label plus any padding ... *) 
        { pos_x = 0.0
        ; pos_y = 0.0
        ; height = lbl_bounds.height +. cfg.internal_padding
        ; width = lbl_bounds.width +. cfg.internal_padding 
        }
  
      else begin

        let is_odd = (lf_count % 2) = 1 in

        let (left_branches, rem) = List.split_n lf_markers (lf_count / 2) in
        let right_branches = if is_odd then List.tl_exn rem else rem in 

        let _ = List.fold_right left_branches
            ~f:(fun br shift -> translate_branch br shift 0.0 ;
                 shift +. (br.left_subtree_margin -. br.right_subtree_margin))
            ~init:0.0 in 

        let _ = List.fold_right right_branches
            ~f:(fun br shift -> translate_branch br shift 0.0 ;
                 shift +. (br.left_subtree_margin -. br.right_subtree_margin))
            ~init:0.0 in 
        
        { pos_x = 0.0
        ; pos_y = 0.0
        ; height = lbl_bounds.height +. cfg.internal_padding
        ; width = lbl_bounds.width +. cfg.internal_padding 
        }
        
      end
        
    | Nd (_,cn) ->
      
      let _ = idt_fold cn
        (fun _ addr -> element_at lvs addr)
        (fun n ls ->
           let _ = layout cfg n ls
           in empty_rendered_branch)
  
      in default_box
        
      
end

