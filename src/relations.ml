(**************************************************************************)
(*                                                                        *)
(*     ParamCoq                                                           *)
(*     Copyright (C) 2012 - 2018                                          *)
(*                                                                        *)
(*     See the AUTHORS file for the list of contributors                  *)
(*                                                                        *)
(*   This file is distributed under the terms of the MIT License          *)
(*                                                                        *)
(**************************************************************************)


open Names
open Globnames
open Libobject

let (set_parametricity_tactic, get_parametricity_tactic, print_parametricity_tactic) = 
    Tactic_option.declare_tactic_option "Parametricity tactic"

module IntMap = Map.Make(Int)
module GMap = GlobRef.Map


let initial_translations = GMap.empty
let initial_relations = IntMap.empty

let relations = Summary.ref initial_relations ~name:"parametricity"

let print_relations () = 
  IntMap.iter (fun n translations -> 
   GMap.iter (fun gref c -> Feedback.(msg_info (Printer.pr_global gref))) translations
  ) !relations

let add (n : int) f = 
  let translations =
    try IntMap.find n !relations with Not_found -> initial_translations
  in
  relations := IntMap.add n (f translations) !relations

let cache_relation (n, x, x_R) =
  add n (GMap.add x x_R)

let discharge_relation (n, x, x_R) =
  Some (n, x, x_R)

let subst_relation (subst, (n, x, x_R)) = 
    (n, subst_global_reference subst x, subst_global_reference subst x_R)

let in_relation = declare_object {(default_object "PARAMETRICITY") with 
                   cache_function = cache_relation;
                   load_function = (fun _ -> cache_relation);
                   subst_function = subst_relation;
                   classify_function = (fun obj -> Substitute);
                   discharge_function = discharge_relation}
 
let declare_relation n x x_R = 
 Lib.add_leaf (in_relation (n, x, x_R))
 
let declare_constant_relation (n : int) (c : Constant.t) (c_R : Constant.t) =
  declare_relation n (GlobRef.ConstRef c) (GlobRef.ConstRef c_R)

let declare_inductive_relation (n : int) (i : inductive) (i_R : inductive) = 
  declare_relation n (GlobRef.IndRef i) (GlobRef.IndRef i_R)

let declare_variable_relation (n : int) (v : variable) (v_R : Constant.t) =
  declare_relation n (GlobRef.VarRef v) (GlobRef.ConstRef v_R)

let get_constant n c = 
  let map = IntMap.find n !relations in
  GMap.find (GlobRef.ConstRef c) map

let get_inductive n i = 
  let map = IntMap.find n !relations in
  GMap.find (GlobRef.IndRef i) map

let get_variable n v = 
  let map = IntMap.find n !relations in
  destConstRef (GMap.find (GlobRef.VarRef v) map)
  
let is_referenced n ref = 
  try
    let map = IntMap.find n !relations in 
    GMap.mem ref map
  with Not_found -> false
