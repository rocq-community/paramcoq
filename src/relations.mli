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

val set_parametricity_tactic :
  ?loc:Loc.t ->
  Tactic_option.tac_option_locality -> Gentactic.glob_generic_tactic -> unit
val get_parametricity_tactic : unit -> unit Proofview.tactic
val print_parametricity_tactic : unit -> Pp.t
val print_relations : unit -> unit
val declare_relation : int -> GlobRef.t -> Names.GlobRef.t -> unit
val declare_constant_relation :
  int -> Names.Constant.t -> Names.Constant.t -> unit
val declare_inductive_relation :
  int -> Names.inductive -> Names.inductive -> unit
val declare_variable_relation :
  int -> Names.variable -> Names.Constant.t -> unit
val get_constant : int -> Names.Constant.t -> Names.GlobRef.t
val get_inductive : int -> Names.inductive -> Names.GlobRef.t
val get_variable : int -> Names.variable -> Names.Constant.t
val is_referenced : int -> GlobRef.t -> bool
