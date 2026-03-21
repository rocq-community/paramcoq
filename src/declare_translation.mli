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

val intern_reference_to_name : Libnames.qualid -> Names.GlobRef.t
val parametricity_close_proof :
  lemma:Declare.Proof.t -> pm:Declare.OblState.t -> Declare.OblState.t
val translate_inductive_command :
  int ->
  Constrexpr.constr_expr ->
  Names.Id.t -> opaque_access:Global.indirect_accessor -> unit
val realizer_command :
  opaque_access:Global.indirect_accessor ->
  int ->
  Names.Id.t option ->
  Constrexpr.constr_expr -> Constrexpr.constr_expr -> unit
val translate_module_command :
  opaque_access:Global.indirect_accessor ->
  ?name:Names.Id.t -> int -> Libnames.qualid -> unit
val command_reference :
  opaque_access:Global.indirect_accessor ->
  ?continuation:(unit -> unit) ->
  ?fullname:bool ->
  int -> Names.GlobRef.t -> Names.Id.t option -> unit
val command_reference_recursive :
  opaque_access:Global.indirect_accessor ->
  ?continuation:(unit -> unit) ->
  ?fullname:bool -> int -> Names.GlobRef.t -> unit
val translate_command :
  opaque_access:Global.indirect_accessor ->
  int -> Constrexpr.constr_expr -> Names.Id.t -> unit
