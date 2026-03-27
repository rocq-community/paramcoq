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

val new_evar_compat :
  Environ.env -> Evd.evar_map -> EConstr.types -> Evd.evar_map * EConstr.t
val default_arity : int
val prime : Evd.evar_map -> int -> int -> EConstr.t -> EConstr.t
val translate_string : int -> string -> string
val translate_id : int -> Names.Id.t -> Names.Id.t
val range : (int -> 'a) -> int -> 'a list

val translate_type :
  int ->
  Evd.evar_map ref -> Environ.env -> EConstr.constr -> EConstr.constr
val translate_term :
  int ->
  Evd.evar_map ref -> Environ.env -> EConstr.constr -> EConstr.constr
val translate_constant :
  accessor:Global.indirect_accessor ->
  int ->
  Evd.evar_map ref ->
  Environ.env ->
  Names.Constant.t EConstr.puniverses ->
  (Opaqueproof.opaque, 'a) Declarations.pconstant_body ->
  Evd.econstr
val translate_mind_body :
  Names.Id.t ->
  int ->
  Evd.evar_map ref ->
  Environ.env ->
  Names.MutInd.t ->
  Declarations.mutual_inductive_body ->
  UVars.Instance.t -> Entries.mutual_inductive_entry
