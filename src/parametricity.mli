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
module CoqConstants :
  sig
    val msg : string
    val eq_refl :
      Environ.env ->
      Evd.evar_map ref -> EConstr.constr array -> EConstr.constr
  end
val default_arity : int
val hyps_from_rel_context : Environ.env -> int list
val prime : Evd.evar_map -> int -> int -> EConstr.t -> EConstr.t
val translate_string : int -> string -> string
val translate_id : int -> Names.Id.t -> Names.Id.t
val range : (int -> 'a) -> int -> 'a list
val firsts : int -> 'a list -> 'a list
val substl_rel_context :
  EConstr.Vars.substl ->
  EConstr.rel_declaration list -> EConstr.rel_declaration list
val generalize_env : Environ.env -> EConstr.types -> EConstr.t
val abstract_env : Environ.env -> EConstr.constr -> EConstr.t
val mkFreshInd :
  Environ.env -> Evd.evar_map ref -> Names.inductive -> EConstr.t
val mkFreshConstruct :
  Environ.env -> Evd.evar_map ref -> Names.constructor -> EConstr.t

module WithOpaqueAccess :
  functor (Access : sig val access : Global.indirect_accessor end) ->
    sig
      val relation :
        int ->
        Evd.evar_map ref -> Environ.env -> EConstr.constr -> EConstr.constr
      val translate :
        int ->
        Evd.evar_map ref -> Environ.env -> EConstr.constr -> EConstr.constr
      val get_arity : Constr.types -> Constr.rel_context
      val translate_mind_body :
        Names.Id.t ->
        int ->
        Evd.evar_map ref ->
        Environ.env ->
        Names.MutInd.t ->
        Declarations.mutual_inductive_body ->
        UVars.Instance.t -> Entries.mutual_inductive_entry
    end
