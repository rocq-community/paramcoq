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

val toDecl :
  (Names.Name.t, EConstr.ERelevance.t) Context.pbinder_annot *
  EConstr.constr option * EConstr.types -> EConstr.rel_declaration
val fromDecl :
  ('a, 'b, 'c) Context.Rel.Declaration.pt ->
  (Names.Name.t, 'c) Context.pbinder_annot * 'a option * 'b

type debug_flag = [
| `Abstraction
| `Cast
| `Fix
| `Inductive
| `Module
| `ProofIrrelevance
| `Realizer
| `Time
| `Translate ]

val all :
  [> `Abstraction
   | `Case
   | `Fix
   | `GenericUnfolding
   | `Inductive
   | `Module
   | `Opacity
   | `ProofIrrelevance
   | `Realizer
   | `Relation
   | `Translate
   | `Unfolding ]
  list
val debug_flag : [> debug_flag ] list
val debug_mode : bool ref
val debug_message : [> debug_flag ] list -> string -> Pp.t -> unit
val debug_env : [> debug_flag ] list -> string -> Environ.env -> Evd.evar_map -> unit
val debug : [> debug_flag ] list -> string -> Environ.env -> Evd.evar_map -> EConstr.t -> unit
val debug_evar_map : [> debug_flag ] list -> string -> Environ.env -> Evd.evar_map -> unit
val debug_string : [> debug_flag ] list -> string -> unit
val debug_case_info : [> debug_flag ] list -> Constr.case_info -> unit
val debug_rel_context :
  [> debug_flag ] list ->
  string -> Environ.env -> Evd.evar_map -> EConstr.rel_context -> unit
val not_implemented :
  ?reason:string -> Environ.env -> Evd.evar_map -> EConstr.t -> 'a
val debug_mutual_inductive_entry :
  Evd.evar_map -> Entries.mutual_inductive_entry -> unit
