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

open Feedback
open Libnames
open EConstr
open Debug
open Parametricity

[@@@ocaml.warning "-40"]
let error = CErrors.user_err
let ongoing_translation = Summary.ref false ~name:"parametricity ongoing translation"
let ongoing_translation_opacity = Summary.ref false ~name:"parametricity ongoing translation opacity"
let check_nothing_ongoing () =
  if !ongoing_translation then
    error (Pp.str "Some terms are being translated, please prove pending obligations before starting a new one. End them with the command 'Parametricity Done'.")

let intern_reference_to_name qualid =
  match Constrintern.intern_reference qualid with
  | Some x -> x
  | None ->
      error Pp.(Libnames.pr_qualid qualid ++ str " does not refer to a global constant")

let obligation_message () =
  let open Pp in
  msg_notice (str "The parametricity tactic generated generated proof obligations. "
          ++  str "Please prove them and end your proof with 'Parametricity Done'. ")

let default_continuation = ignore

let parametricity_close_proof ~lemma ~pm =
  let opaque = if !ongoing_translation_opacity then Vernacexpr.Opaque else Transparent in
  ongoing_translation := false;
  let pm, _ = Declare.Proof.save ~pm ~proof:lemma ~opaque ~idopt:None in
  pm

let add_definition ~opaque ~hook ~poly ~scope ~kind ~tactic name env evd term typ =
  debug Debug.all "add_definition, term = " env evd (snd (term ( evd)));
  debug Debug.all "add_definition, typ  = " env evd typ;
  debug_evar_map Debug.all "add_definition, evd  = " env evd;
  let init_tac =
    let open Proofview in
    let typecheck = true in
    tclTHEN (Refine.refine ~typecheck begin fun sigma -> term sigma end) tactic
  in
  ongoing_translation_opacity := opaque;
  let info = Declare.Info.make ~hook ~scope ~kind ~poly () in
  let cinfo = Declare.CInfo.make ~name ~typ () in
  let lemma = Declare.Proof.start ~cinfo ~info evd in
  let lemma = Declare.Proof.map lemma ~f:(fun p ->
      let p, _, () = Proof.run_tactic Global.(env()) init_tac p in
      p)
  in
  let proof = Declare.Proof.get lemma in
  let is_done = Proof.is_done proof in
  if is_done then
    (let pm = Declare.OblState.empty in
     let _pm = parametricity_close_proof ~pm ~lemma in None)
  else begin
    ongoing_translation := true;
    obligation_message ();
    Some lemma
  end

let declare_abstraction ?(opaque = false) ?(continuation = default_continuation) ~poly ~scope ~kind arity evdr env a name =
  Debug.debug_evar_map Debug.all "declare_abstraction, evd  = " env !evdr;
  debug [`Abstraction] "declare_abstraction, a =" env !evdr a;
  let b = Retyping.get_type_of env !evdr a in
  debug [`Abstraction] "declare_abstraction, b =" env !evdr b;
  let b = Retyping.get_type_of env !evdr a in
  let b_R = relation arity evdr env b in
  let sub = range (fun k -> prime !evdr arity k a) arity in
  let b_R = EConstr.Vars.substl sub b_R in
  let a_R = fun evd ->
    let evdr = ref evd in
    let a_R = translate arity evdr env a in
    debug [`Abstraction] "a_R = " env !evdr a_R;
    debug_evar_map Debug.all "abstraction, evar_map = " env !evdr;
    !evdr, a_R
  in
  let evd = !evdr in
  let hook =
    match EConstr.kind !evdr a with
      | Const cte when
          let cte = (fst cte, EInstance.kind !evdr (snd cte)) in
          (try ignore (Relations.get_constant arity (Univ.out_punivs cte)); false with Not_found -> true)
        ->
        Declare.Hook.(make (fun { dref ; _ } ->
            if !ongoing_translation then error (Pp.str "Please use the 'Debug.Done' command to end proof obligations generated by the parametricity tactic.");
            Pp.(Flags.if_verbose msg_info (str (Printf.sprintf "'%s' is now a registered translation." (Names.Id.to_string name))));
            let cte = (fst cte, EInstance.kind !evdr (snd cte)) in
            Relations.declare_relation arity (Names.GlobRef.ConstRef (Univ.out_punivs cte)) dref;
            continuation ()))
      | _ -> Declare.Hook.(make (fun _ -> continuation ()))
  in
  let tactic = snd (Relations.get_parametricity_tactic ()) in
  add_definition ~tactic ~opaque ~poly ~scope ~kind ~hook name env evd a_R b_R

let declare_inductive name ?(continuation = default_continuation) arity evd env (((mut_ind, _) as ind, inst)) =
  let mut_body, _ = Inductive.lookup_mind_specif env ind in
  debug_string [`Inductive] "Translating mind body ...";
  let translation_entry = Parametricity.translate_mind_body name arity evd env mut_ind mut_body inst in
  debug_string [`Inductive] ("Translating mind body ... done.");
  debug_evar_map [`Inductive] "evar_map inductive " env !evd;
  let size = Declarations.(Array.length mut_body.mind_packets) in
  let mut_ind_R = DeclareInd.declare_mutual_inductive_with_eliminations translation_entry
                  (Monomorphic_entry Univ.ContextSet.empty, Names.Id.Map.empty) [] in
  for k = 0 to size-1 do
    Relations.declare_inductive_relation arity (mut_ind, k) (mut_ind_R, k)
  done;
  continuation ()

let translate_inductive_command arity c name =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, c) = Constrintern.interp_open_constr env sigma c in
  let (ind, _) as pind, _ =
    try
      Inductive.find_rectype env (to_constr sigma c)
    with Not_found ->
      error (Pp.(str "Unable to locate an inductive in " ++ Printer.pr_econstr_env env sigma c))
  in
  try
    let ind_R = Globnames.destIndRef (Relations.get_inductive arity ind) in
    error (Pp.(str "The inductive " ++ Printer.pr_inductive env ind ++ str " already as the following registered translation " ++ Printer.pr_inductive env ind_R))
  with Not_found ->
  let evd = ref sigma in
  declare_inductive name arity evd env pind

let declare_realizer ?(continuation = default_continuation) ?kind ?real arity evd env name (var : constr)  =
  let gref = (match EConstr.kind !evd var with
     | Var id -> Names.GlobRef.VarRef id
     | Const (cst, _) -> Names.GlobRef.ConstRef cst
     | _ -> error (Pp.str "Realizer works only for variables and constants.")) in
  let evd', typ = Typing.type_of env !evd var in
  evd := evd';
  let typ_R = Parametricity.relation arity evd env typ in
  let sub = range (fun _ -> var) arity in
  let typ_R = Vars.substl sub typ_R in
  let cpt = ref 0 in
  let real =
    incr cpt;
    match real with Some real -> fun sigma ->
      let (sigma, term) = real sigma in
      let realtyp = Retyping.get_type_of env sigma term in
      debug [`Realizer] (Printf.sprintf "real in realdef (%d) =" !cpt) env sigma term;
      debug [`Realizer] (Printf.sprintf "realtyp in realdef (%d) =" !cpt) env sigma realtyp;
      let sigma = Evarconv.unify_leq_delay env sigma realtyp typ_R in
      debug [`Realizer] (Printf.sprintf "real in realdef (%d), after =" !cpt) env sigma term;
      debug [`Realizer] (Printf.sprintf "realtyp in realdef (%d), after =" !cpt) env sigma realtyp;
      (sigma, term)
    | None -> fun sigma ->
      (let sigma, real = new_evar_compat env sigma typ_R in
      (sigma, real))
  in
  let scope = Locality.(Global ImportDefaultBehavior) in
  let poly = true in
  let kind = Decls.(IsDefinition Definition) in
  let name = match name with Some x -> x | _ ->
     let name_str = (match EConstr.kind !evd var with
     | Var id -> Names.Id.to_string id
     | Const (cst, _) -> Names.Label.to_string (Names.Constant.label cst)
     | _ -> assert false)
     in
     let name_R = translate_string arity name_str in
     Names.Id.of_string name_R
  in
  let sigma = !evd in
  debug_evar_map [`Realizer] "ear_map =" env sigma;
  let hook = Declare.Hook.(make (fun { dref; _ } ->
    Pp.(msg_info (str (Printf.sprintf "'%s' is now a registered translation." (Names.Id.to_string name))));
    Relations.declare_relation arity gref dref;
    continuation ())) in
  let tactic = snd (Relations.get_parametricity_tactic ()) in
  add_definition ~tactic ~opaque:false ~poly ~scope ~kind ~hook name env sigma real typ_R

let realizer_command arity name var real =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let (sigma, var) = Constrintern.interp_open_constr env sigma var in
  RetrieveObl.check_evars env sigma;
  let real = fun sigma -> Constrintern.interp_open_constr env sigma real in
  ignore(declare_realizer arity (ref sigma) env name var ~real)

let rec list_continuation final f l _ = match l with [] -> final ()
   | hd::tl -> f (list_continuation final f tl) hd

let rec translate_module_command ?name arity r  =
  check_nothing_ongoing ();
  let qid = r in
  let mb = try Global.lookup_module (Nametab.locate_module qid)
    with Not_found -> error Pp.(str "Unknown Module " ++ pr_qualid qid)
  in
  declare_module ?name arity mb

and id_of_module_path mp =
 let open Names in
 let open ModPath in
 match mp with
   | MPdot (_, lab) -> Label.to_id lab
   | MPfile dp -> List.hd (DirPath.repr dp)
   | MPbound id -> MBId.to_id id

and declare_module ?(continuation = ignore) ?name arity mb  =
  debug_string [`Module] "--> declare_module";
  let open Declarations in
  let mp = mb.mod_mp in
  match mb.mod_expr, mb.mod_type with
  | Algebraic _, NoFunctor fields
  | FullStruct, NoFunctor fields ->
     let id = id_of_module_path mp in
     let id_R = match name with Some id -> id | None -> translate_id arity id in
     debug_string [`Module] (Printf.sprintf "start module: '%s' (translating '%s')."
       (Names.Id.to_string id_R) (Names.Id.to_string id));
     let mp_R = Global.start_module id_R in
     (* I have no idea what I'm doing here : *)
     let fs = Summary.freeze_summaries ~marshallable:false in
     let _ = Lib.start_module None id_R mp_R fs in
     list_continuation
     (fun _ ->
       debug_string [`Module] (Printf.sprintf "end module: '%s'." (Names.Id.to_string id_R));
       ignore (Declaremods.end_module ()); continuation ())
     (fun continuation -> function
     | (lab, SFBconst cb) when (match cb.const_body with OpaqueDef _ -> false | Undef _ -> true | _ -> false) ->
       let cst = Mod_subst.constant_of_delta_kn mb.mod_delta (Names.KerName.make mp lab) in
       if try ignore (Relations.get_constant arity cst); true with Not_found -> false then
         continuation ()
       else
       debug_string [`Module] (Printf.sprintf "axiom field: '%s'." (Names.Label.to_string lab));
       (* As we rely on globally declared constants we need to access the
          global env here; previously indeed there was a bug in the call to
          Pfedit.get_current_context [it worked because we had no proof
          state] *)
       let env = Global.env () in
       let evd = Evd.from_env env in
       let evdr = ref evd in
       ignore(declare_realizer ~continuation arity evdr env None (mkConst cst))

     | (lab, SFBconst cb) ->
       let opaque =
         match cb.const_body with OpaqueDef _ -> true | _ -> false
       in
       let poly = Declareops.constant_is_polymorphic cb in
       let scope = Locality.(Global ImportDefaultBehavior) in
       let kind = Decls.(IsDefinition Definition) in
       let cst = Mod_subst.constant_of_delta_kn mb.mod_delta (Names.KerName.make mp lab) in
       if try ignore (Relations.get_constant arity cst); true with Not_found -> false then
         continuation ()
       else
       let env = Global.env () in
       let evd = Evd.from_env env in
       let evd, ucst =
          Evd.(with_context_set univ_rigid evd (UnivGen.fresh_constant_instance env cst))
       in
       let c = mkConstU (fst ucst, EInstance.make (snd ucst)) in
       let evdr = ref evd in
       let lab_R = translate_id arity (Names.Label.to_id lab) in
       debug [`Module] "field : " env !evdr c;
       (try
        let evd, typ = Typing.type_of env !evdr c in
        evdr := evd;
        debug [`Module] "type :" env !evdr typ
       with e -> error (Pp.str  (Printexc.to_string e)));
       debug_string [`Module] (Printf.sprintf "constant field: '%s'." (Names.Label.to_string lab));
       ignore(declare_abstraction ~opaque ~continuation ~poly ~scope ~kind arity evdr env c lab_R)

     | (lab, SFBmind _) ->
       let env = Global.env () in
       let evd = Evd.from_env env in
       let evdr = ref evd in
       let mut_ind = Mod_subst.mind_of_delta_kn mb.mod_delta (Names.KerName.make mp lab) in
       let ind = (mut_ind, 0) in
       if try ignore (Relations.get_inductive arity ind); true with Not_found -> false then
         continuation ()
       else begin
         let evd, pind =
            Evd.(with_context_set univ_rigid !evdr (UnivGen.fresh_inductive_instance env ind))
         in
         evdr := evd;
         debug_string [`Module] (Printf.sprintf "inductive field: '%s'." (Names.Label.to_string lab));
	 let ind_name = Names.Id.of_string
          @@ translate_string arity
          @@ Names.Label.to_string
          @@ Names.MutInd.label
          @@ mut_ind
	 in
         declare_inductive ind_name ~continuation arity evdr env pind
       end
     | (lab, SFBmodule mb') when
          match mb'.mod_type with NoFunctor _ ->
            (match mb'.mod_expr with FullStruct | Algebraic _ -> true | _ -> false)
          | _ -> false
        ->
        declare_module ~continuation arity mb'

     | (lab, _) ->
         Pp.(Flags.if_verbose msg_info (str (Printf.sprintf "Ignoring field '%s'." (Names.Label.to_string lab))));
          continuation ()
     ) fields ()
  | Struct _, _ -> error Pp.(str "Module " ++ (str (Names.ModPath.to_string mp))
                                 ++ str " is an interactive module.")
  | Abstract, _ -> error Pp.(str "Module " ++ (str (Names.ModPath.to_string mp))
                                 ++ str " is an abstract module.")
  | _ -> Feedback.msg_warning Pp.(str "Module " ++ (str (Names.ModPath.to_string mp))
                                 ++ str " is not a fully-instantiated module.");
         continuation ()


let command_variable ?(continuation = default_continuation) arity variable names =
  error (Pp.str "Cannot translate an axiom nor a variable. Please use the 'Parametricity Realizer' command.")

let translateFullName ~fullname arity (kername : Names.KerName.t) : string =
  let nstr =
    (translate_string arity
     @@ Names.Label.to_string
     @@ Names.KerName.label
     @@ kername)in 
  let pstr =
    (Names.ModPath.to_string
     @@ Names.KerName.modpath
     @@ kername) in
  let plstr = Str.split (Str.regexp ("\\.")) pstr in
  if fullname then
    (String.concat "_o_" (plstr@[nstr]))
  else nstr

let command_constant ?(continuation = default_continuation) ~fullname arity constant names =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let poly, opaque =
    let cb = Global.lookup_constant constant in
    let open Declarations in
    Declareops.constant_is_polymorphic cb,
    (match cb.const_body with Def _ -> false | _ -> true)
  in
  let name = match names with
      | None -> Names.Id.of_string
                @@ translateFullName ~fullname arity
                @@ Names.Constant.canonical
                @@ constant
      | Some name -> name
  in
  let scope = Locality.(Global ImportDefaultBehavior) in
  let kind = Decls.(IsDefinition Definition) in
  let evd, pconst =
    Evd.(with_context_set univ_rigid evd (UnivGen.fresh_constant_instance env constant))
  in
  let constr = mkConstU (fst pconst, EInstance.make @@ snd pconst) in
  declare_abstraction ~continuation ~opaque ~poly ~scope ~kind arity (ref evd) env constr name

let command_inductive ?(continuation = default_continuation) ~fullname arity inductive names =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evd, pind =
    Evd.(with_context_set univ_rigid evd (UnivGen.fresh_inductive_instance env inductive))
  in
  let name = match names with
      | None ->
             Names.Id.of_string
          @@ translateFullName ~fullname arity
          @@ Names.MutInd.canonical
          @@ fst
	  @@ fst
	  @@ pind
      | Some name -> name
  in
  declare_inductive name ~continuation arity (ref evd) env pind

let command_constructor ?(continuation = default_continuation) arity gref names =
  let open Pp in
  error ((str "'")
        ++ (Printer.pr_global gref)
        ++ (str "' is a constructor. To generate its parametric translation, please translate its inductive first."))

let command_reference ?(continuation = default_continuation) ?(fullname = false) arity gref names =
   check_nothing_ongoing ();
   let open Names.GlobRef in
   (* We ignore proofs for now *)
   let _pstate = match gref with
   | VarRef variable ->
     command_variable ~continuation arity variable names
   | ConstRef constant ->
     command_constant ~continuation ~fullname arity constant names
   | IndRef inductive ->
     command_inductive ~continuation ~fullname arity inductive names;
     None
   | ConstructRef constructor ->
     command_constructor ~continuation arity gref names
   in ()

let command_reference_recursive ?(continuation = default_continuation) ?(fullname = false) arity gref =
  let open Globnames in
  let gref= Globnames.canonical_gr gref in
  let label = Names.Label.of_id (Nametab.basename_of_global gref) in
  let c = printable_constr_of_global gref in
  let (direct, graph, _) = Assumptions.traverse label c in
  let inductive_of_constructor ref =
    let open Globnames in
    let ref= Globnames.canonical_gr ref in
    if not (isConstructRef ref) then ref else
     let (ind, _) = Globnames.destConstructRef ref in
     Names.GlobRef.IndRef ind
  in
  let rec fold_sort graph visited nexts f acc =
    Names.GlobRef.Set_env.fold (fun ref ((visited, acc) as visacc) ->
          let ref_ind = inductive_of_constructor ref in
          if Names.GlobRef.Set_env.mem ref_ind visited
          || Relations.is_referenced arity ref_ind  then visacc else
          let nexts = Names.GlobRef.Map_env.find ref graph in
          let visited = Names.GlobRef.Set_env.add ref_ind visited in
          let visited, acc = fold_sort graph visited nexts f acc in
          let acc = f ref_ind acc in
          (visited, acc)
     ) nexts (visited, acc)
  in
  let _, dep_refs = fold_sort graph Names.GlobRef.Set_env.empty direct (fun x l -> (inductive_of_constructor x)::l) [] in
  let dep_refs = List.rev dep_refs in
  (* DEBUG: *)
  (* Pp.(msg_info (str "DepRefs:"));
   * List.iter (fun x -> msg_info (Printer.pr_global x)) dep_refs; *)
  list_continuation continuation (fun continuation gref ->
      command_reference ~continuation ~fullname arity gref None) dep_refs ()

let translate_command arity c name =
  if !ongoing_translation then error (Pp.str "On going translation.");
  (* Same comment as above *)
  let env = Global.env () in
  let evd = Evd.from_env env in
  let (evd, c) = Constrintern.interp_open_constr env evd c in
  let cte_option =
    match kind evd c with Const cte -> Some cte | _ -> None
  in
  let poly, opaque =
    match cte_option with
    | Some (cte, _) ->
        let cb = Global.lookup_constant cte in
        Declarations.((* cb.const_polymorphic, *) false,
             match cb.const_body with Def _ -> false
                                        | _ -> true)
    | None -> false, false
  in
  let scope = Locality.(Global ImportDefaultBehavior) in
  let kind = Decls.(IsDefinition Definition) in
  let _ : Declare.Proof.t option = declare_abstraction ~opaque ~poly ~scope ~kind arity (ref evd) env c name in
  ()
