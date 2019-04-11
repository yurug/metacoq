open Univ
open Names
open Constr_quoter
open Pp

open Quoter


let resolve_symbol_p (path : string list) (tm : string) : global_reference =
  Coqlib.gen_reference_in_modules contrib_name [path] tm

let pkg_template_monad_prop = ["Template";"TemplateMonad";"Core"]
let pkg_template_monad_type = ["Template";"TemplateMonad";"Extractable"]

let r_template_monad_prop_p = resolve_symbol_p pkg_template_monad_prop
let r_template_monad_type_p = resolve_symbol_p pkg_template_monad_type


(* for "Core" *)
let (ptmReturn,
     ptmBind,

     ptmPrint,
     ptmMsg,
     ptmFail,

     ptmEval,

     ptmDefinitionRed,
     ptmLemmaRed,
     ptmAxiomRed,
     ptmMkDefinition,
     ptmMkInductive,

     ptmFreshName,

     ptmAbout,
     ptmCurrentModPath,

     ptmQuote,
     ptmQuoteRec,
     ptmQuoteInductive,
     ptmQuoteConstant,
     ptmQuoteUniverses,

     ptmUnquote,
     ptmUnquoteTyped,

     ptmInferInstance,
     ptmExistingInstance,

     ptmTestQuote,
     ptmQuoteDefinition,
     ptmQuoteDefinitionRed,
     ptmQuoteRecDefinition) =
  (r_template_monad_prop_p "tmReturn",
   r_template_monad_prop_p "tmBind",

   r_template_monad_prop_p "tmPrint",
   r_template_monad_prop_p "tmMsg",
   r_template_monad_prop_p "tmFail",

   r_template_monad_prop_p "tmEval",

   r_template_monad_prop_p "tmDefinitionRed",
   r_template_monad_prop_p "tmLemmaRed",
   r_template_monad_prop_p "tmAxiomRed",
   r_template_monad_prop_p "tmMkDefinition",
   r_template_monad_prop_p "tmMkInductive",

   r_template_monad_prop_p "tmFreshName",

   r_template_monad_prop_p "tmAbout",
   r_template_monad_prop_p "tmCurrentModPath",

   r_template_monad_prop_p "tmQuote",
   r_template_monad_prop_p "tmQuoteRec",
   r_template_monad_prop_p "tmQuoteInductive",
   r_template_monad_prop_p "tmQuoteConstant",
   r_template_monad_prop_p "tmQuoteUniverses",

   r_template_monad_prop_p "tmUnquote",
   r_template_monad_prop_p "tmUnquoteTyped",

   r_template_monad_prop_p "tmInferInstance",
   r_template_monad_prop_p "tmExistingInstance",

   r_template_monad_prop_p "tmTestQuote",
   r_template_monad_prop_p "tmQuoteDefinition",
   r_template_monad_prop_p "tmQuoteDefinitionRed",
   r_template_monad_prop_p "tmQuoteRecDefinition")

(* for "Extractable" *)
let (ttmReturn,
     ttmBind,
     ttmPrintTerm,
     ttmMsg,
     ttmFail,
     ttmEval,

     ttmDefinition,
     ttmAxiom,
     ttmLemma,
     ttmFreshName,
     ttmAbout,
     ttmCurrentModPath,
     ttmQuoteInductive,
     ttmQuoteConstant,
     ttmQuoteUniverses,
     ttmInductive,
     ttmInferInstance,
     ttmExistingInstance) =
  (r_template_monad_type_p "tmReturn",
   r_template_monad_type_p "tmBind",

   r_template_monad_type_p "tmPrint",
   r_template_monad_type_p "tmMsg",
   r_template_monad_type_p "tmFail",
   r_template_monad_type_p "tmEval",

   r_template_monad_type_p "tmDefinition",
   r_template_monad_type_p "tmAxiom",
   r_template_monad_type_p "tmLemma",

   r_template_monad_type_p "tmFreshName",

   r_template_monad_type_p "tmAbout",
   r_template_monad_type_p "tmCurrentModPath",

   r_template_monad_type_p "tmQuoteInductive",
   r_template_monad_type_p "tmQuoteUniverses",
   r_template_monad_type_p "tmQuoteConstant",

   r_template_monad_type_p "tmInductive",

   r_template_monad_type_p "tmInferInstance",
   r_template_monad_type_p "tmExistingInstance")

type constr = Constr.t

type template_monad =
    TmReturn of Constr.t
  | TmBind  of Constr.t * Constr.t

    (* printing *)
  | TmPrint of Constr.t      (* only Prop *)
  | TmPrintTerm of Constr.t  (* only Extractable *)
  | TmMsg of Constr.t
  | TmFail of Constr.t

    (* evaluation *)
  | TmEval of Constr.t * Constr.t      (* only Prop *)
  | TmEvalTerm of Constr.t * Constr.t  (* only Extractable *)

    (* creating definitions *)
  | TmDefinition of Constr.t * Constr.t * Constr.t * Constr.t
  | TmDefinitionTerm of Constr.t * Constr.t * Constr.t
  | TmLemma of Constr.t * Constr.t * Constr.t
  | TmLemmaTerm of Constr.t * Constr.t
  | TmAxiom of Constr.t * Constr.t * Constr.t
  | TmAxiomTerm of Constr.t * Constr.t
  | TmMkDefinition of Constr.t * Constr.t
  | TmMkInductive of Constr.t

  | TmFreshName of Constr.t

  | TmAbout of Constr.t
  | TmCurrentModPath

    (* quoting *)
  | TmQuote of bool * Constr.t  (* only Prop *)
  | TmQuoteInd of Constr.t
  | TmQuoteConst of Constr.t * Constr.t
  | TmQuoteUnivs

  | TmUnquote of Constr.t                   (* only Prop *)
  | TmUnquoteTyped of Constr.t * Constr.t (* only Prop *)

    (* typeclass resolution *)
  | TmExistingInstance of Constr.t
  | TmInferInstance of Constr.t * Constr.t (* only Prop *)
  | TmInferInstanceTerm of Constr.t        (* only Extractable *)

(* todo: the recursive call is uneeded provided we call it on well formed terms *)
let rec app_full trm acc =
  match Constr.kind trm with
    Constr.App (f, xs) -> app_full f (Array.to_list xs @ acc)
  | _ -> (trm, acc)

let monad_failure s k =
  CErrors.user_err  Pp.(str s ++ str " must take " ++ int k ++
                        str " argument" ++ str (if k > 0 then "s" else "") ++ str "." ++ fnl () ++
                        str "Please file a bug with MetaCoq.")

let next_action env evd (pgm : constr) : template_monad * _ =
  let pgm = Reduction.whd_all env pgm in
  let (coConstr, args) = app_full pgm [] in
  let (glob_ref, universes) =
    try
      let open Constr in
      match kind coConstr with
      | Const (c, u) -> ConstRef c, u
      | Ind (i, u) -> IndRef i, u
      | Construct (c, u) -> ConstructRef c, u
      | Var id -> VarRef id, Instance.empty
      | _ -> raise Not_found
    with _ ->
      CErrors.user_err (str "Invalid argument or not yet implemented. The argument must be a TemplateProgram: " ++ Printer.pr_constr_env env evd coConstr)
  in
  if Globnames.eq_gr glob_ref ptmReturn || Globnames.eq_gr glob_ref ttmReturn then
    match args with
    | _::h::[] ->
      (TmReturn h, universes)
    | _ -> monad_failure "tmReturn" 2
  else if Globnames.eq_gr glob_ref ptmBind || Globnames.eq_gr glob_ref ttmBind then
    match args with
    | _::_::a::f::[] ->
      (TmBind (a, f), universes)
    | _ -> monad_failure "tmBind" 4
  else if Globnames.eq_gr glob_ref ptmPrint then
    match args with
    | _::trm::[] ->
      (TmPrint trm, universes)
    | _ -> monad_failure "tmPrint" 2
  else if Globnames.eq_gr glob_ref ttmPrintTerm then
    match args with
    | trm::[] ->
      (TmPrintTerm trm, universes)
    | _ -> monad_failure "tmPrint" 1
  else if Globnames.eq_gr glob_ref ptmMsg || Globnames.eq_gr glob_ref ttmMsg then
    match args with
    | trm::[] ->
      (TmMsg trm, universes)
    | _ -> monad_failure "tmMsg" 2
  else if Globnames.eq_gr glob_ref ptmFail || Globnames.eq_gr glob_ref ttmFail then
    match args with
    | _::trm::[] ->
      (TmFail trm, universes)
    | _ -> monad_failure "tmFail" 2
  else if Globnames.eq_gr glob_ref ptmEval then
    match args with
    | strat::_::trm::[] -> (TmEval (strat, trm), universes)
    | _ -> monad_failure "tmEval" 3
  else if Globnames.eq_gr glob_ref ttmEval then
    match args with
    | strat::trm::[] -> (TmEvalTerm (strat, trm), universes)
    | _ -> monad_failure "tmEval" 2

  else if Globnames.eq_gr glob_ref ptmDefinitionRed then
    match args with
    | name::s::typ::body::[] ->
      (TmDefinition (name, s, typ, body), universes)
    | _ -> monad_failure "tmDefinitionRed" 4
  else if Globnames.eq_gr glob_ref ttmDefinition then
    match args with
    | name::typ::body::[] ->
      (TmDefinitionTerm (name, typ, body), universes)
    | _ -> monad_failure "tmDefinition" 3

  else if Globnames.eq_gr glob_ref ptmLemmaRed then
    match args with
    | name::s::typ::[] ->
      (TmLemma (name,s,typ), universes)
    | _ -> monad_failure "tmLemmaRed" 3
  else if Globnames.eq_gr glob_ref ttmLemma then
    match args with
    | name::typ::[] ->
      (TmLemmaTerm (name, typ), universes)
    | _ -> monad_failure "tmLemma" 2

  else if Globnames.eq_gr glob_ref ptmAxiomRed then
    match args with
    | name::s::typ::[] ->
      (TmAxiom (name,s,typ), universes)
    | _ -> monad_failure "tmAxiomRed" 3
  else if Globnames.eq_gr glob_ref ttmAxiom then
    match args with
    | name::typ::[] ->
      (TmAxiomTerm (name, typ), universes)
    | _ -> monad_failure "tmAxiom" 2

  else if Globnames.eq_gr glob_ref ptmFreshName || Globnames.eq_gr glob_ref ttmFreshName then
    match args with
    | name::[] ->
      (TmFreshName name, universes)
    | _ -> monad_failure "tmFreshName" 1

  else if Globnames.eq_gr glob_ref ptmAbout || Globnames.eq_gr glob_ref ttmAbout then
    match args with
    | id::[] ->
      (TmAbout id, universes)
    | _ -> monad_failure "tmAbout" 1
  else if Globnames.eq_gr glob_ref ptmCurrentModPath then
    match args with
    | _::[] -> (TmCurrentModPath, universes)
    | _ -> monad_failure "tmCurrentModPath" 1
  else if Globnames.eq_gr glob_ref ttmCurrentModPath then
    match args with
    | [] -> (TmCurrentModPath, universes)
    | _ -> monad_failure "tmCurrentModPath" 1

  else if Globnames.eq_gr glob_ref ptmMkDefinition then
    match args with
    | name::body::[] ->
      (TmMkDefinition (name, body), universes)
    | _ -> monad_failure "tmMkDefinition" 2

  else if Globnames.eq_gr glob_ref ptmQuote then
    match args with
    | _::trm::[] ->
      (TmQuote (false,trm), universes)
    | _ -> monad_failure "tmQuote" 2
  else if Globnames.eq_gr glob_ref ptmQuoteRec then
    match args with
    | _::trm::[] ->
      (TmQuote (true,trm), universes)
    | _ -> monad_failure "tmQuoteRec" 2

  else if Globnames.eq_gr glob_ref ptmQuoteInductive || Globnames.eq_gr glob_ref ttmQuoteInductive then
    match args with
    | name::[] ->
      (TmQuoteInd name, universes)
    | _ -> monad_failure "tmQuoteInductive" 1
  else if Globnames.eq_gr glob_ref ptmQuoteUniverses || Globnames.eq_gr glob_ref ttmQuoteUniverses then
    match args with
    | [] ->
      (TmQuoteUnivs, universes)
    | _ -> monad_failure "tmQuoteUniverses" 0
  else if Globnames.eq_gr glob_ref ptmQuoteConstant || Globnames.eq_gr glob_ref ttmQuoteConstant then
    match args with
    | name::bypass::[] ->
      (TmQuoteConst (name, bypass), universes)
    | _ -> monad_failure "tmQuoteConstant" 2

  else if Globnames.eq_gr glob_ref ptmMkInductive then
    match args with
    | mind::[] -> (TmMkInductive mind, universes)
    | _ -> monad_failure "tmMkInductive" 1
  else if Globnames.eq_gr glob_ref ttmInductive then
    match args with
    | mind::[] -> (TmMkInductive mind, universes)
    | _ -> monad_failure "tmInductive" 1
  else if Globnames.eq_gr glob_ref ptmUnquote then
    match args with
    | t::[] ->
      (TmUnquote t, universes)
    | _ -> monad_failure "tmUnquote" 1
  else if Globnames.eq_gr glob_ref ptmUnquoteTyped then
    match args with
    | typ::t::[] ->
      (TmUnquoteTyped (typ, t), universes)
    | _ -> monad_failure "tmUnquoteTyped" 2

  else if Globnames.eq_gr glob_ref ptmExistingInstance || Globnames.eq_gr glob_ref ttmExistingInstance then
    match args with
    | name :: [] ->
      (TmExistingInstance name, universes)
    | _ -> monad_failure "tmExistingInstance" 1
  else if Globnames.eq_gr glob_ref ptmInferInstance then
    match args with
    | s :: typ :: [] ->
      (TmInferInstance (s, typ), universes)
    | _ -> monad_failure "tmInferInstance" 2
  else if Globnames.eq_gr glob_ref ttmInferInstance then
    match args with
    | typ :: [] ->
      (TmInferInstanceTerm typ, universes)
    | _ -> monad_failure "tmInferInstance" 2

  else CErrors.user_err (str "Invalid argument or not yet implemented. The argument must be a TemplateProgram: " ++ pr_constr coConstr)
