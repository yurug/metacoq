(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "template_coq_checker_plugin"

open Constrarg
open Pp
open PeanoNat.Nat
open Typing0
let pr_char c = str (Char.escaped c)
   
let pr_char_list = prlist_with_sep mt pr_char

let check gr =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let Sigma.Sigma (c, sigma, _) = Evarutil.new_global (Sigma.Unsafe.of_evar_map sigma) gr in
  Feedback.msg_debug (str"Quoting");
  let term = Template_coq.quote_term_rec env c in
  Feedback.msg_debug (str"Finished quoting.. checking.");
  let fuel = pow two (pow two (pow two two)) in
  match Typing0.typecheck_program fuel term with
  | CorrectDecl t ->
     Feedback.msg_debug (str"Finished checking successfully")
  | EnvError (AlreadyDeclared id) ->
     CErrors.errorlabstrm "template-coq" (str "Already declared: " ++ pr_char_list id)
  | EnvError (IllFormedDecl (id, e)) ->
     CErrors.errorlabstrm "template-coq" (str "Type error while checking: " ++ pr_char_list id)
    
VERNAC COMMAND EXTEND TemplateCheck CLASSIFIED AS QUERY
| [ "Template" "Check" global(gr) ] -> [
    let gr = Nametab.global gr in
    check gr
  ]
END
