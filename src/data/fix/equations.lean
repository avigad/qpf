
import for_mathlib

namespace tactic
namespace eqn_compiler

meta inductive def_body
| term (b : expr)
| eqns (ls : list (list expr × expr))

meta structure fun_def :=
(univs : list name)
(name : name)
(params : list expr)
(type : expr)
(body : def_body)

open function

meta def render_body : def_body → format
| (def_body.term b) := " :=\n" ++ b.parsable_printer
| (def_body.eqns ls) :=
"\n" ++ format.intercalate "\n" (ls.map $ uncurry $
  λ p e, let pat := format.intercalate " " (p.map $ format.paren ∘ expr.parsable_printer) in
         format!"| {pat} := {expr.parsable_printer e}")

meta def add_fn (pre : name) (fn : fun_def) : lean.parser unit :=
do
   let n' := to_fmt fn.name,
   let n' := to_fmt $ fn.name.replace_prefix pre name.anonymous,
   let args := format.intercalate " " (n' :: fn.params.map expr.as_binder),
   let xs :=
     sformat!"def {args} : {expr.parsable_printer fn.type}{render_body fn.body}",
   trace xs,
   lean.parser.with_input lean.parser.command_like xs,
   (resolve_name fn.name >>= trace : tactic _),
   pure ()

end eqn_compiler
end tactic
