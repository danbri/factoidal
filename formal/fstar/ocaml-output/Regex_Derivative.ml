open Prims
let rec deriv (c : Prims.nat) (r : Regex_Syntax.regex) : Regex_Syntax.regex=
  match r with
  | Regex_Syntax.R_Empty -> Regex_Syntax.R_Empty
  | Regex_Syntax.R_Eps -> Regex_Syntax.R_Empty
  | Regex_Syntax.R_Ranges rs ->
      if Regex_Syntax.in_ranges c rs
      then Regex_Syntax.R_Eps
      else Regex_Syntax.R_Empty
  | Regex_Syntax.R_Alt (a, b) ->
      Regex_Syntax.smart_alt (deriv c a) (deriv c b)
  | Regex_Syntax.R_And (a, b) ->
      Regex_Syntax.smart_and (deriv c a) (deriv c b)
  | Regex_Syntax.R_Not a -> Regex_Syntax.smart_not (deriv c a)
  | Regex_Syntax.R_Cat (a, b) ->
      let left = Regex_Syntax.R_Cat ((deriv c a), b) in
      if Regex_Syntax.nullable a
      then Regex_Syntax.smart_alt left (deriv c b)
      else left
  | Regex_Syntax.R_Star a ->
      Regex_Syntax.R_Cat ((deriv c a), (Regex_Syntax.R_Star a))
let rec deriv_word (r : Regex_Syntax.regex) (w : Prims.nat Prims.list) :
  Regex_Syntax.regex=
  match w with | [] -> r | c::rest -> deriv_word (deriv c r) rest
let matches (r : Regex_Syntax.regex) (w : Prims.nat Prims.list) : Prims.bool=
  Regex_Syntax.nullable (deriv_word r w)
