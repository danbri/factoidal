open Prims
let ends_with (s : Prims.string) (suf : Prims.string) : Prims.bool=
  let lp = FStar_String.strlen s in
  let ls = FStar_String.strlen suf in
  if lp >= ls then (FStar_String.sub s (lp - ls) ls) = suf else false
let content_type_for_path (path : Prims.string) : Prims.string=
  let p = FStar_String.lowercase path in
  if (ends_with p ".html") || (ends_with p ".htm")
  then "text/html; charset=utf-8"
  else
    if ends_with p ".css"
    then "text/css; charset=utf-8"
    else
      if (ends_with p ".js") || (ends_with p ".mjs")
      then "application/javascript; charset=utf-8"
      else
        if ends_with p ".json"
        then "application/json; charset=utf-8"
        else
          if ends_with p ".svg"
          then "image/svg+xml; charset=utf-8"
          else
            if ends_with p ".png"
            then "image/png"
            else
              if (ends_with p ".jpg") || (ends_with p ".jpeg")
              then "image/jpeg"
              else
                if ends_with p ".ico"
                then "image/x-icon"
                else
                  if (ends_with p ".txt") || (ends_with p ".md")
                  then "text/plain; charset=utf-8"
                  else
                    if ends_with p ".ttl"
                    then "text/turtle; charset=utf-8"
                    else
                      if ends_with p ".nt"
                      then "application/n-triples; charset=utf-8"
                      else
                        if ends_with p ".nq"
                        then "application/n-quads; charset=utf-8"
                        else "application/octet-stream"
let rec contains_dotdot_at (s : Prims.string) (i : Prims.nat) : Prims.bool=
  let n = FStar_String.strlen s in
  if (i + (Prims.of_int (2))) > n
  then false
  else
    if (FStar_String.sub s i (Prims.of_int (2))) = ".."
    then true
    else
      if (i + Prims.int_one) > n
      then false
      else contains_dotdot_at s (i + Prims.int_one)
let path_has_dotdot (p : Prims.string) : Prims.bool=
  contains_dotdot_at p Prims.int_zero
