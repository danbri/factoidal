open Prims
let rec (replace_all_aux :
  Prims.string ->
    Prims.string ->
      Prims.string ->
        Prims.nat ->
          Prims.nat ->
            FStar_Char.char Prims.list -> FStar_Char.char Prims.list)
  =
  fun haystack ->
    fun needle ->
      fun replacement ->
        fun nlen ->
          fun pos ->
            fun acc ->
              let hlen = FStar_String.strlen haystack in
              if pos >= hlen
              then acc
              else
                if (pos + nlen) > hlen
                then
                  (let c = FStar_String.index haystack pos in
                   replace_all_aux haystack needle replacement nlen
                     (pos + Prims.int_one) (c :: acc))
                else
                  (let candidate = FStar_String.sub haystack pos nlen in
                   if candidate = needle
                   then
                     let rep_chars = FStar_String.list_of_string replacement in
                     let acc' = FStar_List_Tot_Base.rev_acc rep_chars acc in
                     replace_all_aux haystack needle replacement nlen
                       (pos + nlen) acc'
                   else
                     (let c = FStar_String.index haystack pos in
                      replace_all_aux haystack needle replacement nlen
                        (pos + Prims.int_one) (c :: acc)))
let (string_replace_all :
  Prims.string -> Prims.string -> Prims.string -> Prims.string) =
  fun needle ->
    fun replacement ->
      fun haystack ->
        let nlen = FStar_String.strlen needle in
        if nlen = Prims.int_zero
        then haystack
        else
          (let revc =
             replace_all_aux haystack needle replacement nlen Prims.int_zero
               [] in
           FStar_String.string_of_list (FStar_List_Tot_Base.rev revc))
let (expand_user_graph : Prims.string -> Prims.string -> Prims.string) =
  fun template -> fun authid -> string_replace_all "{authid}" authid template
let rec (find_authid_placeholder :
  Prims.string ->
    Prims.nat -> Prims.nat -> Prims.nat FStar_Pervasives_Native.option)
  =
  fun s ->
    fun pos ->
      fun fuel ->
        let len = FStar_String.strlen s in
        let key = "{authid}" in
        let klen = FStar_String.strlen key in
        if fuel = Prims.int_zero
        then FStar_Pervasives_Native.None
        else
          if (pos + klen) > len
          then FStar_Pervasives_Native.None
          else
            if (FStar_String.sub s pos klen) = key
            then FStar_Pervasives_Native.Some pos
            else
              find_authid_placeholder s (pos + Prims.int_one)
                (fuel - Prims.int_one)
let (template_prefix : Prims.string -> Prims.string) =
  fun template ->
    let len = FStar_String.strlen template in
    let fuel = len + Prims.int_one in
    match find_authid_placeholder template Prims.int_zero fuel with
    | FStar_Pervasives_Native.None -> template
    | FStar_Pervasives_Native.Some i ->
        if i <= len
        then FStar_String.sub template Prims.int_zero i
        else template
type ggp_target_status =
  | GTS_Ok 
  | GTS_Mismatch of Prims.string 
  | GTS_NonIri 
let (uu___is_GTS_Ok : ggp_target_status -> Prims.bool) =
  fun projectee -> match projectee with | GTS_Ok -> true | uu___ -> false
let (uu___is_GTS_Mismatch : ggp_target_status -> Prims.bool) =
  fun projectee ->
    match projectee with | GTS_Mismatch iri -> true | uu___ -> false
let (__proj__GTS_Mismatch__item__iri : ggp_target_status -> Prims.string) =
  fun projectee -> match projectee with | GTS_Mismatch iri -> iri
let (uu___is_GTS_NonIri : ggp_target_status -> Prims.bool) =
  fun projectee -> match projectee with | GTS_NonIri -> true | uu___ -> false
let (check_ggp_graph_target :
  SPARQL11_Algebra.group_graph_pattern ->
    RDF_Graph_Executable.wf_iri -> ggp_target_status)
  =
  fun g ->
    fun usergraph ->
      match g with
      | SPARQL11_Algebra.GP_Graph (pt, _inner) ->
          (match pt with
           | SPARQL11_Algebra.PT_IRI iri ->
               if iri = usergraph then GTS_Ok else GTS_Mismatch iri
           | uu___ -> GTS_NonIri)
      | uu___ -> GTS_Ok
let (wrap_if_unwrapped :
  SPARQL11_Algebra.group_graph_pattern ->
    RDF_Graph_Executable.wf_iri -> SPARQL11_Algebra.group_graph_pattern)
  =
  fun g ->
    fun usergraph ->
      match g with
      | SPARQL11_Algebra.GP_Graph (uu___, uu___1) -> g
      | uu___ ->
          SPARQL11_Algebra.GP_Graph ((SPARQL11_Algebra.PT_IRI usergraph), g)
type ggp_check_result =
  | GCR_Rewrite of SPARQL11_Algebra.group_graph_pattern 
  | GCR_Reject of Prims.string 
let (uu___is_GCR_Rewrite : ggp_check_result -> Prims.bool) =
  fun projectee ->
    match projectee with | GCR_Rewrite _0 -> true | uu___ -> false
let (__proj__GCR_Rewrite__item___0 :
  ggp_check_result -> SPARQL11_Algebra.group_graph_pattern) =
  fun projectee -> match projectee with | GCR_Rewrite _0 -> _0
let (uu___is_GCR_Reject : ggp_check_result -> Prims.bool) =
  fun projectee ->
    match projectee with | GCR_Reject _0 -> true | uu___ -> false
let (__proj__GCR_Reject__item___0 : ggp_check_result -> Prims.string) =
  fun projectee -> match projectee with | GCR_Reject _0 -> _0
let (check_ggp :
  Prims.string ->
    SPARQL11_Algebra.group_graph_pattern ->
      RDF_Graph_Executable.wf_iri -> ggp_check_result)
  =
  fun which ->
    fun g ->
      fun usergraph ->
        match check_ggp_graph_target g usergraph with
        | GTS_Ok -> GCR_Rewrite (wrap_if_unwrapped g usergraph)
        | GTS_Mismatch iri ->
            GCR_Reject
              (Prims.strcat which
                 (Prims.strcat " targets graph <"
                    (Prims.strcat iri
                       (Prims.strcat ">; your sandbox is <"
                          (Prims.strcat usergraph ">")))))
        | GTS_NonIri ->
            GCR_Reject
              (Prims.strcat which
                 (Prims.strcat " uses a non-IRI graph target; only GRAPH <"
                    (Prims.strcat usergraph "> is allowed")))
type gref_check_result =
  | GRCR_Ok 
  | GRCR_Reject of Prims.string 
let (uu___is_GRCR_Ok : gref_check_result -> Prims.bool) =
  fun projectee -> match projectee with | GRCR_Ok -> true | uu___ -> false
let (uu___is_GRCR_Reject : gref_check_result -> Prims.bool) =
  fun projectee ->
    match projectee with | GRCR_Reject _0 -> true | uu___ -> false
let (__proj__GRCR_Reject__item___0 : gref_check_result -> Prims.string) =
  fun projectee -> match projectee with | GRCR_Reject _0 -> _0
let (check_gref :
  Prims.string ->
    SPARQL11_Algebra.graph_ref ->
      RDF_Graph_Executable.wf_iri -> gref_check_result)
  =
  fun which ->
    fun gr ->
      fun usergraph ->
        match gr with
        | SPARQL11_Algebra.GR_Graph iri ->
            if iri = usergraph
            then GRCR_Ok
            else
              GRCR_Reject
                (Prims.strcat which
                   (Prims.strcat " targets graph <"
                      (Prims.strcat iri
                         (Prims.strcat ">; your sandbox is <"
                            (Prims.strcat usergraph ">")))))
        | SPARQL11_Algebra.GR_Default ->
            GRCR_Reject
              (Prims.strcat which
                 (Prims.strcat
                    " targets the default graph; your sandbox is <"
                    (Prims.strcat usergraph ">")))
        | SPARQL11_Algebra.GR_Named ->
            GRCR_Reject
              (Prims.strcat which
                 (Prims.strcat " targets NAMED; your sandbox is <"
                    (Prims.strcat usergraph ">")))
        | SPARQL11_Algebra.GR_All ->
            GRCR_Reject
              (Prims.strcat which
                 (Prims.strcat " targets ALL graphs; your sandbox is <"
                    (Prims.strcat usergraph ">")))
type sandbox_result =
  | SB_Ok of SPARQL11_Algebra.update_op 
  | SB_Reject of Prims.string 
let (uu___is_SB_Ok : sandbox_result -> Prims.bool) =
  fun projectee -> match projectee with | SB_Ok _0 -> true | uu___ -> false
let (__proj__SB_Ok__item___0 : sandbox_result -> SPARQL11_Algebra.update_op)
  = fun projectee -> match projectee with | SB_Ok _0 -> _0
let (uu___is_SB_Reject : sandbox_result -> Prims.bool) =
  fun projectee ->
    match projectee with | SB_Reject _0 -> true | uu___ -> false
let (__proj__SB_Reject__item___0 : sandbox_result -> Prims.string) =
  fun projectee -> match projectee with | SB_Reject _0 -> _0
type tpl_opt_result =
  | TOR_Rewrite of SPARQL11_Algebra.group_graph_pattern
  FStar_Pervasives_Native.option 
  | TOR_Reject of Prims.string 
let (uu___is_TOR_Rewrite : tpl_opt_result -> Prims.bool) =
  fun projectee ->
    match projectee with | TOR_Rewrite _0 -> true | uu___ -> false
let (__proj__TOR_Rewrite__item___0 :
  tpl_opt_result ->
    SPARQL11_Algebra.group_graph_pattern FStar_Pervasives_Native.option)
  = fun projectee -> match projectee with | TOR_Rewrite _0 -> _0
let (uu___is_TOR_Reject : tpl_opt_result -> Prims.bool) =
  fun projectee ->
    match projectee with | TOR_Reject _0 -> true | uu___ -> false
let (__proj__TOR_Reject__item___0 : tpl_opt_result -> Prims.string) =
  fun projectee -> match projectee with | TOR_Reject _0 -> _0
let (check_tpl_opt :
  Prims.string ->
    SPARQL11_Algebra.group_graph_pattern FStar_Pervasives_Native.option ->
      RDF_Graph_Executable.wf_iri -> tpl_opt_result)
  =
  fun label ->
    fun t ->
      fun usergraph ->
        match t with
        | FStar_Pervasives_Native.None ->
            TOR_Rewrite FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            (match check_ggp label g usergraph with
             | GCR_Rewrite g' ->
                 TOR_Rewrite (FStar_Pervasives_Native.Some g')
             | GCR_Reject msg -> TOR_Reject msg)
let (sandbox_op :
  RDF_Graph_Executable.wf_iri -> SPARQL11_Algebra.update_op -> sandbox_result)
  =
  fun usergraph ->
    fun op ->
      match op with
      | SPARQL11_Algebra.U_InsertData g ->
          (match check_ggp "INSERT DATA" g usergraph with
           | GCR_Rewrite g' -> SB_Ok (SPARQL11_Algebra.U_InsertData g')
           | GCR_Reject msg -> SB_Reject msg)
      | SPARQL11_Algebra.U_DeleteData g ->
          (match check_ggp "DELETE DATA" g usergraph with
           | GCR_Rewrite g' -> SB_Ok (SPARQL11_Algebra.U_DeleteData g')
           | GCR_Reject msg -> SB_Reject msg)
      | SPARQL11_Algebra.U_DeleteWhere g ->
          (match check_ggp "DELETE WHERE" g usergraph with
           | GCR_Rewrite g' -> SB_Ok (SPARQL11_Algebra.U_DeleteWhere g')
           | GCR_Reject msg -> SB_Reject msg)
      | SPARQL11_Algebra.U_Modify (w, del_tpl, ins_tpl, using, where) ->
          (match check_tpl_opt "INSERT/DELETE: DELETE clause" del_tpl
                   usergraph
           with
           | TOR_Reject msg -> SB_Reject msg
           | TOR_Rewrite del_tpl' ->
               (match check_tpl_opt "INSERT/DELETE: INSERT clause" ins_tpl
                        usergraph
                with
                | TOR_Reject msg -> SB_Reject msg
                | TOR_Rewrite ins_tpl' ->
                    SB_Ok
                      (SPARQL11_Algebra.U_Modify
                         (w, del_tpl', ins_tpl', using, where))))
      | SPARQL11_Algebra.U_Clear (silent, gr) ->
          (match check_gref "CLEAR" gr usergraph with
           | GRCR_Ok -> SB_Ok (SPARQL11_Algebra.U_Clear (silent, gr))
           | GRCR_Reject msg -> SB_Reject msg)
      | SPARQL11_Algebra.U_Drop (silent, gr) ->
          (match check_gref "DROP" gr usergraph with
           | GRCR_Ok -> SB_Ok (SPARQL11_Algebra.U_Drop (silent, gr))
           | GRCR_Reject msg -> SB_Reject msg)
      | SPARQL11_Algebra.U_Create (silent, iri) ->
          if iri = usergraph
          then SB_Ok (SPARQL11_Algebra.U_Create (silent, iri))
          else
            SB_Reject
              (Prims.strcat "CREATE targets graph <"
                 (Prims.strcat iri
                    (Prims.strcat ">; your sandbox is <"
                       (Prims.strcat usergraph ">"))))
      | SPARQL11_Algebra.U_Add (silent, src, dst) ->
          (match check_gref "ADD source" src usergraph with
           | GRCR_Reject msg -> SB_Reject msg
           | GRCR_Ok ->
               (match check_gref "ADD dest" dst usergraph with
                | GRCR_Ok ->
                    SB_Ok (SPARQL11_Algebra.U_Add (silent, src, dst))
                | GRCR_Reject msg -> SB_Reject msg))
      | SPARQL11_Algebra.U_Move (silent, src, dst) ->
          (match check_gref "MOVE source" src usergraph with
           | GRCR_Reject msg -> SB_Reject msg
           | GRCR_Ok ->
               (match check_gref "MOVE dest" dst usergraph with
                | GRCR_Ok ->
                    SB_Ok (SPARQL11_Algebra.U_Move (silent, src, dst))
                | GRCR_Reject msg -> SB_Reject msg))
      | SPARQL11_Algebra.U_Copy (silent, src, dst) ->
          (match check_gref "COPY source" src usergraph with
           | GRCR_Reject msg -> SB_Reject msg
           | GRCR_Ok ->
               (match check_gref "COPY dest" dst usergraph with
                | GRCR_Ok ->
                    SB_Ok (SPARQL11_Algebra.U_Copy (silent, src, dst))
                | GRCR_Reject msg -> SB_Reject msg))
      | SPARQL11_Algebra.U_Load (uu___, uu___1, uu___2) ->
          SB_Reject "LOAD is not permitted in sandboxed updates"
type update_sandbox_result =
  | USR_Ok of SPARQL11_Algebra.sparql_update 
  | USR_Error of Prims.string 
let (uu___is_USR_Ok : update_sandbox_result -> Prims.bool) =
  fun projectee -> match projectee with | USR_Ok _0 -> true | uu___ -> false
let (__proj__USR_Ok__item___0 :
  update_sandbox_result -> SPARQL11_Algebra.sparql_update) =
  fun projectee -> match projectee with | USR_Ok _0 -> _0
let (uu___is_USR_Error : update_sandbox_result -> Prims.bool) =
  fun projectee ->
    match projectee with | USR_Error _0 -> true | uu___ -> false
let (__proj__USR_Error__item___0 : update_sandbox_result -> Prims.string) =
  fun projectee -> match projectee with | USR_Error _0 -> _0
let rec (sandbox_ops_aux :
  RDF_Graph_Executable.wf_iri ->
    SPARQL11_Algebra.update_op Prims.list ->
      SPARQL11_Algebra.update_op Prims.list ->
        (Prims.string, SPARQL11_Algebra.update_op Prims.list)
          FStar_Pervasives.either)
  =
  fun usergraph ->
    fun acc ->
      fun ops ->
        match ops with
        | [] -> FStar_Pervasives.Inr (FStar_List_Tot_Base.rev acc)
        | op::rest ->
            (match sandbox_op usergraph op with
             | SB_Ok op' -> sandbox_ops_aux usergraph (op' :: acc) rest
             | SB_Reject msg -> FStar_Pervasives.Inl msg)
let (sandbox_update :
  RDF_Graph_Executable.wf_iri ->
    SPARQL11_Algebra.sparql_update -> update_sandbox_result)
  =
  fun usergraph ->
    fun u ->
      match sandbox_ops_aux usergraph [] u.SPARQL11_Algebra.u_ops with
      | FStar_Pervasives.Inl msg -> USR_Error msg
      | FStar_Pervasives.Inr ops' ->
          USR_Ok
            {
              SPARQL11_Algebra.u_base = (u.SPARQL11_Algebra.u_base);
              SPARQL11_Algebra.u_prefixes = (u.SPARQL11_Algebra.u_prefixes);
              SPARQL11_Algebra.u_ops = ops'
            }
