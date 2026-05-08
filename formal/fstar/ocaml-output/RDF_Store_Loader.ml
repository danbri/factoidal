open Prims
let merge_pair (acc : RDF_Graph_Executable.rdf_dataset)
  (extra : RDF_Graph_Executable.rdf_dataset) :
  RDF_Graph_Executable.rdf_dataset=
  {
    RDF_Graph_Executable.ds_default =
      (RDF_List_Helpers.append_tr acc.RDF_Graph_Executable.ds_default
         extra.RDF_Graph_Executable.ds_default);
    RDF_Graph_Executable.ds_named =
      (RDF_List_Helpers.append_tr acc.RDF_Graph_Executable.ds_named
         extra.RDF_Graph_Executable.ds_named)
  }
let merge_datasets (base : RDF_Graph_Executable.rdf_dataset)
  (extras : RDF_Graph_Executable.rdf_dataset Prims.list) :
  RDF_Graph_Executable.rdf_dataset=
  FStar_List_Tot_Base.fold_left merge_pair base extras
