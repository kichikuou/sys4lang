open Base
open System4_lsp
module Lsp = Linol_lsp.Lsp

let test_project_dir = Stdlib.Filename.concat (Stdlib.Sys.getcwd ()) "testdata"
let testdir_path = List.fold ~init:test_project_dir ~f:Stdlib.Filename.concat

let initialize_project () =
  let proj = Project.create ~read_file:Stdio.In_channel.read_all in
  let pjePath = testdir_path [ "default.pje" ] in
  let options = { Types.InitializationOptions.default with pjePath } in
  Project.initialize proj options;
  Project.initial_scan proj;
  proj

let load_jaf proj path =
  let jaf_text = Stdio.In_channel.read_all path in
  List.iter (Project.update_document proj ~path jaf_text) ~f:(fun d ->
      Stdio.printf "(%d, %d) - (%d, %d) " d.range.start.line
        d.range.start.character d.range.end_.line d.range.end_.character;
      match d.message with
      | `String message -> Stdio.print_endline message
      | _ -> Stdio.print_endline "?");
  jaf_text

let%expect_test "get_hover" =
  let proj = initialize_project () in
  let path = testdir_path [ "src"; "hover.jaf" ] in
  let jaf_text = load_jaf proj path in
  let lines = String.split_lines jaf_text in
  List.iteri lines ~f:(fun i line ->
      match String.substr_index line ~pattern:"^hover" with
      | Some col -> (
          let pos = Lsp.Types.Position.create ~line:(i - 1) ~character:col in
          Stdio.printf "%d:%d: " pos.line pos.character;
          let hover = Project.get_hover proj ~path pos in
          match hover with
          | Some { contents = `MarkupContent { value; _ }; _ } ->
              Stdio.print_endline value
          | _ -> Stdio.print_endline "No hover info")
      | None -> ());
  [%expect
    {|
    1:11: int
    6:11: string
    11:7: int Copy(int , ref array@string , int , int );
    |}]

let definition_test
    (getdef :
      Project.t ->
      path:string ->
      Lsp.Types.Position.t ->
      Lsp.Types.Locations.t option) pattern ~load_classes_after_def =
  let proj = initialize_project () in
  let path = testdir_path [ "src"; "definition.jaf" ] in
  let jaf_text = load_jaf proj path in
  if load_classes_after_def then
    load_jaf proj (testdir_path [ "src"; "classes.jaf" ]) |> ignore;
  let lines = String.split_lines jaf_text in
  List.iteri lines ~f:(fun i line ->
      match String.substr_index line ~pattern with
      | Some col -> (
          let pos = Lsp.Types.Position.create ~line:(i - 1) ~character:col in
          Stdio.printf "%d:%d: " pos.line pos.character;
          let locs = getdef proj ~path pos in
          match locs with
          | Some (`Location [ loc ]) ->
              let def_path = Lsp.Uri.to_path loc.uri in
              let def_text = Stdio.In_channel.read_all def_path in
              let def_lines = String.split_lines def_text in
              let start_line = List.nth_exn def_lines loc.range.start.line in
              let text =
                String.sub start_line ~pos:loc.range.start.character
                  ~len:(loc.range.end_.character - loc.range.start.character)
              in
              Stdio.printf "%s:%d:%d-%d \"%s\"\n"
                (Stdlib.Filename.basename def_path)
                loc.range.start.line loc.range.start.character
                loc.range.end_.character text
          | _ -> Stdio.print_endline "No definition found")
      | None -> ())

let%expect_test "get_definition" =
  let test ~load_classes_after_def =
    definition_test Project.get_definition "^definition" ~load_classes_after_def;
    [%expect
      {|
      1:11: definition.jaf:0:21-26 "int x"
      6:11: globals.jaf:0:4-14 "global_int"
      13:5: definition.jaf:10:0-17 "void foo(void) {}"
      15:6: definition.jaf:29:0-18 "int C::method() {}"
      |}]
  in
  test ~load_classes_after_def:false;
  test ~load_classes_after_def:true

let%expect_test "get_references" =
  let proj = initialize_project () in
  let path = testdir_path [ "src"; "references.jaf" ] in
  let jaf_text = load_jaf proj path in
  let lines = String.split_lines jaf_text in
  List.iteri lines ~f:(fun i line ->
      match String.substr_index line ~pattern:"^ref" with
      | Some col -> (
          let pos = Lsp.Types.Position.create ~line:(i - 1) ~character:col in
          Stdio.printf "%d:%d:\n" pos.line pos.character;
          match
            Project.get_references proj ~path pos ~include_declaration:true
          with
          | None -> Stdio.print_endline "  (none)"
          | Some locs ->
              let sorted =
                List.sort locs ~compare:(fun (a : Lsp.Types.Location.t) b ->
                    let cmp =
                      String.compare (Lsp.Uri.to_path a.uri)
                        (Lsp.Uri.to_path b.uri)
                    in
                    if cmp <> 0 then cmp
                    else
                      let cmp =
                        Int.compare a.range.start.line b.range.start.line
                      in
                      if cmp <> 0 then cmp
                      else
                        Int.compare a.range.start.character
                          b.range.start.character)
              in
              List.iter sorted ~f:(fun (loc : Lsp.Types.Location.t) ->
                  let fname =
                    Stdlib.Filename.basename (Lsp.Uri.to_path loc.uri)
                  in
                  Stdio.printf "  %s:%d:%d-%d:%d\n" fname loc.range.start.line
                    loc.range.start.character loc.range.end_.line
                    loc.range.end_.character))
      | None -> ());
  [%expect
    {|
    0:4:
      references.jaf:0:0-8:1
    2:12:
      references.jaf:0:15-0:20
      references.jaf:2:12-2:13
      references.jaf:4:12-4:13
    4:4:
      references.jaf:2:8-2:17
      references.jaf:4:4-4:5
      references.jaf:4:8-4:9
      references.jaf:6:11-6:12
    6:11:
      references.jaf:2:8-2:17
      references.jaf:4:4-4:5
      references.jaf:4:8-4:9
      references.jaf:6:11-6:12
    11:16:
      definition.jaf:6:11-6:21
      globals.jaf:0:4-0:14
      references.jaf:11:12-11:22
      references.jaf:13:4-13:14
      references.jaf:15:11-15:21
    13:8:
      definition.jaf:6:11-6:21
      globals.jaf:0:4-0:14
      references.jaf:11:12-11:22
      references.jaf:13:4-13:14
      references.jaf:15:11-15:21
    15:15:
      definition.jaf:6:11-6:21
      globals.jaf:0:4-0:14
      references.jaf:11:12-11:22
      references.jaf:13:4-13:14
      references.jaf:15:11-15:21
    19:9:
      references.jaf:19:0-19:34
      references.jaf:23:4-23:24
      references.jaf:25:4-25:24
    23:10:
      references.jaf:19:0-19:34
      references.jaf:23:4-23:24
      references.jaf:25:4-25:24
    25:10:
      references.jaf:19:0-19:34
      references.jaf:23:4-23:24
      references.jaf:25:4-25:24
    30:4:
      references.jaf:29:16-29:19
      references.jaf:30:4-30:5
      references.jaf:32:11-32:12
    32:13:
      classes.jaf:0:15-0:16
      definition.jaf:20:11-20:14
      references.jaf:30:4-30:7
      references.jaf:32:11-32:14
    |}]

let%expect_test "get_type_definition" =
  let test ~load_classes_after_def =
    definition_test Project.get_type_definition "^type_definition"
      ~load_classes_after_def;
    [%expect
      {|
      20:11: classes.jaf:0:0-20 "struct S { int x; };"
      25:4: classes.jaf:2:0-23 "functype void ft(void);"
      |}]
  in
  test ~load_classes_after_def:false;
  test ~load_classes_after_def:true
