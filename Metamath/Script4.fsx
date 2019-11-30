let substitute (desc : string list) (m : Map<string, string list>) =
    List.collect (fun x -> 
        match Map.tryFind x m with
        | Some x -> x
        | None -> [x]
        ) desc

let disjointness_check (disjoint_vars : Map<string, Set<string>>) (substs_map : Map<string,Set<string>>) =
    let fails = ResizeArray()

    let find x m on_succ = 
        match Map.tryFind x m with
        | None -> ()
        | Some a -> on_succ a

    /// Find all the outer substitutions that need to be checked.
    Map.iter (fun var subvars ->
        find var disjoint_vars (
            Set.iter (fun var' ->
                find var' substs_map (fun subvars' ->
                    // Make sure that the inner substitutions make sense.
                    Set.iter (fun v ->
                        let v_disjoint_vars = 
                            match Map.tryFind v disjoint_vars with
                            | None -> Set.singleton v
                            | Some v_disjoint_vars -> Set.add v v_disjoint_vars
                        if Set.isEmpty (subvars' - v_disjoint_vars) = false then fails.Add(var,var',v,subvars')
                        ) subvars
                    )
                )
            )
        ) substs_map

    fails.ToArray()