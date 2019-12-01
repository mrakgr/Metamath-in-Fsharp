open System.Collections.Generic

let disjointness_check (disjoint_vars : Map<string, Set<string>>) (substs_map : Dictionary<string, Set<string>>) =
    let fails = ResizeArray()

    let check (kv : KeyValuePair<_,_>) next prev = 
        let var', subvars' as cur = kv.Key, kv.Value
        match prev with
        | None -> ()
        | Some (var, subvars) as prev ->
            Set.iter (fun v ->
                let v_disjoint_vars =
                    match Map.tryFind v disjoint_vars with
                    | None -> Set.empty
                    | Some v_disjoint_vars -> v_disjoint_vars
                if Set.isEmpty (subvars' - v_disjoint_vars) = false then fails.Add((var,v),(var',subvars'))
                ) subvars
            next prev
        next (Some cur)

    Seq.foldBack check substs_map (fun _ -> ()) None
    fails.ToArray()

type MMEval =
    | MMFloating of ty : string * var : string
    | MMEssential of ty : string * prog : string list * disjoint : Map<string, Set<string>>
    | MMAxiom of ty : string * prog : string list * disjoint : Map<string, Set<string>>

let substitute is_var (m : Map<string, string list>) (desc : string list) =
    let subvars = Dictionary(HashIdentity.Structural)
    subvars,
    List.collect (fun x ->
        match Map.tryFind x m with
        | Some v ->
            match subvars.TryGetValue x with
            | false, _ -> subvars.[x] <- List.fold (fun s x -> if is_var x then Set.add x s else s) Set.empty v
            | true, _ -> ()
            v
        | None -> [x]
        ) desc

let prove (floating : Map<string, string>) (x : (MMEval * (string * string list)) list) = 
    List.fold (fun m x ->
        match x with
        | MMFloating(ty,var), (ty', var') ->
            if ty = ty' then Map.add var var' m
            else failwith "ty <> ty'"
        | MMEssential(ty,prog,disjoint), (ty',prog') ->
            if ty = ty' then 
                let used_vars, prog'' = substitute (fun x -> Map.containsKey x floating) m prog
                if prog' = prog'' then
                    match disjointness_check disjoint used_vars with
                    | [||] -> m
                    | errors -> 
                        Array.map (fun ((var,v),(var',subvars')) -> sprintf "In the substitution of %s and %s, the variable %s is not disjoint from %A" var var' v subvars') errors
                        |> String.concat "\n"
                        |> failwith
                else failwith "unification failed"
            else failwith "ty <> ty'"
        | MMAxiom(_,prog,disjoint), _ ->
            let used_vars, prog'' = substitute (fun x -> Map.containsKey x floating) m prog
            match disjointness_check disjoint used_vars with
            | [||] -> m // should return prog''
            | errors -> 
                Array.map (fun ((var,v),(var',subvars')) -> sprintf "In the substitution of %s and %s, the variable %s is not disjoint from %A" var var' v subvars') errors
                |> String.concat "\n"
                |> failwith
        ) Map.empty x
