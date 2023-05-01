module Focus

    module Lens =

        type Lens<'container, 'value> = ('container -> 'value) * ('value -> 'container -> 'container)
        let composeLenses ((g1, s1): Lens<'container1, 'container2>) ((g2, s2): Lens<'container2, 'value>) = 
            let g3 =
                g1 >> g2
            let s3 = 
                fun v a -> s1 (g1 a |> s2 v) a
            new Lens<'container1, 'value>(g3, s3)
        let (>->) = composeLenses

        let map f ((getter, setter): Lens<'a, 'b>) =
            fun a -> setter(f (getter a)) a

    module Prism =
        open Lens

        type Prism<'container, 'value> = ('container -> 'value option) * ('value -> 'container -> 'container)
        let composePrismAndLens ((gp, sp):Prism<'container1, 'container2>) ((gl, sl):Lens<'container2, 'value>) = 
            let composedGetter (a:'container1) = 
                match gp a with
                | None -> None
                | Some b -> gl b |> Some
            let composedSetter (v:'value) (a:'container1) =
                match gp a with
                | None -> a
                | Some b -> 
                    let (b':'container2) = sl v b
                    sp b' a
            new Prism<'container1, 'value>(composedGetter, composedSetter)
        let (>?>) = composePrismAndLens

        let composeLensAndPrism ((gl, sl):Lens<'container1, 'container2>) ((gp, sp):Prism<'container2, 'value>) = 
            let composedGetter = gl >> gp
            let composedSetter (v: 'value) (a: 'container1) =
                match gp <| gl a with
                | None -> a
                | Some sth -> sl (sp v (gl a)) a 
            new Prism<'container1, 'value>(composedGetter, composedSetter)

        let (>-?>) = composeLensAndPrism

        let composeLensAndPrism' ((gl, sl): Lens<'container1, 'container2>) ((gp, sp):Prism<'container2, 'value>) = 
            let g3 =
                gl >> gp
            let s3 = 
                fun v a -> sl (gl a |> sp v) a
            new Prism<'container1, 'value>(g3, s3)

        let composePrismAndPrism ((g1, s1): Prism<'container1, 'container2>) ((g2, s2):Prism<'container2, 'value>) = 
            let composedGetter a = match g1 a with
                                        | None -> None 
                                        | Some b -> g2 b
            let composedSetter (v: 'value) (a: 'container1) =
                match g1 a with
                | None -> a
                | Some b -> match g2 b with
                                         | None -> a
                                         | Some sth -> s1 (s2 v b) a 
            new Prism<'container1, 'value>(composedGetter, composedSetter)
        let (>??>) = composePrismAndPrism

    module Morphism = 
        open Lens
        
        // Lets manipulate WITHOUT having the expected Lens 'value type
        type Isomorphism<'a, 'b> = ('a -> 'b) * ('b -> 'a)

        let composeLensAndIsomorphism ((gl, sl):Lens<'container1, 'value1>) ((convertTo, convertFrom): Isomorphism<'value1, 'value2>) = 
            let composedGetter = gl >> convertTo
            let composedSetter (v:'value2) (a: 'container1) = sl (convertFrom v) a
            new Lens<'container1, 'value2>(composedGetter, composedSetter)

        let (>-~>) = composeLensAndIsomorphism

        let composeIsomorphisms (iso1: Isomorphism<'a, 'b>) (iso2: Isomorphism<'b, 'c>) = 
            let to1, from1 = iso1
            let to2, from2 = iso2
            let composedConvertTo = to1 >> to2
            let composedConvertFrom = from2 >> from1
            new Isomorphism<'a, 'c>(composedConvertTo, composedConvertFrom)

        let (>->->) = composeIsomorphisms

    module Work =
        open Lens

        type RecordA =
            { B: RecordB }

        and RecordB =
            { Value: string }

        let getB = 
            fun a -> a.B
        let getValue = 
            fun b -> b.Value
        let getValueFromA = 
            getB >> getValue

        let setB = 
            fun b a -> { a with B = b }
        let setValue =
            fun v b -> { b with Value = v }
        let setValueFromA = 
            fun a v -> setB (getB a |> setValue v) a

        let lensLevelA = new Lens<RecordA,RecordB>(getB,setB)
        let lensLevelB = new Lens<RecordB, string>(getValue, setValue)
        let lensCombined = lensLevelA >-> lensLevelB
        let getter ((g, _): Lens<_, _>) = g
        let setter ((_, s): Lens<_, _>) = s

        let rec1 = { B = { Value = "toto" } }
        let rec1Val = (getter lensCombined) rec1
        let rec1Alt = (setter lensCombined) "titi" rec1

        let capitalizeThruLens = 
            Lens.map (fun (s :string) -> s.ToUpper()) lensCombined

        let test = capitalizeThruLens rec1

    module Work2 = 
        open Prism
        open Lens

        // --------------------------------
        // If we ARE dealing with an option
        type RecordA =
            { B: RecordB option }

        and RecordB =
            { Value: string }

        let getBFromA (a:RecordA) = a.B
        let setBFromA (b:RecordB) a = { a with B = Some b }

        let getValueFromB b = b.Value
        let setBFromValue v b = { b with Value = v }

        let p1 = new Prism<RecordA,RecordB>(getBFromA, setBFromA)
        let l1 = new Lens<RecordB,string>(getValueFromB, setBFromValue)

        let newPrism = p1 >?> l1

        // ------------------------------------
        // If we are NOT dealing with an option

        type RecordA' = 
            { B: RecordB'InMyUnion } // what if we have not an option but another kind of discriminated union
        and RecordB'InMyUnion = 
            | Absent
            | Maybe of int
            | Totally of RecordB'
        and RecordB' = { Value: string }

        let getTotallyValueFromMyUnion = 
            fun (m:RecordB'InMyUnion) -> match m with
                                         | Absent -> None
                                         | Maybe _ -> None
                                         | Totally r -> Some r

        let setTotallyValueFromMyUnion (v:RecordB') (m:RecordB'InMyUnion) = 
            match m with 
            | Absent -> m
            | Maybe _ -> m 
            | Totally r -> Totally(v)

        let getValueFromRecordB' (r:RecordB') = r.Value
        let setValueFromRecordB' (v:string) (r:RecordB') = { r with Value = v }

        let getBFromRecordA' (a:RecordA') = a.B
        let setBFromRecordA' (b:RecordB'InMyUnion) (a:RecordA') = 
            { a with B = b }

        let topL2 = 
            new Lens<RecordA', RecordB'InMyUnion>(getBFromRecordA', setBFromRecordA')

        let p2 = 
            new Prism<RecordB'InMyUnion, RecordB'>(getTotallyValueFromMyUnion, setTotallyValueFromMyUnion)

        let l2 = 
            new Lens<RecordB', string>(getValueFromRecordB', setValueFromRecordB')

        let test = { B = Absent }
        let test' = { B = Maybe (1) }
        let test'' = { B = {Value = "value"} |> Totally }

        let myComposedPrism = 
            //composePrismAndLens (composeLensAndPrism topL2 p2) l2
            topL2 >-?> p2 >?> l2

        let theirComposedPrism = composePrismAndLens (composeLensAndPrism' topL2 p2) l2

        let (myG, myS) = myComposedPrism
        let (theirG, theirS) = theirComposedPrism

        let res1 = myG test
        let res2 = myG test'
        let res3 = myG test''

        let res4 = theirG test
        let res5 = theirG test'
        let res6 = theirG test''
            

        let res1' = myS "edited" test
        let res2' = myS "edited" test'
        let res3' = myS "edited" test''

        let res4' = theirS "edited" test
        let res5' = theirS "edited" test'
        let res6' = theirS "edited" test''