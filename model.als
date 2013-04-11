sig State{
	kinds : set Kind
}

sig Kind{
	name : one Name,
	records : set Record,
	structure : seq Def
}{
	some s : State |
		this in s.kinds

	!structure.hasDups
}

sig Record{
	items : seq Container,
	id : Int
}{
	//record in a kind
	some k : Kind |
		this in k.records

	//if multiple owning kinds => they have same name => the same kind in different states
	all k1, k2 : Kind |
		this in k1.records and this in k2.records implies k1.name = k2.name		
	
	//no duplicates of containers
	!items.hasDups
	
	//number of items is equal to number of definitions defying the structure of the owning kind
	#items = #(this.~records.structure)
}

abstract sig Container{
	values : set (Value + Int)
}{
	some r : Record |
		this in r.items.elems
}

sig ValueContainer extends Container{
	
}{
	values in Value
	#values >= 1
}

sig ReferenceContainer extends Container{

}{
	values in Int
}


sig Value{}{
	one vc : ValueContainer |
		this in vc.values
}

sig Name{}{
	some k : Kind |
		this in k.name
	
	all disj k1, k2 : Kind |
		this in k1.name and this in k2.name implies k1.~kinds != k2.~kinds
}

abstract sig Def{}{
	some k : Kind |
		this in k.structure.elems
}

sig ValueDef extends Def{

}


sig ReferenceDef extends Def{
	reference : one Name
}{
	//reference is in the same state
	//reference.~kinds = this.~structure.~kinds
}

/* ************************************************************************************************** */
fact not_same_ids_in_kinds{
	all disj r1, r2 : Record |
		r1.id = r2.id implies r1.(~records) != r2.(~records)
}

fact structure_of_record_in_kind{
	all k : Kind, r : Record, vc : ValueContainer |
			vc in r.items.elems and r in k.records implies
				 one vd : ValueDef | vd in k.structure.elems and k.structure.idxOf[vd] = r.items.idxOf[vc]

	all k : Kind, r : Record, rc : ReferenceContainer |
			rc in r.items.elems and r in k.records implies
				 one rd : ReferenceDef | rd in k.structure.elems and k.structure.idxOf[rd] = r.items.idxOf[rc]
	
	all k : Kind, r : Record, vd : ValueDef |
		vd in k.structure.elems   and r in k.records implies
			 one vc : ValueContainer | vc in r.items.elems and k.structure.idxOf[vd] = r.items.idxOf[vc]		
}

fact refereces_are_ids_of_referenced{
	all k : Kind, rd : ReferenceDef, rc : ReferenceContainer, r : Record |
		r in k.records	
		and rd in k.structure.elems
		and rc in r.items.elems
		and r.items.idxOf[rc] = k.structure.idxOf[rd] implies
			rc.values in rd.reference.~name.records.id 
}


fact referenced_name_and_reference_are_in_same_state{
	all rd : ReferenceDef |
	//	rd.reference.~name.~kinds in {s : State | rd in s.kinds.structure.elems}
	{s : State | rd in s.kinds.structure.elems} in rd.reference.~name.~kinds
}


/* ************************************************************************************************** */

run {} for 3 but exactly 1 ReferenceContainer, 1 State, 1 Kind, 2 Record, 2 Value
run {} for 3
