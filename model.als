sig State{
	kinds : set Kind
}

sig Kind{
	parent : lone Name,
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
	//values : set (Value + Int)
}{
	some r : Record |
		this in r.items.elems
	
	all disj k1, k2 : Kind |
		this in k1.records.items.elems and this in k2.records.items.elems implies k1.~kinds & k2.~kinds = none


}

sig ValueContainer extends Container{
	
}{
	//values in Value
	//#values >= 1
}

sig ReferenceContainer extends Container{
		values : set Int
}{

}

/*
sig Value{}{
	one vc : ValueContainer |
		this in vc.values
}
*/
sig Name{}{
	some k : Kind |
		this in k.name
}

abstract sig Def{

}{
	some k : Kind |
		this in k.structure.elems
}

sig ValueDef extends Def{

}


sig ReferenceDef extends Def{
	reference : one Name
}{

}

/* ************************************************************************************************** */
fact not_same_ids_in_kinds{
	all disj r1, r2 : Record |
		r1.id = r2.id implies r1.(~records) != r2.(~records)

	//no duplicate ids
	all k : Kind, disj r1, r2 : Record |
		r1 in k.records and r2 in k.records implies r1.id != r2.id
}

fact not_same_name_of_kinds_in_same_states{
	all disj k1, k2 : Kind |
		k1.name = k2.name implies no s : State | s in k1.~kinds and s in k2.~kinds
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

fact no_same_defs_in_kinds_of_a_state{
	all disj k1, k2 : Kind, d : Def |
		d in k1.structure.elems and d in k2.structure.elems implies k1.~kinds != k2.~kinds
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
	{s : State | rd in s.kinds.structure.elems} in rd.reference.~name.~kinds
}

fact no_overriding{
	all disj k1, k2 : Kind |
		k1.parent = k2.name implies
			no d : Def | d in k1.structure.elems and d in k2.structure.elems
}

fact parent_and_child_in_same_states{
	all k1, k2 : Kind |
		k1.parent = k2.name implies some s : State | s in k1.~kinds and s in k2.~kinds
}

fact no_cyclical_inheritance{
	all k1, k2 : Kind |
		k1.parent = k2.name implies k1.name not in k2.*parent
}

fact ids_in_hierarchy_are_same{
	all disj k1, k2 : Kind |
		k1.parent = k2.name and k1.~kinds in k2.~kinds implies 
			all r1 : Record | r1 in k1.records implies 
				one r2 : Record | r2 in k2.records and r1.id = r2.id
}



/* ************************************************************************************************** */

run {} for 3 but exactly 1 ReferenceContainer, 1 State, 1 Kind, 2 Record
run {
	some k1, k2, k3 : Kind |
		k1.parent = k2.name and k2.parent = k3.name //and k1 = k3
} for 4 but exactly 2 State
