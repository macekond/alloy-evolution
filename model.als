sig State{
	kinds : set Kind
}

sig Kind{
	records : set Record,
	structure : set ValueDef
}{
	some s : State |
		this in s.kinds
}

sig Record{
	items : set ValueContainer,
	id : Int
}{
	one k : Kind |
		this in k.records
	
	all vd : ValueDef |
		vd in (this.~records).structure implies one vc : ValueContainer | vc.def = vd and vc in items
}

sig ValueContainer{
	values : set Value,
	def : one ValueDef
}{
	some r : Record |
		this in r.items

	def in (this.~items.~records).structure

	#values >= 1
}


sig Value{}{
	one vc : ValueContainer |
		this in vc.values
}

sig ValueDef{}{
	some k : Kind |
		this in k.structure
}

fact not_same_ids_in_kinds{
	all disj r1, r2 : Record |
		r1.id = r2.id implies r1.(~records) != r2.(~records)
}

fact not_same_vc_in_kinds{
	all disj r1, r2 : Record, vc : ValueContainer |
		r1 in vc.~items and r2 in vc.~items implies r1.(~records) != r2.(~records)
}


fact same_structure_in_kind{
	all r1, r2 : Record |
		r1.~records = r2.~records implies r1.items.def = r2.items.def
}

fact different_definitions_in_record{
	all r : Record, disj vc1, vc2 : ValueContainer |
		vc1 in r.items and vc2 in r.items implies vc1.def != vc2.def
}
