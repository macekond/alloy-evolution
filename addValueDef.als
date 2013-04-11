open model

pred addValueDef[vd : ValueDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	k2 not in s1.kinds
	s2.kinds = (s1.kinds - k1) + k2

	vd not in k1.structure.elems 

	k2.structure = k1.structure.add[vd]
	k2.name = k1.name
	
	#k1.records = #k2.records
	all r2 : Record |
		r2 in k2.records implies 
			one r1 : Record | r1 in k1.records and r1.id = r2.id 
				and r1.items.add[r2.items.last] = r2.items 
}

pred addValue_with_no_record[vd : ValueDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	k1.records = none and addValueDef[vd, k1, k2, s1, s2]
}
run addValue_with_no_record for 3 but exactly 2 State, 2 Kind

pred addValue_with_no_record_but_reference[vd : ValueDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	k1.records = none and one ref : ReferenceDef | ref in k1.structure.elems and addValueDef[vd, k1, k2, s1, s2]
}
run addValue_with_no_record_but_reference for 3 but exactly 2 State, 3 Kind

pred addValue_with_no_record_but_reference_on_self[rd: ReferenceDef, vd : ValueDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	k1.records = none 
	and rd.reference = k1.name
	and rd  in k1.structure.elems
	and addValueDef[vd, k1, k2, s1, s2]
}
run addValue_with_no_record_but_reference_on_self for 3 but exactly 2 State, 2 Kind



pred addValue_with_one_record[vd : ValueDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	#k1.records = 1 and addValueDef[vd, k1, k2, s1, s2]
}
run addValue_with_one_record for 2 but exactly 2 State, 2 Kind, 0 ReferenceDef

pred addValue_with_one_record_and_reference_on_self[rd: ReferenceDef, vd : ValueDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	#k1.records = 1
	and rd.reference = k1.name
	and rd  in k1.structure.elems
	and addValueDef[vd, k1, k2, s1, s2]
}
run addValue_with_one_record_and_reference_on_self for 4 but exactly 2 State, 2 Kind

pred addValue_with_one_record_and_reference_on_self_from_other[rd: ReferenceDef, vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 :  State]{
	#k1.records = 1
	and rd.reference = k1.name
	and rd  in k3.structure.elems
	and k3 in s1.kinds
	and addValueDef[vd, k1, k2, s1, s2]
}
run addValue_with_one_record_and_reference_on_self_from_other for 4 but exactly 2 State
