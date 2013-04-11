open model

pred copyValueDef[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	// k1 source of def
	// k2 target of copy
	// k3 result of copy
	
	s2.kinds = s1.kinds - k2 + k3

	vd in k1.structure.elems and vd not in k2.structure.elems

	k2.name = k3.name
	k3.structure = k2.structure.add[vd]

	#k3.records = #k2.records
	all r3 : Record |
		r3 in k3.records implies one r2 : Record | 
			r2.id = r3.id and r2 in k2.records and #r3.items = add[1, #r2.items] 
			and r3.items.subseq[0, add[r3.items.lastIdx,-1]] = r2.items

	//references are ok - the name and ids preserve
}

pred copyValueDef_no_record[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records = 0 and #k2.records = 0 and copyValueDef[vd, k1, k2, k3, s1, s2]
}
run copyValueDef_no_record for 3 but exactly 2 State, 3 Kind

pred copyValueDef_no_record_in_target[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k2.records = 0 and copyValueDef[vd, k1, k2, k3, s1, s2]
}
run copyValueDef_no_record_in_target for 3 but exactly 2 State, 3 Kind

pred copyValueDef_one_record_in_target[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k2.records = 1 and copyValueDef[vd, k1, k2, k3, s1, s2]
}
run copyValueDef_one_record_in_target for 3 but exactly 2 State, 3 Kind
