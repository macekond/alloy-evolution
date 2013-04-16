open model

pred copyValueDef[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	// k1 source of def
	// k2 target of copy
	// k3 result of copy
	k1 in s1.kinds
	k2 in s1.kinds
	k3 not in s1.kinds

	s2.kinds = s1.kinds - k2 + k3

	vd in k1.structure.elems and vd not in k2.structure.elems

	k2.name = k3.name
	k3.structure = k2.structure.add[vd]

	#k3.records = #k2.records
	all r2 : Record |
		r2 in k2.records implies one r3 : Record | 
			r2.id = r3.id and r3 in k3.records and 
				all c : Container | c in r2.items.elems implies r2.items.idxOf[c] = r3.items.idxOf[c]
	
/*	all r3 : Record |
		r3 in k3.records implies one r2 : Record | 
			r2.id = r3.id and r2 in k2.records and #r3.items = add[1, #r2.items] and
				all c : Container | r2.items.idxOf[c] = r3.items.idxOf[c]
		//	and r3.items.subseq[0, add[r3.items.lastIdx,-1]] = r2.items
*/
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
	#k2.records = 1 copyValueDef[vd, k1, k2, k3, s1, s2]
}
run copyValueDef_one_record_in_target for 13 but exactly 2 State, 3 Kind

/*
pred copyValueDef_one_record_in_target_test[r1, r2, r3 : Record, vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	r1 in k1.records and  !r1.items.hasDups and 
	r2 in k2.records and  !r2.items.hasDups and
	r3 in k3.records and  !r3.items.hasDups and
	copyValueDef[vd, k1, k2, k3, s1, s2]
}
run  copyValueDef_one_record_in_target_test for 4 but exactly 2 State, 3 Kind
*/
/* ***************************************************************************************** */

assert copyValueDef_structure_same_after{
	all vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State |
		copyValueDef[vd, k1, k2, k3, s1, s2] implies 
			#s1.kinds.structure.elems = #s2.kinds.structure.elems		
}
check copyValueDef_structure_same_after for 5

assert copyValueDef_number_of_valueDefs_same{
	all vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State |
		copyValueDef[vd, k1, k2, k3, s1, s2] implies 
 			#({vc : ValueDef | vc in s1.kinds.structure.elems}) = #({vc : ValueDef | vc in s2.kinds.structure.elems})
}

check copyValueDef_number_of_valueDefs_same  for 5

assert copyValueDef_number_of_referenceDefs_same_after{
	all vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State |
		copyValueDef[vd, k1, k2, k3, s1, s2] implies 
			#({rd : ReferenceDef | rd in s1.kinds.structure.elems}) = #({vc : ReferenceDef | vc in s2.kinds.structure.elems})
}
check copyValueDef_number_of_referenceDefs_same_after for 5


assert copyValueDef_number_of_kinds_is_same{
	all vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State |
		copyValueDef[vd, k1, k2, k3, s1, s2] implies 
			#({k : Kind | k in s1.kinds}) = #({k : Kind | k in s2.kinds})
}
check copyValueDef_number_of_kinds_is_same for 5

assert copyValueDef_increase_number_of_values{
	all vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State |
		copyValueDef[vd, k1, k2, k3, s1, s2] implies 
			#({k : ValueContainer | k in s1.kinds.records.items.elems}) <= #({k : ValueContainer | k in s2.kinds.records.items.elems})
}
check copyValueDef_increase_number_of_values for 5

assert copyValueDef_not_change_number_of_references{
	all vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State |
		copyValueDef[vd, k1, k2, k3, s1, s2] implies 
			#({k : ReferenceContainer | k in s1.kinds.records.items.elems}) = #({k : ReferenceContainer | k in s2.kinds.records.items.elems})
}
check copyValueDef_not_change_number_of_references for 5
