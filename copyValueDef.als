open model

pred copyValueDef[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	// k1 source of def
	// k2 target of copy
	// k3 result of copy
	k1 in s1.kinds
	k2 in s1.kinds
	k3 not in s1.kinds
	
	k2.parent = k3.parent

	s2.kinds = s1.kinds - k2 + k3

	vd in k1.structure.elems and vd not in k2.structure.elems

	k2.name = k3.name
	k3.structure = k2.structure.add[vd]

	#k3.records = #k2.records
	all r2 : Record |
		r2 in k2.records implies one r3 : Record | 
			r2.id = r3.id and r3 in k3.records and 
				all c : Container | c in r2.items.elems implies r2.items.idxOf[c] = r3.items.idxOf[c]
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
run copyValueDef_one_record_in_target for 5 but exactly 2 State, 3 Kind

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

assert  copyValueDef_not_change_inheritace_depth{
	all vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State |
		copyValueDef[vd, k1, k2, k3, s1, s2]  implies
			depth_preserved[s1, s2]
}
check copyValueDef_not_change_inheritace_depth for 5

assert copyValueDef_not_change_number_of_children{
	all vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State |
		copyValueDef[vd, k1, k2, k3, s1, s2]   implies 
			children_preserve[s1,s2]
}
check copyValueDef_not_change_number_of_children for 5

assert copyValueDef_not_change_cohesion_number{
	all vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State |
		copyValueDef[vd, k1, k2, k3, s1, s2]   implies
			coupling_preserve[s1,s2]
}
check copyValueDef_not_change_cohesion_number for 5

