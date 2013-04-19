open model

pred addReferenceDef[rd : ReferenceDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	k2 not in s1.kinds
	k1 in s1.kinds
	s2.kinds = s1.kinds - k1 + k2

	k1.name = k2.name
	k1.parent = k2.parent

	rd not in k1.structure.elems

	rd.reference in s1.kinds.name and rd.reference in s2.kinds.name

	k2.structure = k1.structure.add[rd]
	
	#k1.records = #k2.records
	all r1 : Record |
		r1 in k1.records implies one r2 : Record |
			r2 in k2.records and r1.id = r2.id  and {
				all c1 : Container | c1 in r1.items.elems implies r1.items.idxOf[c1] = r2.items.idxOf[c1]
			}

	all r2 : Record |
		r2 in k2.records implies one r1 : Record |
			r1 in k1.records and r1.id = r2.id 
//r2.items.subseq[0, r2.items.lastIdx-1] = r1.items 
		
}

pred addReference_with_no_record[rd : ReferenceDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	k1.records = none and addReferenceDef[rd, k1, k2, s1, s2]
}
run addReference_with_no_record for 3 but exactly 2 State, 2 Kind

pred addReference_with_one_record[rd : ReferenceDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	#k1.records = 1 and addReferenceDef[rd, k1, k2, s1, s2]
}
run addReference_with_one_record for 4 but exactly 2 State, 2 Kind

pred addReference_on_other_with_no_record[rd : ReferenceDef, disj k1, k2, k3 : Kind, disj s1, s2 :  State]{
	rd.reference = k3.name and #k1.records = 0 and addReferenceDef[rd, k1, k2, s1, s2]
}
run addReference_on_other_with_no_record for 4 but exactly 2 State, 3 Kind

pred addReference_on_other_with_some_record[rd : ReferenceDef, disj k1, k2, k3 : Kind, disj s1, s2 :  State]{
	rd.reference = k3.name and #k1.records > 0 and addReferenceDef[rd, k1, k2, s1, s2]
}
run addReference_on_other_with_some_record for 4 but exactly 2 State, 3 Kind

assert addReferenceDef_structure_is_grater_or_equal_after{
	all rd : ReferenceDef, disj k1, k2 : Kind, disj s1, s2 :  State |
		addReferenceDef[rd, k1, k2, s1, s2] implies
			#s1.kinds.structure.elems <= #s2.kinds.structure.elems
}
check addReferenceDef_structure_is_grater_or_equal_after for 5

assert addReferenceDef_number_of_valueDefs_not_changed{
	all rd : ReferenceDef, disj k1, k2 : Kind, disj s1, s2 :  State |
		addReferenceDef[rd, k1, k2, s1, s2] implies
			#({vc : ValueDef | vc in s1.kinds.structure.elems}) = #({vc : ValueDef | vc in s2.kinds.structure.elems})
}
check addReferenceDef_number_of_valueDefs_not_changed for 5

assert addReferenceDef_number_of_referenceDefs_equal_or_higher_after{
	all rd : ReferenceDef, disj k1, k2 : Kind, disj s1, s2 :  State |
		addReferenceDef[rd, k1, k2, s1, s2] implies
			#({rd : ReferenceDef | rd in s1.kinds.structure.elems}) <= #({vc : ReferenceDef | vc in s2.kinds.structure.elems})
}
check addReferenceDef_number_of_referenceDefs_equal_or_higher_after for 5

assert addReferenceDef_number_of_kinds_is_equal{
		all rd : ReferenceDef, disj k1, k2 : Kind, disj s1, s2 :  State |
		addReferenceDef[rd, k1, k2, s1, s2] implies
			#({k : Kind | k in s1.kinds}) = #({k : Kind | k in s2.kinds})
}
check addReferenceDef_number_of_kinds_is_equal for 5

assert addReferenceDef_not_change_number_of_values{
	all rd : ReferenceDef, disj k1, k2 : Kind, disj s1, s2 :  State |
		addReferenceDef[rd, k1, k2, s1, s2] implies
			#({k : ValueContainer | k in s1.kinds.records.items.elems}) = #({k : ValueContainer | k in s2.kinds.records.items.elems})
}
check addReferenceDef_not_change_number_of_values for 5

assert addReferenceDef_increase_or_not_change_number_of_references{
	all rd : ReferenceDef, disj k1, k2 : Kind, disj s1, s2 :  State |
		addReferenceDef[rd, k1, k2, s1, s2] implies
			#({k : ReferenceContainer | k in s1.kinds.records.items.elems}) <= #({k : ReferenceContainer | k in s2.kinds.records.items.elems})
}
check addReferenceDef_increase_or_not_change_number_of_references  for 5


assert  addReferenceDef_not_change_inheritace_depth{
	all rd : ReferenceDef, disj k1, k2 : Kind, disj s1, s2 :  State |
		addReferenceDef[rd, k1, k2, s1, s2] implies 
			depth_preserved[s1, s2]
}
check addReferenceDef_not_change_inheritace_depth for 5

assert addReferenceDef_not_change_number_of_children{
	all rd : ReferenceDef, disj k1, k2 : Kind, disj s1, s2 :  State |
		addReferenceDef[rd, k1, k2, s1, s2] implies
			children_preserve[s1,s2]
}
check addReferenceDef_not_change_number_of_children for 5

assert addReferenceDef_can_increase_cohesion_number{
	all rd : ReferenceDef, disj k1, k2 : Kind, disj s1, s2 :  State |
		addReferenceDef[rd, k1, k2, s1, s2] implies
				coupling_preserve[s1, s2] or coupling_increase[s1, s2]	
}
check addReferenceDef_can_increase_cohesion_number for 5

