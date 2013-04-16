open model

pred addValueDef[vd : ValueDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	k2 not in s1.kinds
	k1 in s1.kinds
	s2.kinds = (s1.kinds - k1) + k2

	vd not in k1.structure.elems 

	k2.structure = k1.structure.add[vd]
	k2.name = k1.name
	
	#k1.records = #k2.records
	all r2 : Record |
		r2 in k2.records implies 
			one r1 : Record | r1 in k1.records and r1.id = r2.id and 
				all c : Container | c in r1.items.elems implies r1.items.idxOf[c] = r2.items.idxOf[c]
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
run addValue_with_one_record for 6 but exactly 2 State, 2 Kind, 0 ReferenceDef

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

/* ***************************************************************************************** */

assert addValueDef_structure_is_grater_or_equal_after{
	all k1, k2 : Kind, disj s1, s2 : State, vd : ValueDef |
		addValueDef[vd, k1, k2, s1, s2] implies 
			#s1.kinds.structure.elems <= #s2.kinds.structure.elems		
}
check addValueDef_structure_is_grater_or_equal_after for 5

assert addValueDef_number_of_valueDefs_increases_or_stay_same{
	all k1, k2 : Kind, disj s1, s2 : State, vd : ValueDef |
		addValueDef[vd, k1, k2, s1, s2] implies 
 			#({vc : ValueDef | vc in s1.kinds.structure.elems}) <= #({vc : ValueDef | vc in s2.kinds.structure.elems})
}

check addValueDef_number_of_valueDefs_increases_or_stay_same  for 5

assert addValueDef_number_of_referenceDefs_same_after{
	all k1, k2 : Kind, disj s1, s2 : State, vd : ValueDef |
		addValueDef[vd, k1, k2, s1, s2] implies 
			#({rd : ReferenceDef | rd in s1.kinds.structure.elems}) = #({vc : ReferenceDef | vc in s2.kinds.structure.elems})
}
check addValueDef_number_of_referenceDefs_same_after for 5


assert addvalueDef_number_of_kinds_is_same{
	all k1, k2 : Kind, disj s1, s2 : State, vd : ValueDef |
		addValueDef[vd, k1, k2, s1, s2] implies 
			#({k : Kind | k in s1.kinds}) = #({k : Kind | k in s2.kinds})
}
check addvalueDef_number_of_kinds_is_same for 5

assert addValueDef_increase_number_of_values{
	all k1, k2 : Kind, disj s1, s2 : State, vd : ValueDef |
		addValueDef[vd, k1, k2, s1, s2] implies  
			#({k : ValueContainer | k in s1.kinds.records.items.elems}) <= #({k : ValueContainer | k in s2.kinds.records.items.elems})
}
check addValueDef_increase_number_of_values for 5

assert addValueDef_not_change_number_of_references{
	all k1, k2 : Kind, disj s1, s2 : State, vd : ValueDef |
		addValueDef[vd, k1, k2, s1, s2] implies  
			#({k : ReferenceContainer | k in s1.kinds.records.items.elems}) = #({k : ReferenceContainer | k in s2.kinds.records.items.elems})
}
check addValueDef_not_change_number_of_references for 5
