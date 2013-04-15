open model

pred addKind[k : Kind, disj s1, s2 : State]{
	k not in s1.kinds
	#k.records = 0

	s2.kinds = s1.kinds + k
}

assert addKind_structure_is_grater_or_equal_after{
	all k : Kind, disj s1, s2 : State |
		addKind[k, s1, s2] implies 
			#s1.kinds.structure.elems <= #s2.kinds.structure.elems		
}
check addKind_structure_is_grater_or_equal_after for 5

assert addKind_number_of_valueDefs_increases_or_stay_same{
	all k : Kind, disj s1, s2 : State |
		addKind[k, s1, s2] implies
 			#({vc : ValueDef | vc in s1.kinds.structure.elems}) <= #({vc : ValueDef | vc in s2.kinds.structure.elems})
}

check addKind_number_of_valueDefs_increases_or_stay_same  for 5

assert addKind_number_of_referenceDefs_equal_or_higher_after{
	all k : Kind, disj s1, s2 : State |
		addKind[k, s1, s2] implies
			#({rd : ReferenceDef | rd in s1.kinds.structure.elems}) <= #({vc : ReferenceDef | vc in s2.kinds.structure.elems})
}
check addKind_number_of_referenceDefs_equal_or_higher_after for 5


assert addKind_number_of_kinds_is_higher{
	all k : Kind, disj s1, s2 : State |
		addKind[k, s1, s2] implies
			#({k : Kind | k in s1.kinds}) < #({k : Kind | k in s2.kinds})
}
check addKind_number_of_kinds_is_higher for 5

assert addKind_not_change_number_of_values{
	all k : Kind, disj s1, s2 : State |
		addKind[k, s1, s2] implies 
			#({k : ValueContainer | k in s1.kinds.records.items.elems}) = #({k : ValueContainer | k in s2.kinds.records.items.elems})
}
check addKind_not_change_number_of_values for 5

assert addKind_not_change_number_of_references{
	all k : Kind, disj s1, s2 : State |
		addKind[k, s1, s2] implies 
			#({k : ReferenceContainer | k in s1.kinds.records.items.elems}) = #({k : ReferenceContainer | k in s2.kinds.records.items.elems})
}
check addKind_not_change_number_of_references for 5
