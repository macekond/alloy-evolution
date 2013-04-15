open model

pred remKind[k : Kind, disj s1, s2 : State]{
	k in s1.kinds
	s2.kinds = s1.kinds - k
}

/* ***************************************************************************************** */

assert remKind_structure_less_or_equal_after{
	all k1 : Kind, disj s1, s2 : State |
		remKind[k1, s1, s2] implies 
			#s1.kinds.structure.elems >= #s2.kinds.structure.elems		
}
check remKind_structure_less_or_equal_after for 5

assert remKind_number_of_valueDefs_same_or_less{
	all k1 : Kind, disj s1, s2 : State |
		remKind[k1, s1, s2] implies   
 			#({vc : ValueDef | vc in s1.kinds.structure.elems}) >= #({vc : ValueDef | vc in s2.kinds.structure.elems})
}
check remKind_number_of_valueDefs_same_or_less  for 5

assert remKind_number_of_referenceDefs_same_or_less{
	all k1 : Kind, disj s1, s2 : State |
		remKind[k1, s1, s2] implies 
			#({rd : ReferenceDef | rd in s1.kinds.structure.elems}) >= #({vc : ReferenceDef | vc in s2.kinds.structure.elems})
}
check remKind_number_of_referenceDefs_same_or_less for 5


assert remKind_number_of_kinds_is_lower_after{
	all k1 : Kind, disj s1, s2 : State |
		remKind[k1, s1, s2] implies
			#({k : Kind | k in s1.kinds}) > #({k : Kind | k in s2.kinds})
}
check remKind_number_of_kinds_is_lower_after for 5

assert remKind_number_of_values_less_or_equal{
		all k1 : Kind, disj s1, s2 : State |
		remKind[k1, s1, s2] implies
			#({k : ValueContainer | k in s1.kinds.records.items.elems}) >= #({k : ValueContainer | k in s2.kinds.records.items.elems})
}
check remKind_number_of_values_less_or_equal for 5 

assert remKind_number_of_references_less_or_equal{
	all k1 : Kind, disj s1, s2 : State |
		remKind[k1, s1, s2] implies
			#({k : ReferenceContainer | k in s1.kinds.records.items.elems}) >= #({k : ReferenceContainer | k in s2.kinds.records.items.elems})
}
check remKind_number_of_references_less_or_equal for 5

