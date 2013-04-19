open model

pred remParent[disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	k1 in s1.kinds
	k2 in s1.kinds
	k3 not in s1.kinds
	k2.parent = k1.name

	#k1.records = #k2.records
	#k1.records = 0

	s2.kinds = s1.kinds - k2 + k3
	
	k3.name = k2.name
	k3.structure = k2.structure
	k3.parent = none
	k3.records = k2.records
}

run remParent

/* ***************************************************************************************** */

assert remParent_structure_same{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies 
			#s1.kinds.structure.elems = #s2.kinds.structure.elems		
}
check remParent_structure_same for 5

assert remParent_number_of_valueDefs_same{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies 
 			#({vc : ValueDef | vc in s1.kinds.structure.elems}) = #({vc : ValueDef | vc in s2.kinds.structure.elems})
}
check remParent_number_of_valueDefs_same  for 5

assert remParent_number_of_referenceDefs_same_after{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies
			#({rd : ReferenceDef | rd in s1.kinds.structure.elems}) = #({vc : ReferenceDef | vc in s2.kinds.structure.elems})
}
check remParent_number_of_referenceDefs_same_after for 5


assert remParent_number_of_kinds_same{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies 
			#({k : Kind | k in s1.kinds}) = #({k : Kind | k in s2.kinds})
}
check remParent_number_of_kinds_same for 5

assert remParent_number_of_values_same{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies
			#({k : ValueContainer | k in s1.kinds.records.items.elems}) = #({k : ValueContainer | k in s2.kinds.records.items.elems})
}
check remParent_number_of_values_same for 5 

assert remParent_not_change_number_of_references{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies
			#({k : ReferenceContainer | k in s1.kinds.records.items.elems}) = #({k : ReferenceContainer | k in s2.kinds.records.items.elems})
}
check remParent_not_change_number_of_references for 5

assert remParent_can_decrease_inheritace_depth{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies
			depth_decreased[s1, s2] or depth_preserved[s1,s2]
		
}
check remParent_can_decrease_inheritace_depth for 5

assert remParent_can_decrease_number_of_children{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies 
			children_preserve[s1,s2] or 	children_decrease[s1,s2]
}
check remParent_can_decrease_number_of_children for 5

assert remParent_not_change_cohesion_number{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies
			coupling_preserve[s1, s2]
}
check remParent_not_change_cohesion_number for 5
