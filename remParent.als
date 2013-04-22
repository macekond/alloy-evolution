open model

pred remParent[disj k1, k2, k3 : Class, disj s1, s2 : State]{
	k1 in s1.classes
	k2 in s1.classes
	k3 not in s1.classes
	k2.parentName= k1.name

	#k1.instances = #k2.instances
	#k1.instances = 0

	s2.classes = s1.classes - k2 + k3
	
	k3.name = k2.name
	k3.structure = k2.structure
	k3.parentName= none
	k3.instances = k2.instances
}

run remParent

/* ***************************************************************************************** */

assert remParent_structure_same{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies 
			#s1.classes.structure.elems = #s2.classes.structure.elems		
}
check remParent_structure_same for 5

assert remParent_number_of_valueDefs_same{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies 
 			#({vc : Property | vc in s1.classes.structure.elems}) = #({vc : Property | vc in s2.classes.structure.elems})
}
check remParent_number_of_valueDefs_same  for 5

assert remParent_number_of_referenceDefs_same_after{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies
			#({rd : Reference | rd in s1.classes.structure.elems}) = #({vc : Reference | vc in s2.classes.structure.elems})
}
check remParent_number_of_referenceDefs_same_after for 5


assert remParent_number_of_classes_same{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies 
			#({k : Class | k in s1.classes}) = #({k : Class | k in s2.classes})
}
check remParent_number_of_classes_same for 5

assert remParent_number_of_values_same{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies
			#({k : ValueContainer | k in s1.classes.instances.items.elems}) = #({k : ValueContainer | k in s2.classes.instances.items.elems})
}
check remParent_number_of_values_same for 5 

assert remParent_not_change_number_of_references{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies
			#({k : ReferenceContainer | k in s1.classes.instances.items.elems}) = #({k : ReferenceContainer | k in s2.classes.instances.items.elems})
}
check remParent_not_change_number_of_references for 5

assert remParent_can_decrease_inheritace_depth{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies
			depth_decreased[s1, s2] or depth_preserved[s1,s2]
		
}
check remParent_can_decrease_inheritace_depth for 5

assert remParent_can_decrease_number_of_children{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies 
			children_preserve[s1,s2] or 	children_decrease[s1,s2]
}
check remParent_can_decrease_number_of_children for 5

assert remParent_not_change_cohesion_number{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		remParent[k1, k2, k3, s1, s2] implies
			coupling_preserve[s1, s2]
}
check remParent_not_change_cohesion_number for 5
