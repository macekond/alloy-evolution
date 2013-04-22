open model

pred addClass[k : Class, disj s1, s2 : State]{
	k not in s1.classes
	
	k.parentName= none
	#k.instances = 0

	s2.classes = s1.classes + k
}

assert addClass_structure_is_grater_or_equal_after{
	all k : Class, disj s1, s2 : State |
		addClass[k, s1, s2] implies 
			#s1.classes.structure.elems <= #s2.classes.structure.elems		
}
check addClass_structure_is_grater_or_equal_after for 5

assert addClass_number_of_valueDefs_increases_or_stay_same{
	all k : Class, disj s1, s2 : State |
		addClass[k, s1, s2] implies
 			#({vc : Property | vc in s1.classes.structure.elems}) <= #({vc : Property | vc in s2.classes.structure.elems})
}

check addClass_number_of_valueDefs_increases_or_stay_same  for 5

assert addClass_number_of_referenceDefs_equal_or_higher_after{
	all k : Class, disj s1, s2 : State |
		addClass[k, s1, s2] implies
			#({rd : Reference | rd in s1.classes.structure.elems}) <= #({vc : Reference | vc in s2.classes.structure.elems})
}
check addClass_number_of_referenceDefs_equal_or_higher_after for 5


assert addClass_number_of_classes_is_higher{
	all k : Class, disj s1, s2 : State |
		addClass[k, s1, s2] implies
			#({k : Class | k in s1.classes}) < #({k : Class | k in s2.classes})
}
check addClass_number_of_classes_is_higher for 5

assert addClass_not_change_number_of_values{
	all k : Class, disj s1, s2 : State |
		addClass[k, s1, s2] implies 
			#({k : ValueContainer | k in s1.classes.instances.items.elems}) = #({k : ValueContainer | k in s2.classes.instances.items.elems})
}
check addClass_not_change_number_of_values for 5

assert addClass_not_change_number_of_references{
	all k : Class, disj s1, s2 : State |
		addClass[k, s1, s2] implies 
			#({k : ReferenceContainer | k in s1.classes.instances.items.elems}) = #({k : ReferenceContainer | k in s2.classes.instances.items.elems})
}
check addClass_not_change_number_of_references for 5


assert   addClass_not_change_inheritace_depth{
	all k : Class, disj s1, s2 : State |
		addClass[k, s1, s2] implies 
			depth_preserved[s1, s2]
}
check  addClass_not_change_inheritace_depth for 5

assert addClass_not_change_number_of_children{
		all k : Class, disj s1, s2 : State |
		addClass[k, s1, s2] implies 
			children_preserve[s1,s2]
}
check  addClass_not_change_number_of_children for 5

assert addClass_can_increase_cohesion_number{
	all k : Class, disj s1, s2 : State |
		addClass[k, s1, s2] implies 
			coupling_preserve[s1, s2] or coupling_increase[s1, s2]
}
check  addClass_can_increase_cohesion_number for 5
