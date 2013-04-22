open model

pred remClass[k : Class, disj s1, s2 : State]{
	k in s1.classes

	no k' : Class | k' in s1.classes and k'.parentName= k.name
	no k' : Class | k' in s1.classes and some rd : Reference | rd in k'.structure.elems and rd.reference = k.name

	s2.classes = s1.classes - k
}

/* ***************************************************************************************** */

assert remClass_structure_less_or_equal_after{
	all k1 : Class, disj s1, s2 : State |
		remClass[k1, s1, s2] implies 
			#s1.classes.structure.elems >= #s2.classes.structure.elems		
}
check remClass_structure_less_or_equal_after for 5

assert remClass_number_of_valueDefs_same_or_less{
	all k1 : Class, disj s1, s2 : State |
		remClass[k1, s1, s2] implies   
 			#({vc : Property | vc in s1.classes.structure.elems}) >= #({vc : Property | vc in s2.classes.structure.elems})
}
check remClass_number_of_valueDefs_same_or_less  for 5

assert remClass_number_of_referenceDefs_same_or_less{
	all k1 : Class, disj s1, s2 : State |
		remClass[k1, s1, s2] implies 
			#({rd : Reference | rd in s1.classes.structure.elems}) >= #({vc : Reference | vc in s2.classes.structure.elems})
}
check remClass_number_of_referenceDefs_same_or_less for 5


assert remClass_number_of_classes_is_lower_after{
	all k1 : Class, disj s1, s2 : State |
		remClass[k1, s1, s2] implies
			#({k : Class | k in s1.classes}) > #({k : Class | k in s2.classes})
}
check remClass_number_of_classes_is_lower_after for 5

assert remClass_number_of_values_less_or_equal{
		all k1 : Class, disj s1, s2 : State |
		remClass[k1, s1, s2] implies
			#({k : ValueContainer | k in s1.classes.instances.items.elems}) >= #({k : ValueContainer | k in s2.classes.instances.items.elems})
}
check remClass_number_of_values_less_or_equal for 5 

assert remClass_number_of_references_less_or_equal{
	all k1 : Class, disj s1, s2 : State |
		remClass[k1, s1, s2] implies
			#({k : ReferenceContainer | k in s1.classes.instances.items.elems}) >= #({k : ReferenceContainer | k in s2.classes.instances.items.elems})
}
check remClass_number_of_references_less_or_equal for 5

assert remClass_can_decrease_inheritace_depth{
	all k1 : Class, disj s1, s2 : State |
		remClass[k1, s1, s2] implies
			depth_decreased[s1, s2] or depth_preserved[s1,s2]
}
check remClass_can_decrease_inheritace_depth for 5

assert remClass_can_decrease_number_of_children{
		all k1 : Class, disj s1, s2 : State |
		remClass[k1, s1, s2] implies 
			children_preserve[s1,s2] or 	children_decrease[s1,s2]
}
check remClass_can_decrease_number_of_children for 5

assert remClass_can_decrease_cohesion_number{
	all k1 : Class, disj s1, s2 : State |
		remClass[k1, s1, s2] implies
				coupling_preserve[s1, s2] or coupling_decrease[s1,s2]
}
check remClass_can_decrease_cohesion_number for 5



