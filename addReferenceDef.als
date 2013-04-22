open model

pred addReference[rd : Reference, disj k1, k2 : Class, disj s1, s2 :  State]{
	k2 not in s1.classes
	k1 in s1.classes
	s2.classes = s1.classes - k1 + k2

	k1.name = k2.name
	k1.parentName= k2.parentName

	rd not in k1.structure.elems

	rd.reference in s1.classes.name and rd.reference in s2.classes.name

	k2.structure = k1.structure.add[rd]
	
	#k1.instances = #k2.instances
	all r1 : Instance |
		r1 in k1.instances implies one r2 : Instance |
			r2 in k2.instances and r1.id = r2.id  and {
				all c1 : Container | c1 in r1.items.elems implies r1.items.idxOf[c1] = r2.items.idxOf[c1]
			}

	all r2 : Instance |
		r2 in k2.instances implies one r1 : Instance |
			r1 in k1.instances and r1.id = r2.id 
//r2.items.subseq[0, r2.items.lastIdx-1] = r1.items 
		
}

pred addReference_with_no_record[rd : Reference, disj k1, k2 : Class, disj s1, s2 :  State]{
	k1.instances = none and addReference[rd, k1, k2, s1, s2]
}
run addReference_with_no_record for 3 but exactly 2 State, 2 Class

pred addReference_with_one_record[rd : Reference, disj k1, k2 : Class, disj s1, s2 :  State]{
	#k1.instances = 1 and addReference[rd, k1, k2, s1, s2]
}
run addReference_with_one_record for 4 but exactly 2 State, 2 Class

pred addReference_on_other_with_no_record[rd : Reference, disj k1, k2, k3 : Class, disj s1, s2 :  State]{
	rd.reference = k3.name and #k1.instances = 0 and addReference[rd, k1, k2, s1, s2]
}
run addReference_on_other_with_no_record for 4 but exactly 2 State, 3 Class

pred addReference_on_other_with_some_record[rd : Reference, disj k1, k2, k3 : Class, disj s1, s2 :  State]{
	rd.reference = k3.name and #k1.instances > 0 and addReference[rd, k1, k2, s1, s2]
}
run addReference_on_other_with_some_record for 4 but exactly 2 State, 3 Class

assert addReference_structure_is_grater_or_equal_after{
	all rd : Reference, disj k1, k2 : Class, disj s1, s2 :  State |
		addReference[rd, k1, k2, s1, s2] implies
			#s1.classes.structure.elems <= #s2.classes.structure.elems
}
check addReference_structure_is_grater_or_equal_after for 5

assert addReference_number_of_valueDefs_not_changed{
	all rd : Reference, disj k1, k2 : Class, disj s1, s2 :  State |
		addReference[rd, k1, k2, s1, s2] implies
			#({vc : Property | vc in s1.classes.structure.elems}) = #({vc : Property | vc in s2.classes.structure.elems})
}
check addReference_number_of_valueDefs_not_changed for 5

assert addReference_number_of_referenceDefs_equal_or_higher_after{
	all rd : Reference, disj k1, k2 : Class, disj s1, s2 :  State |
		addReference[rd, k1, k2, s1, s2] implies
			#({rd : Reference | rd in s1.classes.structure.elems}) <= #({vc : Reference | vc in s2.classes.structure.elems})
}
check addReference_number_of_referenceDefs_equal_or_higher_after for 5

assert addReference_number_of_classes_is_equal{
		all rd : Reference, disj k1, k2 : Class, disj s1, s2 :  State |
		addReference[rd, k1, k2, s1, s2] implies
			#({k : Class | k in s1.classes}) = #({k : Class | k in s2.classes})
}
check addReference_number_of_classes_is_equal for 5

assert addReference_not_change_number_of_values{
	all rd : Reference, disj k1, k2 : Class, disj s1, s2 :  State |
		addReference[rd, k1, k2, s1, s2] implies
			#({k : ValueContainer | k in s1.classes.instances.items.elems}) = #({k : ValueContainer | k in s2.classes.instances.items.elems})
}
check addReference_not_change_number_of_values for 5

assert addReference_increase_or_not_change_number_of_references{
	all rd : Reference, disj k1, k2 : Class, disj s1, s2 :  State |
		addReference[rd, k1, k2, s1, s2] implies
			#({k : ReferenceContainer | k in s1.classes.instances.items.elems}) <= #({k : ReferenceContainer | k in s2.classes.instances.items.elems})
}
check addReference_increase_or_not_change_number_of_references  for 5


assert  addReference_not_change_inheritace_depth{
	all rd : Reference, disj k1, k2 : Class, disj s1, s2 :  State |
		addReference[rd, k1, k2, s1, s2] implies 
			depth_preserved[s1, s2]
}
check addReference_not_change_inheritace_depth for 5

assert addReference_not_change_number_of_children{
	all rd : Reference, disj k1, k2 : Class, disj s1, s2 :  State |
		addReference[rd, k1, k2, s1, s2] implies
			children_preserve[s1,s2]
}
check addReference_not_change_number_of_children for 5

assert addReference_can_increase_cohesion_number{
	all rd : Reference, disj k1, k2 : Class, disj s1, s2 :  State |
		addReference[rd, k1, k2, s1, s2] implies
				coupling_preserve[s1, s2] or coupling_increase[s1, s2]	
}
check addReference_can_increase_cohesion_number for 5

