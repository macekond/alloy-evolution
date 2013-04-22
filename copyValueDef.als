open model

pred copyProperty[vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State]{
	// k1 source of def
	// k2 target of copy
	// k3 result of copy
	k1 in s1.classes
	k2 in s1.classes
	k3 not in s1.classes
	
	k2.parentName= k3.parentName

	s2.classes = s1.classes - k2 + k3

	vd in k1.structure.elems and vd not in k2.structure.elems

	k2.name = k3.name
	k3.structure = k2.structure.add[vd]

	#k3.instances = #k2.instances
	all r2 : Instance |
		r2 in k2.instances implies one r3 : Instance | 
			r2.id = r3.id and r3 in k3.instances and 
				all c : Container | c in r2.items.elems implies r2.items.idxOf[c] = r3.items.idxOf[c]
}

pred copyProperty_no_record[vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances = 0 and #k2.instances = 0 and copyProperty[vd, k1, k2, k3, s1, s2]
}
run copyProperty_no_record for 3 but exactly 2 State, 3 Class

pred copyProperty_no_record_in_target[vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k2.instances = 0 and copyProperty[vd, k1, k2, k3, s1, s2]
}
run copyProperty_no_record_in_target for 3 but exactly 2 State, 3 Class

pred copyProperty_one_record_in_target[vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k2.instances = 1 copyProperty[vd, k1, k2, k3, s1, s2]
}
run copyProperty_one_record_in_target for 5 but exactly 2 State, 3 Class

/* ***************************************************************************************** */

assert copyProperty_structure_same_after{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		copyProperty[vd, k1, k2, k3, s1, s2] implies 
			#s1.classes.structure.elems = #s2.classes.structure.elems		
}
check copyProperty_structure_same_after for 5

assert copyProperty_number_of_valueDefs_same{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		copyProperty[vd, k1, k2, k3, s1, s2] implies 
 			#({vc : Property | vc in s1.classes.structure.elems}) = #({vc : Property | vc in s2.classes.structure.elems})
}
check copyProperty_number_of_valueDefs_same  for 5

assert copyProperty_number_of_referenceDefs_same_after{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		copyProperty[vd, k1, k2, k3, s1, s2] implies 
			#({rd : Reference | rd in s1.classes.structure.elems}) = #({vc : Reference | vc in s2.classes.structure.elems})
}
check copyProperty_number_of_referenceDefs_same_after for 5


assert copyProperty_number_of_classes_is_same{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		copyProperty[vd, k1, k2, k3, s1, s2] implies 
			#({k : Class | k in s1.classes}) = #({k : Class | k in s2.classes})
}
check copyProperty_number_of_classes_is_same for 5

assert copyProperty_increase_number_of_values{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		copyProperty[vd, k1, k2, k3, s1, s2] implies 
			#({k : ValueContainer | k in s1.classes.instances.items.elems}) <= #({k : ValueContainer | k in s2.classes.instances.items.elems})
}
check copyProperty_increase_number_of_values for 5

assert copyProperty_not_change_number_of_references{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		copyProperty[vd, k1, k2, k3, s1, s2] implies 
			#({k : ReferenceContainer | k in s1.classes.instances.items.elems}) = #({k : ReferenceContainer | k in s2.classes.instances.items.elems})
}
check copyProperty_not_change_number_of_references for 5

assert  copyProperty_not_change_inheritace_depth{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		copyProperty[vd, k1, k2, k3, s1, s2]  implies
			depth_preserved[s1, s2]
}
check copyProperty_not_change_inheritace_depth for 5

assert copyProperty_not_change_number_of_children{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		copyProperty[vd, k1, k2, k3, s1, s2]   implies 
			children_preserve[s1,s2]
}
check copyProperty_not_change_number_of_children for 5

assert copyProperty_not_change_cohesion_number{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		copyProperty[vd, k1, k2, k3, s1, s2]   implies
			coupling_preserve[s1,s2]
}
check copyProperty_not_change_cohesion_number for 5

