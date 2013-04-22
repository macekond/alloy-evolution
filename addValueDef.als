open model

pred addProperty[vd : Property, disj k1, k2 : Class, disj s1, s2 :  State]{
	k2 not in s1.classes
	k1 in s1.classes
	s2.classes = (s1.classes - k1) + k2

	vd not in k1.structure.elems 

	k1.parentName= k2.parentName

	k2.structure = k1.structure.add[vd]
	k2.name = k1.name
	
	#k1.instances = #k2.instances
	all r2 : Instance |
		r2 in k2.instances implies 
			one r1 : Instance | r1 in k1.instances and r1.id = r2.id and 
				{all c : Container | c in r1.items.elems implies r1.items.idxOf[c] = r2.items.idxOf[c]} and
				{all c : Container | c in r2.items.elems and r2.items.idxOf[c] != r2.items.lastIdx implies r1.items.idxOf[c] = r2.items.idxOf[c]}
}

pred addValue_with_no_record[vd : Property, disj k1, k2 : Class, disj s1, s2 :  State]{
	k1.instances = none and addProperty[vd, k1, k2, s1, s2]
}
run addValue_with_no_record for 3 but exactly 2 State, 2 Class

pred addValue_with_no_record_but_reference[vd : Property, disj k1, k2 : Class, disj s1, s2 :  State]{
	k1.instances = none and one ref : Reference | ref in k1.structure.elems and addProperty[vd, k1, k2, s1, s2]
}
run addValue_with_no_record_but_reference for 3 but exactly 2 State, 3 Class

pred addValue_with_no_record_but_reference_on_self[rd: Reference, vd : Property, disj k1, k2 : Class, disj s1, s2 :  State]{
	k1.instances = none 
	and rd.reference = k1.name
	and rd  in k1.structure.elems
	and addProperty[vd, k1, k2, s1, s2]
}
run addValue_with_no_record_but_reference_on_self for 3 but exactly 2 State, 2 Class

pred addValue_with_one_record[vd : Property, disj k1, k2 : Class, disj s1, s2 :  State]{
	#k1.instances = 1 and addProperty[vd, k1, k2, s1, s2]
}
run addValue_with_one_record for 6 but exactly 2 State, 2 Class, 0 Reference

pred addValue_with_one_record_and_reference_on_self[rd: Reference, vd : Property, disj k1, k2 : Class, disj s1, s2 :  State]{
	#k1.instances = 1
	and rd.reference = k1.name
	and rd  in k1.structure.elems
	and addProperty[vd, k1, k2, s1, s2]
}
run addValue_with_one_record_and_reference_on_self for 4 but exactly 2 State, 2 Class

pred addValue_with_one_record_and_reference_on_self_from_other[rd: Reference, vd : Property, disj k1, k2, k3 : Class, disj s1, s2 :  State]{
	#k1.instances = 1
	and rd.reference = k1.name
	and rd  in k3.structure.elems
	and k3 in s1.classes
	and addProperty[vd, k1, k2, s1, s2]
}
run addValue_with_one_record_and_reference_on_self_from_other for 4 but exactly 2 State

/* ***************************************************************************************** */

assert addProperty_structure_is_grater_or_equal_after{
	all k1, k2 : Class, disj s1, s2 : State, vd : Property |
		addProperty[vd, k1, k2, s1, s2] implies 
			#s1.classes.structure.elems <= #s2.classes.structure.elems		
}
check addProperty_structure_is_grater_or_equal_after for 5

assert addProperty_number_of_valueDefs_increases_or_stay_same{
	all k1, k2 : Class, disj s1, s2 : State, vd : Property |
		addProperty[vd, k1, k2, s1, s2] implies 
 			#({vc : Property | vc in s1.classes.structure.elems}) <= #({vc : Property | vc in s2.classes.structure.elems})
}

check addProperty_number_of_valueDefs_increases_or_stay_same  for 5

assert addProperty_number_of_referenceDefs_same_after{
	all k1, k2 : Class, disj s1, s2 : State, vd : Property |
		addProperty[vd, k1, k2, s1, s2] implies 
			#({rd : Reference | rd in s1.classes.structure.elems}) = #({vc : Reference | vc in s2.classes.structure.elems})
}
check addProperty_number_of_referenceDefs_same_after for 5


assert addvalueDef_number_of_classes_is_same{
	all k1, k2 : Class, disj s1, s2 : State, vd : Property |
		addProperty[vd, k1, k2, s1, s2] implies 
			#({k : Class | k in s1.classes}) = #({k : Class | k in s2.classes})
}
check addvalueDef_number_of_classes_is_same for 5

assert addProperty_increase_number_of_values{
	all k1, k2 : Class, disj s1, s2 : State, vd : Property |
		addProperty[vd, k1, k2, s1, s2] implies  
			#({k : ValueContainer | k in s1.classes.instances.items.elems}) <= #({k : ValueContainer | k in s2.classes.instances.items.elems})
}
check addProperty_increase_number_of_values for 5

assert addProperty_not_change_number_of_references{
	all k1, k2 : Class, disj s1, s2 : State, vd : Property |
		addProperty[vd, k1, k2, s1, s2] implies  
			#({k : ReferenceContainer | k in s1.classes.instances.items.elems}) = #({k : ReferenceContainer | k in s2.classes.instances.items.elems})
}
check addProperty_not_change_number_of_references for 5 


assert  addProperty_not_change_inheritace_depth{
	all k1, k2 : Class, disj s1, s2 : State, vd : Property |
		addProperty[vd, k1, k2, s1, s2] implies  
		all k : Class | k in s1.classes implies 
			depth_preserved[s1, s2]
}
check addProperty_not_change_inheritace_depth for 5

assert addProperty_not_change_number_of_children{
	all k1, k2 : Class, disj s1, s2 : State, vd : Property |
		addProperty[vd, k1, k2, s1, s2] implies  
			children_preserve[s1,s2]
}
check addProperty_not_change_number_of_children for 5

assert addProperty_not_change_cohesion_number{
	all k1, k2 : Class, disj s1, s2 : State, vd : Property |
		addProperty[vd, k1, k2, s1, s2] implies  
			coupling_preserve[s1, s2] 
}
check addProperty_not_change_cohesion_number for 5
