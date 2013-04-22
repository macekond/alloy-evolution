open model

pred merge[disj k1, k2, k3 : Class, disj s1, s2 : State]{
	k1.structure.elems & k2.structure.elems = none
	k2.name != k1.name

	k1 in s1.classes 
	k2 in s1.classes
	k3 not in s1.classes
	
	k3.name = k1.name
	k1.parentName= none
	no k' : Class | k' in s1.classes and k' != k1 and k1 in k'.*parent
	k3.parentName= none //inline would be different
	no k' : Class | k' in s1.classes and k' != k2 and k2 in k'.*parent
	k2.parentName= none
	no k' : Class | k' in s1.classes and k' != k3 and k3 in k'.*parent

	{no rd : Reference | rd.reference = k2.name and rd in s1.classes.structure.elems} implies {
		k3.structure = k1.structure.append[k2.structure]  
		and s2.classes = s1.classes - k1 - k2 + k3
	}else{	
			k1 not in s2.classes
			k2 not in s2.classes
			k3 in s2.classes
			#k3.structure.elems = add[#k1.structure.elems, #k2.structure.elems]
			#s2.classes.structure.elems = #s1.classes.structure.elems

			add[#s1.classes, -1] = #s2.classes
			
			all v : Def | v in k1.structure.append[k2.structure].elems and v.reference != k2.name implies
				k1.structure.append[k1.structure].idxOf[v] = k3.structure.idxOf[v]

			all v : Reference | v in k1.structure.append[k2.structure].elems and v.reference = k2.name implies
				one rd3 : Reference |
					k1.structure.append[k2.structure].idxOf[v] = k3.structure.idxOf[rd3] and rd3.reference = k3.name 
					and rd3 not in s1.classes.structure.elems 

			all v1 : Def | v1 in k1.structure.elems + k2.structure.elems and v1.reference != k2.name implies v1 in k3.structure.elems
	
			all k : Class |
				k in s1.classes and k !=k1 and k != k2 and k2.name not in k.structure.elems.reference implies
					k in s2.classes

			all k : Class |
				k in s1.classes and k !=k1 and k != k2 and k2.name in k.structure.elems.reference implies
					 k not in s2.classes and one k' : Class {
						k' in s2.classes  
						k' not in s1.classes
						k'.instances = k.instances 
						k.name = k'.name
						#k'.structure.elems = #k.structure.elems
						all v :  Def |
							 v in k.structure.elems and v.reference ! = k2.name implies
									k'.structure.idxOf[v] = k.structure.idxOf[v] 
						all rd : Reference | rd.reference = k2.name and rd in k.structure.elems implies
							one v' : Reference | 
								k'.structure.idxOf[v'] = k.structure.idxOf[rd] and  v'.reference = k3.name 
								and v' not in s1.classes.structure.elems and v' not in k3.structure.elems
		
					}
	}//end of else
	

	#k1.instances = #k2.instances or (#k1.instances > 0 and #k2.instances = 0) or (#k1.instances = 0 and #k2.instances > 0)
	
	#k1.instances = #k2.instances implies {
		#k3.instances = #k1.instances
		all r1 : Instance |
			r1 in k1.instances implies one r2 : Instance | r2 in k2.instances and r1.id = r2.id
 	
		all r3 : Instance |
			r3 in k3.instances implies one r1, r2 : Instance |
				r1 in k1.instances and r2 in k2.instances and r1.id = r2.id and r3.id = r1.id and
				r3.items = r1.items.append[r2.items]
	}
	
	//only if k2.structure = none
	#k1.instances > 0 and #k2.instances = 0 implies {
		#k3.instances = #k1.instances
		all r3 : Instance |
		r3 in k3.instances implies one r1 : Instance |
			r1 in k1.instances and r3.id = r1.id and #r1.items = #r3.items and
				all c : Container |
					c in r1.items.elems implies r3.items.idxOf[c] = r1.items.idxOf[c]

	}

	//only if k1.structure = none
	#k1.instances = 0 and #k2.instances > 0 implies {
		#k3.instances = #k2.instances	
		all r3 : Instance |
		r3 in k3.instances implies one r2 : Instance |
			r2 in k2.instances and r3.id = r2.id and #r2.items = #r3.items and
			all c : Container |
//					c in r2.items.elems implies r3.items.idxOf[c] = add[r2.items.idxOf[c], #k1.structure]
				r3.items.idxOf[c] = add[r2.items.idxOf[c], #k1.structure]
	}
	
}

pred merge_with_no_record_no_ref[disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances = 0 and #k2.instances = 0 and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record_no_ref for 3 but exactly 3 Class, 2 State, 0 Reference

pred merge_with_no_record[disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances = 0 and #k2.instances = 0 and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record for 3 but exactly 3 Class, 2 State

pred merge_with_record_in_one[disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances = 1 and #k2.instances = 0 and merge[k1, k2, k3, s1, s2]
}
run merge_with_record_in_one for 3 but exactly 3 Class, 2 State

pred merge_with_record_in_both[disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances = 1 and #k2.instances = 1 and merge[k1, k2, k3, s1, s2]
}
run merge_with_record_in_both for 3 but exactly 3 Class, 2 State

pred merge_with_record_and_values_in_both[disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances.items.values = 1 and #k2.instances.items.values = 1 and merge[k1, k2, k3, s1, s2]
}
run merge_with_record_and_values_in_both for 3 but exactly 3 Class, 2 State

pred merge_with_no_record_and_reference[disj k1, k2, k3 : Class, disj s1, s2 : State, rd : Reference]{
	#k1.instances = 0 and #k2.instances = 0 and rd.reference = k2.name and rd in k2.structure.elems  and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record_and_reference for 3 but exactly 3 Class, 2 State

pred merge_with_no_record_and_reference2[disj k1, k2, k3 : Class, disj s1, s2 : State, rd : Reference]{
	#k1.instances = 0 and #k2.instances = 0 and rd.reference = k2.name and rd in k1.structure.elems  and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record_and_reference2 for 3 but exactly 3 Class, 2 State

pred merge_with_no_record_and_reference_in_other[disj k, k1, k2, k3 : Class, disj s1, s2 : State, rd : Reference]{
	#k.instances = 0 and #k1.instances = 0 and #k2.instances = 0 and rd.reference = k2.name and rd in k.structure.elems and k in s1.classes and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record_and_reference_in_other for 3 but exactly 5 Class, 2 State

pred merge_with_no_record_and_no_reference_in_other[disj k, k1, k2, k3 : Class, disj s1, s2 : State]{
	#k.instances = 0 and #k1.instances = 0 and #k2.instances = 0  and k in s1.classes and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record_and_no_reference_in_other for 3 but exactly 4 Class, 2 State, 0 Reference


/* ***************************************************************************************** */

assert merge_structure_same{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		merge[k1, k2, k3, s1, s2] implies 
			#s1.classes.structure.elems = #s2.classes.structure.elems		
}
check merge_structure_same for 5

assert merge_number_of_valueDefs_same{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		merge[k1, k2, k3, s1, s2] implies  
 			#({vc : Property | vc in s1.classes.structure.elems}) = #({vc : Property | vc in s2.classes.structure.elems})
}
check merge_number_of_valueDefs_same  for 5

assert merge_number_of_referenceDefs_same_after{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		merge[k1, k2, k3, s1, s2] implies 
			#({rd : Reference | rd in s1.classes.structure.elems}) = #({vc : Reference | vc in s2.classes.structure.elems})
}
check merge_number_of_referenceDefs_same_after for 5


assert merge_number_of_classes_is_lower_after{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		merge[k1, k2, k3, s1, s2] implies 
			#({k : Class | k in s1.classes}) > #({k : Class | k in s2.classes})
}
check merge_number_of_classes_is_lower_after for 5

assert merge_not_change_number_of_values{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		merge[k1, k2, k3, s1, s2] implies 
			#({k : ValueContainer | k in s1.classes.instances.items.elems}) = #({k : ValueContainer | k in s2.classes.instances.items.elems})
}
check merge_not_change_number_of_values for 5 

assert merge_not_change_number_of_references{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		merge[k1, k2, k3, s1, s2] implies 
			#({k : ReferenceContainer | k in s1.classes.instances.items.elems}) = #({k : ReferenceContainer | k in s2.classes.instances.items.elems})
}
check merge_not_change_number_of_references for 5


assert merge_not_change_inheritace_depth{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		merge[k1, k2, k3, s1, s2]  implies
		all k : Class | k in s1.classes implies 
				depth_preserved[s1, s2]
}
check merge_not_change_inheritace_depth for 5

assert merge_not_change_number_of_children{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		merge[k1, k2, k3, s1, s2] implies 
			depth_preserved[s1,s2]
}
check merge_not_change_number_of_children for 5

assert merge_can_increase_cohesion_number{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		merge[k1, k2, k3, s1, s2]  implies
			coupling_preserve[s1, s2] or coupling_increase[s1, s2]
}
check merge_can_increase_cohesion_number for 5
