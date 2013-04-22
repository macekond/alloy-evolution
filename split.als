open model

pred splitStructure[vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State]{
	k1 in s1.classes
	k2 not in s1.classes
	k3 not in s1.classes
	s2.classes = s1.classes - k1 + k3 + k2

	k1.name = k2.name	

	vd in k1.structure.elems
	k3.structure.elems = vd
	vd not in k2.structure.elems
	
	k1.parentName= none
	k2.parentName= none
	k3.parentName= none	
	{no k : Class | k in s2.classes and k.parentName= k3.name}

	#k1.instances = #k2.instances
	#k1.instances = #k3.instances

	k1.structure.idxOf[vd]	= 0 implies {
			k2.structure = k1.structure.rest
			
			all r2 : Instance |
			r2 in k2.instances implies one r1, r3 : Instance |
				 r1 in k1.instances and 
				 r2.id = r1.id and r2.items = 	r1.items.rest
				and r3 in k3.instances
				 and r3.id = r1.id and r3.items = r1.items.subseq[0, 0]		
	}
	else	k1.structure.idxOf[vd]	= k1.structure.lastIdx implies {
		k2.structure.add[vd] = k1.structure
		all r2 : Instance |
			r2 in k2.instances implies one r1, r3 : Instance |
				 r1 in k1.instances and 
				 r2.id = r1.id and r2.items.add[r1.items.last] = r1.items
				and r3 in k3.instances
				and r3.id = r1.id and r3.items =  r1.items.subseq[0, r1.items.lastIdx - 1]
	} 
	else {
		k2.structure = k1.structure.subseq[0, k1.structure.idxOf[vd]-1].append[k1.structure.subseq[k1.structure.idxOf[vd] +1, #k1.structure.elems]]
		
		all r2 : Instance |
			r2 in k2.instances implies one r1, r3 : Instance |
				 r1 in k1.instances and 
				 r2.id = r1.id and r2.items = r1.items.subseq[0, k1.structure.idxOf[vd]-1].append[r1.items.subseq[k1.structure.idxOf[vd] +1, #k1.structure.elems]]
				and r3 in k3.instances
				and r3.id = r1.id and r3.items = r1.items.subseq[k1.structure.idxOf[vd], k1.structure.idxOf[vd]]
			
	}
}

pred split_with_two_value_defs[disj k1, k2, k3 : Class, disj s1, s2 : State, vd : Property ]{
		#k1.structure.elems = 2 and splitStructure[vd, k1, k2, k3, s1, s2]
}
run split_with_two_value_defs for 4 but exactly 2 State, 3 Class


pred split_with_one_record[disj k1, k2, k3 : Class, disj s1, s2 : State, vd : Property ]{
	#k1.instances = 1 and splitStructure[vd, k1, k2, k3, s1, s2]
}
run split_with_one_record for 3 but exactly 2 State, 3 Class


pred split_with_no_record[disj k1, k2, k3 : Class, disj s1, s2 : State, vd : Property ]{
	#k1.instances = 0 and splitStructure[vd, k1, k2, k3, s1, s2]
}
run split_with_no_record for 3 but exactly 2 State, 3 Class

/* ***************************************************************************************** */

assert split_structure_same{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		splitStructure[vd, k1, k2, k3, s1, s2] implies 
			#s1.classes.structure.elems = #s2.classes.structure.elems		
}
check split_structure_same for 5

assert split_number_of_valueDefs_same{
all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		splitStructure[vd, k1, k2, k3, s1, s2] implies  
 			#({vc : Property | vc in s1.classes.structure.elems}) = #({vc : Property | vc in s2.classes.structure.elems})
}
check split_number_of_valueDefs_same  for 5

assert split_number_of_referenceDefs_same_after{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		splitStructure[vd, k1, k2, k3, s1, s2] implies  
			#({rd : Reference | rd in s1.classes.structure.elems}) = #({vc : Reference | vc in s2.classes.structure.elems})
}
check split_number_of_referenceDefs_same_after for 5


assert split_number_of_classes_is_higher_after{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		splitStructure[vd, k1, k2, k3, s1, s2] implies  
			#({k : Class | k in s1.classes}) < #({k : Class | k in s2.classes})
}
check split_number_of_classes_is_higher_after for 5

assert split_not_change_number_of_values{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		splitStructure[vd, k1, k2, k3, s1, s2] implies  
			#({k : ValueContainer | k in s1.classes.instances.items.elems}) = #({k : ValueContainer | k in s2.classes.instances.items.elems})
}
check split_not_change_number_of_values for 5 

assert split_not_change_number_of_references{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		splitStructure[vd, k1, k2, k3, s1, s2] implies 
			#({k : ReferenceContainer | k in s1.classes.instances.items.elems}) = #({k : ReferenceContainer | k in s2.classes.instances.items.elems})
}
check split_not_change_number_of_references for 5

assert split_not_change_inheritace_depth{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		splitStructure[vd, k1, k2, k3, s1, s2] implies 
		 all k : Class | k in s1.classes implies 
				some k' : Class | k' in s2.classes  and #(k'.*parent) = #(k.*parent)
			and
			all k' : Class | k' in s2.classes implies 
				some k : Class | k in s1.classes and  #(k'.*parent) = #(k.*parent)
}
check split_not_change_inheritace_depth for 5

assert split_not_change_nmber_of_children{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		splitStructure[vd, k1, k2, k3, s1, s2] implies 
			children_preserve[s1,s2] 
}
check split_not_change_nmber_of_children for 5

assert split_not_change_cohesion_number{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		splitStructure[vd, k1, k2, k3, s1, s2] implies 
			coupling_preserve[s1, s2]
}
check split_not_change_cohesion_number for 5


