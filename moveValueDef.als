open model

pred moveProperty[vd : Property, disj k1, k2, k3, k4 : Class, disj s1, s2 : State]{
	//k1 -> k3
	//k2 -> k4
	k3 not in s1.classes
	k4 not in s1.classes
	k1 in s1.classes
	k2 in s1.classes
	s2.classes = (s1.classes - k1 - k2) + k3 + k4

	k1.name = k3.name
	k2.name = k4.name

	k1.parentName= k3.parentName
	k2.parentName= k4.parentName

	vd in k1.structure.elems and vd not in k2.structure.elems
	vd not in k3.structure.elems and vd in k4.structure.elems

	k4.structure = k2.structure.add[vd]
	
	//k1 -> k3 structure
	let idx = k1.structure.idxOf[vd] {
		idx = 0 implies k3.structure = rest[k1.structure] else
			idx = k1.structure.lastIdx implies k3.structure = k1.structure.subseq[0, idx-1] else
				k3.structure =  k1.structure.subseq[0, idx-1].append[ k1.structure.subseq[idx+1,  k1.structure.lastIdx]]
	}
	
	#k1.instances = #k3.instances
	#k2.instances = #k4.instances

	//k1->k3 instances
	all r3 : Instance |
		r3 in k3.instances implies one r1 : Instance { 
			r1 in k1.instances and r1.id = r3.id and
				let idx = k1.structure.idxOf[vd], last =  k1.structure.lastIdx  {
						idx = 0 implies r3.items = rest[r1.items] else
							idx = last implies r3.items = r1.items.subseq[0, idx-1] else
								r3.items = r1.items.subseq[0, idx-1].append[r1.items.subseq[idx+1,  last]]
				}
		}
		

	#k1.instances = #k2.instances or (#k1.instances = 0 and #k2.instances > 0) 
	
	#k1.instances = #k2.instances implies {
		all r4 : Instance |
			r4 in k4.instances implies one r1, r2 : Instance {
				r1 in k1.instances and r2 in k2. instances and r1.id = r2.id and r1.id = r4.id and
					let idx = k1.structure.idxOf[vd] | r4.items = r2.items.append[r1.items.subseq[idx, idx]]
			}	
	}				

	#k1.instances = 0 and #k2.instances > 0 implies {
		all r4 : Instance |
			r4 in k4.instances implies one r2 : Instance {
				r2 in k2. instances and r2.id = r4.id and r4.items.subseq[0, add[#r2.items,-1]] = r2.items
				and add[#r2.items, 1] = #r4.items
			}	
	}
	//reference update not neccesary
}

//run moveProperty for 3 but exactly 2 State, 4 Class, 0 Instance

pred moveProperty_no_record[vd : Property, disj k1, k2, k3, k4 : Class, disj s1, s2 : State]{
	#k1.instances = 0 and #k2.instances = 0  and (k1.structure.elems & k2.structure.elems) = none and moveProperty[vd, k1, k2, k3, k4, s1, s2]
}
run moveProperty_no_record for 3 but exactly 2 State, 4 Class

pred moveProperty_one_record_in_both[vd : Property, disj k1, k2, k3, k4  : Class, disj s1, s2 : State]{
	#k1.instances = 1 and #k2.instances = 1 and (k1.structure.elems & k2.structure.elems)  = none and moveProperty[vd, k1, k2, k3, k4, s1, s2]
}
run moveProperty_one_record_in_both for 4 but exactly 2 State, 4 Class

pred moveProperty_one_record_in_target_only[vd : Property, disj k1, k2, k3, k4  : Class, disj s1, s2 : State]{
	#k1.instances = 0 and #k2.instances = 1 and (k1.structure.elems & k2.structure.elems)  = none and moveProperty[vd, k1, k2, k3, k4, s1, s2]
}
run moveProperty_one_record_in_target_only for 4 but exactly 2 State, 4 Class


/* ***************************************************************************************** */

assert moveProperty_structure_same{
	all vd : Property, disj k1, k2, k3, k4 : Class, disj s1, s2 : State |
		moveProperty[vd, k1, k2, k3, k4, s1, s2] implies 
			#s1.classes.structure.elems = #s2.classes.structure.elems		
}
check moveProperty_structure_same for 5

assert moveProperty_number_of_valueDefs_same{
	all vd : Property, disj k1, k2, k3, k4 : Class, disj s1, s2 : State |
		moveProperty[vd, k1, k2, k3, k4, s1, s2] implies 
 			#({vc : Property | vc in s1.classes.structure.elems}) = #({vc : Property | vc in s2.classes.structure.elems})
}
check moveProperty_number_of_valueDefs_same  for 5

assert moveProperty_number_of_referenceDefs_same_after{
	all vd : Property, disj k1, k2, k3, k4 : Class, disj s1, s2 : State |
		moveProperty[vd, k1, k2, k3, k4, s1, s2] implies 
			#({rd : Reference | rd in s1.classes.structure.elems}) = #({vc : Reference | vc in s2.classes.structure.elems})
}
check moveProperty_number_of_referenceDefs_same_after for 5


assert moveProperty_number_of_classes_is_same{
	all vd : Property, disj k1, k2, k3, k4 : Class, disj s1, s2 : State |
		moveProperty[vd, k1, k2, k3, k4, s1, s2] implies 
			#({k : Class | k in s1.classes}) = #({k : Class | k in s2.classes})
}
check moveProperty_number_of_classes_is_same for 5

assert moveProperty_can_increase_number_of_values{ //because they are NOTNULL
	all vd : Property, disj k1, k2, k3, k4 : Class, disj s1, s2 : State |
		moveProperty[vd, k1, k2, k3, k4, s1, s2] implies 
			#({k : ValueContainer | k in s1.classes.instances.items.elems}) <= #({k : ValueContainer | k in s2.classes.instances.items.elems})
}
check moveProperty_can_increase_number_of_values for 5 

assert moveProperty_not_change_number_of_references{
	all vd : Property, disj k1, k2, k3, k4 : Class, disj s1, s2 : State |
		moveProperty[vd, k1, k2, k3, k4, s1, s2] implies 
			#({k : ReferenceContainer | k in s1.classes.instances.items.elems}) = #({k : ReferenceContainer | k in s2.classes.instances.items.elems})
}
check moveProperty_not_change_number_of_references for 5


assert moveProperty_not_change_inheritace_depth{
	all vd : Property, disj k1, k2, k3, k4 : Class, disj s1, s2 : State |
		moveProperty[vd, k1, k2, k3, k4, s1, s2] implies
			depth_preserved[s1, s2]
}
check moveProperty_not_change_inheritace_depth for 5

assert moveProperty_not_change_number_of_children{
	all vd : Property, disj k1, k2, k3, k4 : Class, disj s1, s2 : State |
		moveProperty[vd, k1, k2, k3, k4, s1, s2] implies 
			children_preserve[s1,s2]
}
check moveProperty_not_change_number_of_children for 5

assert moveProperty_not_change_cohesion_number{
	all vd : Property, disj k1, k2, k3, k4 : Class, disj s1, s2 : State |
		moveProperty[vd, k1, k2, k3, k4, s1, s2] implies
		coupling_preserve[s1, s2]
}
check moveProperty_not_change_cohesion_number for 5



