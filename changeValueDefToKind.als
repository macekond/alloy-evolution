open model

pred changePropertyToClass[vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State]{
	k2 not in s1.classes 
	k3 not in s1.classes 
	k1 in s1.classes
	//k1 -> k2
	// k3 new	

	all k : Class |
		k in s1.classes implies parentsInState[k, s1]

	all k : Class |
		k in s2.classes implies parentsInState[k, s2]

	s2.classes = s1.classes - k1 + k2 + k3
	
	k1.name = k2.name 
	k2.parentName= k1.parentName
	k3.parentName= none

	vd in k1.structure.elems
	
	add[#k2.structure,1] = #k1.structure
	let idx = k1.structure.idxOf[vd], last =  k1.structure.lastIdx |
		 idx = 0 implies k2.structure = rest[k1.structure] else
			idx = last implies k2.structure = k1.structure.subseq[0, add[last, -1]] else
				k2.structure = k1.structure.subseq[0, add[idx,-1]].append[k1.structure.subseq[add[idx,1], last]]
	
	//k3.structure should have the same structure as vd, but the max cardinality is 1
	k3.structure.elems = vd
	
		#k1.instances = #k2.instances
		all r2 : Instance |
			r2 in k2.instances implies one r1 : Instance | r1.id = r2.id and r1 in k1.instances  
				and let idx = k1.structure.idxOf[vd], last = k1.structure.lastIdx  {
						idx = 0 implies r2.items = rest[r1.items] else
							idx = last implies r2.items = r1.items.subseq[0, add[idx,1]] else
								r2.items = r1.items.subseq[0, add[idx,-1]].append[r1.items.subseq[add[idx,1],  last]]
				}

	#k1.instances = #k3.instances
	// this must be updated when cardinalites and references are introduced
	all r3 : Instance |
		r3 in k3.instances implies one r1 : Instance | r1.id = r3.id and r1 in k1.instances
			and let idx = k1.structure.idxOf[vd] |
				r3.items = r1.items.subseq[idx,idx]
	
	//maybe add a reference from k3 -> k1, but they have the same ID
}
pred parentsInState[k:Class, s: State]{
	all k1 : Class | k1 in k.*parent implies k in s.classes and k1 in s.classes
}


pred changePropertyToClass_no_instances[vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances = 0 and changePropertyToClass[vd, k1, k2, k3, s1, s2]
}
run changePropertyToClass_no_instances for 3 but exactly 2 State, 3 Class

pred changePropertyToClass_one_record[vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances = 1 and changePropertyToClass[vd, k1, k2, k3, s1, s2]
}
run changePropertyToClass_one_record for 4 but exactly 2 State, 3 Class

pred changePropertyToClass_hierarchy_exists_on_parent[vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State]{
	k1.parentName!= none and changePropertyToClass[vd, k1, k2, k3, s1, s2]
}
run changePropertyToClass_hierarchy_exists_on_parent for 4 but exactly 2 State

/* ***************************************************************************************** */

assert changePropertytoClass_structure_same_after{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		 changePropertyToClass[vd, k1, k2, k3, s1, s2] implies 
			#s1.classes.structure.elems = #s2.classes.structure.elems		
}
check changePropertytoClass_structure_same_after for 5

assert changePropertytoClass_number_of_valueDefs_same{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		 changePropertyToClass[vd, k1, k2, k3, s1, s2] implies  
 			#({vc : Property | vc in s1.classes.structure.elems}) = #({vc : Property | vc in s2.classes.structure.elems})
}

check changePropertytoClass_number_of_valueDefs_same  for 5

assert changePropertytoClass_number_of_referenceDefs_same_after{
		all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		 changePropertyToClass[vd, k1, k2, k3, s1, s2] implies 
			#({rd : Reference | rd in s1.classes.structure.elems}) = #({vc : Reference | vc in s2.classes.structure.elems})
}
check changePropertytoClass_number_of_referenceDefs_same_after for 5


assert changePropertytoClass_number_of_classes_is_grater_after{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		 changePropertyToClass[vd, k1, k2, k3, s1, s2] implies 
			#({k : Class | k in s1.classes}) < #({k : Class | k in s2.classes})
}
check changePropertytoClass_number_of_classes_is_grater_after for 5

assert changePropertytoClass_not_change_number_of_values{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		 changePropertyToClass[vd, k1, k2, k3, s1, s2] implies 
			#({k : ValueContainer | k in s1.classes.instances.items.elems}) = #({k : ValueContainer | k in s2.classes.instances.items.elems})
}
check changePropertytoClass_not_change_number_of_values for 5

assert changePropertytoClass_not_change_number_of_references{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		 changePropertyToClass[vd, k1, k2, k3, s1, s2] implies 
			#({k : ReferenceContainer | k in s1.classes.instances.items.elems}) = #({k : ReferenceContainer | k in s2.classes.instances.items.elems})
}
check changePropertytoClass_not_change_number_of_references for 5


assert changePropertytoClass_not_change_inheritace_depth{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		changePropertyToClass[vd, k1, k2, k3, s1, s2]  implies
			depth_preserved[s1, s2] 
}
check changePropertytoClass_not_change_inheritace_depth for 5

assert changePropertytoClass_not_change_number_of_children{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		 changePropertyToClass[vd, k1, k2, k3, s1, s2]  implies 
			children_preserve[s1,s2]
}
check changePropertytoClass_not_change_number_of_children for 5

assert changePropertytoClass_can_increase_cohesion_number{
	all vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State |
		 changePropertyToClass[vd, k1, k2, k3, s1, s2] implies 
				coupling_preserve[s1, s2]
}
check changePropertytoClass_can_increase_cohesion_number for 5
