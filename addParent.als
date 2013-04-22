open model

pred addParent[disj k1, k2, k3 : Class, disj s1, s2 : State]{
	k1 in s1.classes
	k2 in s1.classes
	k3 not in s1.classes

	k2 not in k1.*parent

	all k : Class |
		k in s1.classes implies parentsInState[k, s1]

	all k : Class |
		k in s2.classes implies parentsInState[k, s2]

	
	

	k2.parentName= none	
	k2.name = k3.name 
	k2.structure = k3.structure
	
	k2.instances = k3.instances

	((#k2.instances = 0 and #k1.instances = 0) or (#k2.instances = 0 and #k1.instances > 0)) implies {
		s2.classes = s1.classes - k2 + k3
	}

	#k1.instances = 0 and #k2.instances > 0 implies {
		k3.parentName= k1.name
		k2 not in s2.classes
		k3 in s2.classes
		#s1.classes = #s2.classes
		{all k : Class |
			k in s1.classes and k != k2 and k not in k1.*parent implies
				k in s2.classes}
		all k : Class |
			k in s1.classes and k in k1.*parent implies 
				one x : Class {
					x != k3
					x not in s1.classes
					x in s2.classes
					k not in s2.classes
					x.name = k.name
					x.structure = k.structure
					#x.instances = #k2.instances
					x.parentName= k.parent
					#k.instances = 0 implies {
						all r: Instance |
							r in x.instances implies one r2 : Instance |
								r2 in k2.instances and r.id = r2.id and {no c : Container | c in r.items.elems}
					}else{
							all r1 : Instance | r1 in x.instances implies one r2 : Instance | r2 in k2.instances and r2.id = r1.id
					}

				}
	}
/*	
	#k1.instances = 0 and #k2.instances > 0 and k1.parent = none implies {
		one k : Class { 
			k not in s1.classes
			k != k3
			s2.classes = s1.classes - k1 - k2 + k3 + k
			k.name = k1.name
			k.structure = k1.structure
			k.parentName= k1.parent
			#k.instances = #k2.instances
			all r: Instance |
				r in k.instances implies one r2 : Instance |
					r2 in k2.instances and r.id = r2.id //and {no c : Container | c in r.items.elems}
//			all r2: Instance |
	//			r2 in k2.instances implies one r1 : Instance |
		//			r1 in k1.instances and r1.id = r2.id 
			
		}
	}
	*/
	#k1.instances > 0 and #k2.instances > 0 implies {
		s2.classes = s1.classes - k2 + k3
		k3.parentName= k1.name
		#k1.instances = #k2.instances
		all r1 : Instance | r1 in k1.instances implies one r2 : Instance | r2 in k2.instances and r2.id = r1.id
	}
}

pred parentsInState[k:Class, s: State]{
	all k1 : Class | k1 in k.*parent implies k in s.classes and k1 in s.classes
}

pred addParent_no_record[disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances = 0 and #k2.instances = 0 and addParent[k1, k2, k3, s1, s2]
}
run addParent_no_record 

pred addParent_no_record_in_parent_no_existing_hierarchy[disj k1, k2, k3 : Class, disj s1, s2 : State]{
		k1.parentName= none and
	#k1.instances = 0 and #k2.instances > 0 addParent[k1, k2, k3, s1, s2]
}
run addParent_no_record_in_parent_no_existing_hierarchy for 5

pred addParent_no_record_in_parent[disj k1, k2, k3 : Class, disj s1, s2 : State]{
		k1.parentName!= none and
	#k1.instances = 0 and #k1.parent.instances = 0 and #k2.instances > 0 addParent[k1, k2, k3, s1, s2]
}
run addParent_no_record_in_parentNamefor 6

pred addParent_no_record_in_child[disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances > 0 and #k2.instances = 0 addParent[k1, k2, k3, s1, s2]
}
run addParent_no_record_in_child for 5

pred addParent_record_in_both[disj k1, k2, k3 : Class, disj s1, s2 : State]{
		k1.parentName!= none and
	#k1.instances > 0 and #k2.instances > 0 and addParent[k1, k2, k3, s1, s2]
}
run addParent_record_in_both for 5

/* ***************************************************************************************** */

assert addParent_structure_same{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies 
			#s1.classes.structure.elems = #s2.classes.structure.elems		
}
check addParent_structure_same for 5

assert addParent_number_of_valueDefs_same{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies 
 			#({vc : Property | vc in s1.classes.structure.elems}) = #({vc : Property | vc in s2.classes.structure.elems})
}
check addParent_number_of_valueDefs_same  for 5

assert addParent_number_of_referenceDefs_same_after{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies
			#({rd : Reference | rd in s1.classes.structure.elems}) = #({vc : Reference | vc in s2.classes.structure.elems})
}
check addParent_number_of_referenceDefs_same_after for 5


assert addParent_number_of_classes_same{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies 
			#({k : Class | k in s1.classes}) = #({k : Class | k in s2.classes})
}
check addParent_number_of_classes_same for 5

assert addParent_can_increase_number_of_values{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies
			#({k : ValueContainer | k in s1.classes.instances.items.elems}) <= #({k : ValueContainer | k in s2.classes.instances.items.elems})
}
check addParent_can_increase_number_of_values for 5 

assert addParent_not_change_number_of_references{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies
			#({k : ReferenceContainer | k in s1.classes.instances.items.elems}) = #({k : ReferenceContainer | k in s2.classes.instances.items.elems})
}
check addParent_not_change_number_of_references for 5



assert  addParent_can_increase_inheritace_depth{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies
			depth_preserved[s1,s2] or 	depth_increased[s1, s2] 
}
check addParent_can_increase_inheritace_depth for 4

assert addParent_can_increase_number_of_children{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies 
			children_preserve[s1,s2] or children_increase[s1,s2]
}
check addParent_can_increase_number_of_children for 5 but exactly 2 State

assert addParent_not_change_cohesion_number{
	all disj k1, k2, k3 : Class, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies
			coupling_preserve[s1, s2]
}
check addParent_not_change_cohesion_number for 5
