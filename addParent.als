open model

pred addParent[disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	k1 in s1.kinds
	k2 in s1.kinds
	k3 not in s1.kinds

	k2 not in k1.*parK

	all k : Kind |
		k in s1.kinds implies parentsInState[k, s1]

	all k : Kind |
		k in s2.kinds implies parentsInState[k, s2]

	
	

	k2.parent = none	
	k2.name = k3.name 
	k2.structure = k3.structure
	
	k2.records = k3.records

	((#k2.records = 0 and #k1.records = 0) or (#k2.records = 0 and #k1.records > 0)) implies {
		s2.kinds = s1.kinds - k2 + k3
	}

	#k1.records = 0 and #k2.records > 0 implies {
		k3.parent = k1.name
		k2 not in s2.kinds
		k3 in s2.kinds
		#s1.kinds = #s2.kinds
		{all k : Kind |
			k in s1.kinds and k != k2 and k not in k1.*parK implies
				k in s2.kinds}
		all k : Kind |
			k in s1.kinds and k in k1.*parK implies 
				one x : Kind {
					x != k3
					x not in s1.kinds
					x in s2.kinds
					k not in s2.kinds
					x.name = k.name
					x.structure = k.structure
					#x.records = #k2.records
					x.parent = k.parent
					#k.records = 0 implies {
						all r: Record |
							r in x.records implies one r2 : Record |
								r2 in k2.records and r.id = r2.id and {no c : Container | c in r.items.elems}
					}else{
							all r1 : Record | r1 in x.records implies one r2 : Record | r2 in k2.records and r2.id = r1.id
					}

				}
	}
/*	
	#k1.records = 0 and #k2.records > 0 and k1.parK = none implies {
		one k : Kind { 
			k not in s1.kinds
			k != k3
			s2.kinds = s1.kinds - k1 - k2 + k3 + k
			k.name = k1.name
			k.structure = k1.structure
			k.parent = k1.parent
			#k.records = #k2.records
			all r: Record |
				r in k.records implies one r2 : Record |
					r2 in k2.records and r.id = r2.id //and {no c : Container | c in r.items.elems}
//			all r2: Record |
	//			r2 in k2.records implies one r1 : Record |
		//			r1 in k1.records and r1.id = r2.id 
			
		}
	}
	*/
	#k1.records > 0 and #k2.records > 0 implies {
		s2.kinds = s1.kinds - k2 + k3
		k3.parent = k1.name
		#k1.records = #k2.records
		all r1 : Record | r1 in k1.records implies one r2 : Record | r2 in k2.records and r2.id = r1.id
	}
}

pred parentsInState[k:Kind, s: State]{
	all k1 : Kind | k1 in k.*parK implies k in s.kinds and k1 in s.kinds
}

pred addParent_no_record[disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records = 0 and #k2.records = 0 and addParent[k1, k2, k3, s1, s2]
}
run addParent_no_record 

pred addParent_no_record_in_parent_no_existing_hierarchy[disj k1, k2, k3 : Kind, disj s1, s2 : State]{
		k1.parent = none and
	#k1.records = 0 and #k2.records > 0 addParent[k1, k2, k3, s1, s2]
}
run addParent_no_record_in_parent_no_existing_hierarchy for 5

pred addParent_no_record_in_parent[disj k1, k2, k3 : Kind, disj s1, s2 : State]{
		k1.parent != none and
	#k1.records = 0 and #k1.parK.records = 0 and #k2.records > 0 addParent[k1, k2, k3, s1, s2]
}
run addParent_no_record_in_parent for 6

pred addParent_no_record_in_child[disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records > 0 and #k2.records = 0 addParent[k1, k2, k3, s1, s2]
}
run addParent_no_record_in_child for 5

pred addParent_record_in_both[disj k1, k2, k3 : Kind, disj s1, s2 : State]{
		k1.parent != none and
	#k1.records > 0 and #k2.records > 0 and addParent[k1, k2, k3, s1, s2]
}
run addParent_record_in_both for 5

/* ***************************************************************************************** */

assert addParent_structure_same{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies 
			#s1.kinds.structure.elems = #s2.kinds.structure.elems		
}
check addParent_structure_same for 5

assert addParent_number_of_valueDefs_same{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies 
 			#({vc : ValueDef | vc in s1.kinds.structure.elems}) = #({vc : ValueDef | vc in s2.kinds.structure.elems})
}
check addParent_number_of_valueDefs_same  for 5

assert addParent_number_of_referenceDefs_same_after{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies
			#({rd : ReferenceDef | rd in s1.kinds.structure.elems}) = #({vc : ReferenceDef | vc in s2.kinds.structure.elems})
}
check addParent_number_of_referenceDefs_same_after for 5


assert addParent_number_of_kinds_same{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies 
			#({k : Kind | k in s1.kinds}) = #({k : Kind | k in s2.kinds})
}
check addParent_number_of_kinds_same for 5

assert addParent_can_increase_number_of_values{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies
			#({k : ValueContainer | k in s1.kinds.records.items.elems}) <= #({k : ValueContainer | k in s2.kinds.records.items.elems})
}
check addParent_can_increase_number_of_values for 5 

assert addParent_not_change_number_of_references{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies
			#({k : ReferenceContainer | k in s1.kinds.records.items.elems}) = #({k : ReferenceContainer | k in s2.kinds.records.items.elems})
}
check addParent_not_change_number_of_references for 5



assert  addParent_can_increase_inheritace_depth{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies
			depth_preserved[s1,s2] or 	depth_increased[s1, s2] 
}
check addParent_can_increase_inheritace_depth for 4

assert addParent_can_increase_number_of_children{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies 
			children_preserve[s1,s2] or children_increase[s1,s2]
}
check addParent_can_increase_number_of_children for 5 but exactly 2 State

assert addParent_not_change_cohesion_number{
	all disj k1, k2, k3 : Kind, disj s1, s2 : State |
		addParent[k1, k2, k3, s1, s2] implies
			coupling_preserve[s1, s2]
}
check addParent_not_change_cohesion_number for 5
