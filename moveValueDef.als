open model

pred moveValueDef[vd : ValueDef, disj k1, k2, k3, k4 : Kind, disj s1, s2 : State]{
	//k1 -> k3
	//k2 -> k4
	k3 not in s1.kinds
	k4 not in s1.kinds
	k1 in s1.kinds
	k2 in s1.kinds
	s2.kinds = (s1.kinds - k1 - k2) + k3 + k4

	k1.name = k3.name
	k2.name = k4.name

	k1.parent = k3.parent
	k2.parent = k4.parent

	vd in k1.structure.elems and vd not in k2.structure.elems
	vd not in k3.structure.elems and vd in k4.structure.elems

	k4.structure = k2.structure.add[vd]
	
	//k1 -> k3 structure
	let idx = k1.structure.idxOf[vd] {
		idx = 0 implies k3.structure = rest[k1.structure] else
			idx = k1.structure.lastIdx implies k3.structure = k1.structure.subseq[0, idx-1] else
				k3.structure =  k1.structure.subseq[0, idx-1].append[ k1.structure.subseq[idx+1,  k1.structure.lastIdx]]
	}
	
	#k1.records = #k3.records
	#k2.records = #k4.records

	//k1->k3 records
	all r3 : Record |
		r3 in k3.records implies one r1 : Record { 
			r1 in k1.records and r1.id = r3.id and
				let idx = k1.structure.idxOf[vd], last =  k1.structure.lastIdx  {
						idx = 0 implies r3.items = rest[r1.items] else
							idx = last implies r3.items = r1.items.subseq[0, idx-1] else
								r3.items = r1.items.subseq[0, idx-1].append[r1.items.subseq[idx+1,  last]]
				}
		}
		

	#k1.records = #k2.records or (#k1.records = 0 and #k2.records > 0) 
	
	#k1.records = #k2.records implies {
		all r4 : Record |
			r4 in k4.records implies one r1, r2 : Record {
				r1 in k1.records and r2 in k2. records and r1.id = r2.id and r1.id = r4.id and
					let idx = k1.structure.idxOf[vd] | r4.items = r2.items.append[r1.items.subseq[idx, idx]]
			}	
	}				

	#k1.records = 0 and #k2.records > 0 implies {
		all r4 : Record |
			r4 in k4.records implies one r2 : Record {
				r2 in k2. records and r2.id = r4.id and r4.items.subseq[0, add[#r2.items,-1]] = r2.items
				and add[#r2.items, 1] = #r4.items
			}	
	}
	//reference update not neccesary
}

//run moveValueDef for 3 but exactly 2 State, 4 Kind, 0 Record

pred moveValueDef_no_record[vd : ValueDef, disj k1, k2, k3, k4 : Kind, disj s1, s2 : State]{
	#k1.records = 0 and #k2.records = 0  and (k1.structure.elems & k2.structure.elems) = none and moveValueDef[vd, k1, k2, k3, k4, s1, s2]
}
run moveValueDef_no_record for 3 but exactly 2 State, 4 Kind

pred moveValueDef_one_record_in_both[vd : ValueDef, disj k1, k2, k3, k4  : Kind, disj s1, s2 : State]{
	#k1.records = 1 and #k2.records = 1 and (k1.structure.elems & k2.structure.elems)  = none and moveValueDef[vd, k1, k2, k3, k4, s1, s2]
}
run moveValueDef_one_record_in_both for 4 but exactly 2 State, 4 Kind

pred moveValueDef_one_record_in_target_only[vd : ValueDef, disj k1, k2, k3, k4  : Kind, disj s1, s2 : State]{
	#k1.records = 0 and #k2.records = 1 and (k1.structure.elems & k2.structure.elems)  = none and moveValueDef[vd, k1, k2, k3, k4, s1, s2]
}
run moveValueDef_one_record_in_target_only for 4 but exactly 2 State, 4 Kind


/* ***************************************************************************************** */

assert moveValueDef_structure_same{
	all vd : ValueDef, disj k1, k2, k3, k4 : Kind, disj s1, s2 : State |
		moveValueDef[vd, k1, k2, k3, k4, s1, s2] implies 
			#s1.kinds.structure.elems = #s2.kinds.structure.elems		
}
check moveValueDef_structure_same for 5

assert moveValueDef_number_of_valueDefs_same{
	all vd : ValueDef, disj k1, k2, k3, k4 : Kind, disj s1, s2 : State |
		moveValueDef[vd, k1, k2, k3, k4, s1, s2] implies 
 			#({vc : ValueDef | vc in s1.kinds.structure.elems}) = #({vc : ValueDef | vc in s2.kinds.structure.elems})
}
check moveValueDef_number_of_valueDefs_same  for 5

assert moveValueDef_number_of_referenceDefs_same_after{
	all vd : ValueDef, disj k1, k2, k3, k4 : Kind, disj s1, s2 : State |
		moveValueDef[vd, k1, k2, k3, k4, s1, s2] implies 
			#({rd : ReferenceDef | rd in s1.kinds.structure.elems}) = #({vc : ReferenceDef | vc in s2.kinds.structure.elems})
}
check moveValueDef_number_of_referenceDefs_same_after for 5


assert moveValueDef_number_of_kinds_is_same{
	all vd : ValueDef, disj k1, k2, k3, k4 : Kind, disj s1, s2 : State |
		moveValueDef[vd, k1, k2, k3, k4, s1, s2] implies 
			#({k : Kind | k in s1.kinds}) = #({k : Kind | k in s2.kinds})
}
check moveValueDef_number_of_kinds_is_same for 5

assert moveValueDef_can_increase_number_of_values{ //because they are NOTNULL
	all vd : ValueDef, disj k1, k2, k3, k4 : Kind, disj s1, s2 : State |
		moveValueDef[vd, k1, k2, k3, k4, s1, s2] implies 
			#({k : ValueContainer | k in s1.kinds.records.items.elems}) <= #({k : ValueContainer | k in s2.kinds.records.items.elems})
}
check moveValueDef_can_increase_number_of_values for 5 

assert moveValueDef_not_change_number_of_references{
	all vd : ValueDef, disj k1, k2, k3, k4 : Kind, disj s1, s2 : State |
		moveValueDef[vd, k1, k2, k3, k4, s1, s2] implies 
			#({k : ReferenceContainer | k in s1.kinds.records.items.elems}) = #({k : ReferenceContainer | k in s2.kinds.records.items.elems})
}
check moveValueDef_not_change_number_of_references for 5


assert moveValueDef_not_change_inheritace_depth{
	all vd : ValueDef, disj k1, k2, k3, k4 : Kind, disj s1, s2 : State |
		moveValueDef[vd, k1, k2, k3, k4, s1, s2] implies
			depth_preserved[s1, s2]
}
check moveValueDef_not_change_inheritace_depth for 5

assert moveValueDef_not_change_number_of_children{
	all vd : ValueDef, disj k1, k2, k3, k4 : Kind, disj s1, s2 : State |
		moveValueDef[vd, k1, k2, k3, k4, s1, s2] implies 
			children_preserve[s1,s2]
}
check moveValueDef_not_change_number_of_children for 5

assert moveValueDef_not_change_cohesion_number{
	all vd : ValueDef, disj k1, k2, k3, k4 : Kind, disj s1, s2 : State |
		moveValueDef[vd, k1, k2, k3, k4, s1, s2] implies
		coupling_preserve[s1, s2]
}
check moveValueDef_not_change_cohesion_number for 5



