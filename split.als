open model

pred splitStructure[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	s2.kinds - k3 - k2 = s1.kinds - k1

	k1.name = k2.name	

	vd in k1.structure.elems
	k3.structure.elems = vd
	vd not in k2.structure.elems
	
	#k1.records = #k2.records
	#k1.records = #k3.records

	k1.structure.idxOf[vd]	= 0 implies {
			k2.structure = k1.structure.rest
			
			all r2 : Record |
			r2 in k2.records implies one r1, r3 : Record |
				 r1 in k1.records and 
				 r2.id = r1.id and r2.items = r1.items.rest				
				and r3 in k3.records
				 and r3.id = r1.id and r3.items = r1.items.subseq[1, r1.items.lastIdx]
	}
	else	k1.structure.idxOf[vd]	= k1.structure.lastIdx implies {
		k2.structure.add[vd] = k1.structure
		all r2 : Record |
			r2 in k2.records implies one r1, r3 : Record |
				 r1 in k1.records and 
				 r2.id = r1.id and r2.items.add[r1.items.last] = r1.items
				and r3 in k3.records
				and r3.id = r1.id and r3.items = r1.items.subseq[0, r1.items.lastIdx - 1]
	} 
	else {
		k2.structure = k1.structure.subseq[0, k1.structure.idxOf[vd]-1].append[k1.structure.subseq[k1.structure.idxOf[vd] +1, #k1.structure.elems]]
		
		all r2 : Record |
			r2 in k2.records implies one r1, r3 : Record |
				 r1 in k1.records and 
				 r2.id = r1.id and r2.items = r1.items.subseq[0, k1.structure.idxOf[vd]-1].append[r1.items.subseq[k1.structure.idxOf[vd] +1, #k1.structure.elems]]
				and r3 in k3.records
				and r3.id = r1.id and r3.items = r1.items.subseq[k1.structure.idxOf[vd], k1.structure.idxOf[vd]]
			
	}
}

pred split_with_two_value_defs[disj k1, k2, k3 : Kind, disj s1, s2 : State, vd : ValueDef ]{
		#k1.structure.elems = 2 and splitStructure[vd, k1, k2, k3, s1, s2]
}
run split_with_two_value_defs for 4 but exactly 2 State, 3 Kind


pred split_with_one_record[disj k1, k2, k3 : Kind, disj s1, s2 : State, vd : ValueDef ]{
	#k1.records = 1 and splitStructure[vd, k1, k2, k3, s1, s2]
}
run split_with_one_record for 3 but exactly 2 State, 3 Kind


pred split_with_no_record[disj k1, k2, k3 : Kind, disj s1, s2 : State, vd : ValueDef ]{
	#k1.records = 0 and splitStructure[vd, k1, k2, k3, s1, s2]
}
run split_with_no_record for 2 but exactly 2 State, 3 Kind

