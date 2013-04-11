open model

pred changeValueDefToKind[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	k2 not in s1.kinds 
	k3 not in s1.kinds 
	//k1 -> k2
	// k3 new	

	s2.kinds = s1.kinds - k1 + k2 + k3
	
	vd in k1.structure.elems
	
	add[#k2.structure,1] = #k1.structure
	let idx = k1.structure.idxOf[vd], last =  k1.structure.lastIdx |
		 idx = 0 implies k2.structure = rest[k1.structure] else
			idx = last implies k2.structure = k1.structure.subseq[0, last -1] else
				k2.structure = k1.structure.subseq[0, idx-1].append[k1.structure.subseq[idx+1, last]]
	
	//k3.structure should have the same structure as vd, but the max cardinality is 1
	k3.structure.elems = vd
	
	#k1.records = #k2.records
	
		all r2 : Record |
			r2 in k2.records implies one r1 : Record | r1.id = r2.id and r1 in k1.records  
				and let idx = k1.structure.idxOf[vd], last = k1.structure.lastIdx  {
						idx = 0 implies r2.items = rest[r1.items] else
							idx = last implies r2.items = r1.items.subseq[0, idx-1] else
								r2.items = r1.items.subseq[0, idx-1].append[r1.items.subseq[idx+1,  last]]
				}

	#k1.records = #k3.records
	// this must be updated when cardinalites and references are introduced
	all r3 : Record |
		r3 in k3.records implies one r1 : Record | r1.id = r3.id and r1 in k1.records
			and let idx = k1.structure.idxOf[vd] |
				r3.items = r1.items.subseq[idx,idx]
	
	//maybe add a reference from k3 -> k1, but they have the same ID
}

pred changeValueDefToKind_no_records[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records = 0 and changeValueDefToKind[vd, k1, k2, k3, s1, s2]
}
run changeValueDefToKind_no_records for 3 but exactly 2 State, 3 Kind

pred changeValueDefToKind_one_record[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records = 1 and changeValueDefToKind[vd, k1, k2, k3, s1, s2]
}
run changeValueDefToKind_one_record for 3 but exactly 2 State, 3 Kind
