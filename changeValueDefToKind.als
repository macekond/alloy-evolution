open model

pred changeValueDefToKind[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	k1 in s1.kinds and k1 not in s2.kinds
	k2 not in s1.kinds and k2 in s2.kinds
	k3 not in s1.kinds and k3 in s2.kinds

	vd in k1.structure
	
	k2.structure = k1.structure - vd
	//k3.structure should have the same structure as vd, but the max cardinality is 1
	k3.structure = vd
	
	#k1.records > 0 implies{
	all r2 : Record |
		r2 in k2.records implies one r1 : Record | r1.id = r2.id 
				and r2.items = r1.items - {vc : ValueContainer | vc in r1.items and vc.def = vd}

	// this must be updated when cardinalites and references are introduced
	all r3 : Record |
		r3 in k3.records implies one r1 : Record | r1.id = r3.id 
				and r3.items =  {vc : ValueContainer | vc in r1.items and vc.def = vd}
	}else{#k2.records = 0 and #k3.records = 0}
}

pred changeValueDefToKind_no_records[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records = 0 and changeValueDefToKind[vd, k1, k2, k3, s1, s2]
}
run changeValueDefToKind_no_records for 3 but exactly 2 State, 3 Kind

pred changeValueDefToKind_one_record[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records = 1 and changeValueDefToKind[vd, k1, k2, k3, s1, s2]
}
run changeValueDefToKind_one_record for 3 but exactly 2 State, 3 Kind
