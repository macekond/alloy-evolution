open model

pred merge[disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	k1.structure.elems & k2.structure.elems = none
	
	k3.name = k1.name

	{no rd : ReferenceDef | rd.reference = k2.name and rd in s1.kinds.structure.elems} implies {
		k3.structure = k1.structure.append[k2.structure]  
		and s2.kinds = s1.kinds - k1 - k2 + k3
	}else{
			k1 in s1.kinds and k1 not in s2.kinds
			k2 in s1.kinds and k2 not in s2.kinds
			k3 not in s1.kinds and k3 in s2.kinds
			#k3.structure = add[#k1.structure, #k2.structure]
			
			add[#s1.kinds, -1] = #s2.kinds
			
			all v :  Def | v in k3.structure.elems implies{  
				one v1 : Def |
					let mstruct = k1.structure.append[k2.structure] {
						v1 in mstruct.elems
						k3.structure.idxOf[v] = mstruct.idxOf[v1]
						{v1.reference != k2.name implies v = v1 else v.reference = k3.name}
					}
			} 
			
			all k : Kind |
				k in s2.kinds and k != k3 implies one k' : Kind {
					k' in s1.kinds
					(k2.name not in  k'.structure.elems.reference implies k = k')
					or 
					(k2.name not in  k.structure.elems.reference implies k'.records = k.records and
						all v :  Def | v in k.structure.elems implies{  
							one v1 : Def |
								v1 in k'.structure.elems
								and k'.structure.idxOf[v] = k.structure.idxOf[v1]
								and {v1.reference != k2.name implies v = v1 else v.reference = k3.name}
						} 
					)
				}
	}//end of else
	

	#k1.records = #k2.records or (#k1.records > 0 and #k2.records = 0) or (#k1.records = 0 and #k2.records > 0)
	
	#k1.records = #k2.records implies {
		#k3.records = #k1.records
		all r1 : Record |
			r1 in k1.records implies one r2 : Record | r2 in k2.records and r1.id = r2.id
 	
		all r3 : Record |
			r3 in k3.records implies one r1, r2 : Record |
				r1 in k1.records and r2 in k2.records and r1.id = r2.id and r3.id = r1.id and
				r3.items = r1.items.append[r2.items]
	}
	
	//only if k2.structure = none
	#k1.records > 0 and #k2.records = 0 implies {
		#k3.records = #k1.records
		all r3 : Record |
		r3 in k3.records implies one r1 : Record |
			r1 in k1.records and r3.id = r1.id and
				all c : Container |
					c in r1.items.elems implies r3.items.idxOf[c] = r1.items.idxOf[c]

	}

	//only if k1.structure = none
	#k1.records = 0 and #k2.records > 0 implies {
		#k3.records = #k2.records	
		all r3 : Record |
		r3 in k3.records implies one r2 : Record |
			r2 in k2.records and r3.id = r2.id and
			all c : Container |
					c in r2.items.elems implies r3.items.idxOf[c] = add[r2.items.idxOf[c], #k1.structure]
	}
	
}

pred merge_with_no_record_no_ref[disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records = 0 and #k2.records = 0 and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record_no_ref for 3 but exactly 3 Kind, 2 State, 0 ReferenceDef

pred merge_with_no_record[disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records = 0 and #k2.records = 0 and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record for 3 but exactly 3 Kind, 2 State

pred merge_with_record_in_one[disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records = 1 and #k2.records = 0 and merge[k1, k2, k3, s1, s2]
}
run merge_with_record_in_one for 3 but exactly 3 Kind, 2 State

pred merge_with_record_in_both[disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records = 1 and #k2.records = 1 and merge[k1, k2, k3, s1, s2]
}
run merge_with_record_in_both for 3 but exactly 3 Kind, 2 State

pred merge_with_record_and_values_in_both[disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records.items.values = 1 and #k2.records.items.values = 1 and merge[k1, k2, k3, s1, s2]
}
run merge_with_record_and_values_in_both for 3 but exactly 3 Kind, 2 State

pred merge_with_no_record_and_reference[disj k1, k2, k3 : Kind, disj s1, s2 : State, rd : ReferenceDef]{
	#k1.records = 0 and #k2.records = 0 and rd.reference = k2.name and rd in k2.structure.elems  and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record_and_reference for 3 but exactly 3 Kind, 2 State

pred merge_with_no_record_and_reference2[disj k1, k2, k3 : Kind, disj s1, s2 : State, rd : ReferenceDef]{
	#k1.records = 0 and #k2.records = 0 and rd.reference = k2.name and rd in k1.structure.elems  and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record_and_reference2 for 3 but exactly 3 Kind, 2 State

pred merge_with_no_record_and_reference_in_other[disj k, k1, k2, k3 : Kind, disj s1, s2 : State, rd : ReferenceDef]{
	#k.records = 0 and #k1.records = 0 and #k2.records = 0 and rd.reference = k2.name and rd in k.structure.elems and k in s1.kinds and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record_and_reference_in_other for 3 but exactly 5 Kind, 2 State

pred merge_with_no_record_and_no_reference_in_other[disj k, k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k.records = 0 and #k1.records = 0 and #k2.records = 0  and k in s1.kinds and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record_and_no_reference_in_other for 3 but exactly 4 Kind, 2 State, 0 ReferenceDef
