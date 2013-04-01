open model

pred merge[disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	k1 in s1.kinds and k1 not in s2.kinds
	k2 in s1.kinds and k2 not in s2.kinds
	k3 not in s1.kinds and k3 in s2.kinds

	k1.structure + k2.structure - (k2.structure - k1.structure) - (k1.structure - k2.structure) = none
	
	k3.structure = k1.structure + k2.structure
	
	#k1.records = #k2.records implies {
	all r1 : Record |
		r1 in k1.records implies one r2 : Record | r2 in k2.records and r1.id = r2.id
 	
	all r3 : Record |
		r3 in k3.records implies one r1, r2 : Record |
			r1 in k1.records and r2 in k2.records and r1.id = r2.id and r3.id = r1.id and
			r3.items = r1.items + r2.items
	}
	
	//only if k2.structure = none
	#k1.records > 0 and #k2.records = 0 implies {
		all r3 : Record |
		r3 in k3.records implies one r1 : Record |
			r1 in k1.records and r3.id = r1.id and
			r3.items = r1.items 
	}

	//only if k1.structure = none
	#k1.records = 0 and #k2.records > 0 implies {
		all r3 : Record |
		r3 in k3.records implies one r1 : Record |
			r1 in k1.records and r3.id = r1.id and
			r3.items = r1.items 
	}
}

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
	#k1.records.items = 1 and #k2.records.items = 1 and merge[k1, k2, k3, s1, s2]
}
run merge_with_record_and_values_in_both for 3 but exactly 3 Kind, 2 State
