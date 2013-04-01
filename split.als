open model

pred splitStructure[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	k1 in s1.kinds and k1 not in s2.kinds
	k2 in s2.kinds and k2 not in s1.kinds
	k3 in s2.kinds and k3 not in s1.kinds	


	k3.structure = vd
	k2.structure = k1.structure - vd
	

	#k1.records > 0 implies{
		vd in k1.records.items.def
		vd not in k2.records.items.def
		k3.records.items.def = vd	
	}

	k1.structure != vd implies{ 
		#k1.records = #k2.records
		all r2 : Record |
			r2 in k2.records implies one r1 : Record |
				 r1 in k1.records and 
				 r2.id = r1.id and all v : ValueContainer | 
					v in r1.items and v.def != vd implies v in r2.items}
	else {#k2.records = 0}

	#k1.records = #k3.records
	all r3 : Record |
		r3 in k3.records implies  one r1 : Record |
			 r1 in k1.records and 
			r3.id = r1.id and  all v : ValueContainer | 
					v in r1.items and  v.def = vd implies v in r3.items
				
}

run splitStructure

pred split_with_two_value_defs[disj k1, k2, k3 : Kind, disj s1, s2 : State, vd : ValueDef ]{
		#k1.records.items.def = 2 and splitStructure[vd, k1, k2, k3, s1, s2]
}
run split_with_two_value_defs for 4 but exactly 2 State, 3 Kind


pred split_with_multiple_records[disj k1, k2, k3 : Kind, disj s1, s2 : State, vd : ValueDef ]{
	#k1.records > 1 and splitStructure[vd, k1, k2, k3, s1, s2]
}
run split_with_multiple_records for 6 but exactly 2 State, 3 Kind


pred split_with_no_record[disj k1, k2, k3 : Kind, disj s1, s2 : State, vd : ValueDef ]{
	#k1.records = 0 and splitStructure[vd, k1, k2, k3, s1, s2]
}
run split_with_no_record for 4 but exactly 2 State, 3 Kind

