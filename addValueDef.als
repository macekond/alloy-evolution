open model

pred addValueDef[vd : ValueDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	k1 in s1.kinds and k1 not in s2.kinds
	k2 in s2.kinds and k2 not in s1.kinds

	vd not in k1.structure and vd not in k1.records.items.def
	k2.structure = k1.structure + vd
	
	#k1.records = #k2.records
	all r2 : Record |
		r2 in k2.records implies one r1 : Record |
			r1 in k1.records and r1.id = r2.id implies r2.items = r1.items 
		
}

pred addValue_with_no_record[vd : ValueDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	k1.records = none and addValueDef[vd, k1, k2, s1, s2]
}
run addValue_with_no_record for 3 but exactly 2 State, 2 Kind

pred addValue_with_one_record[vd : ValueDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	#k1.records = 1 and addValueDef[vd, k1, k2, s1, s2]
}
run addValue_with_one_record for 4 but exactly 2 State, 2 Kind

