open model

pred addReferenceDef[rd : ReferenceDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	k2 not in s1.kinds
	s2.kinds = s1.kinds - k1 + k2

	k1.name = k2.name

	rd not in k1.structure.elems

	rd.reference in s1.kinds.name and rd.reference in s2.kinds.name

	k2.structure = k1.structure.add[rd]
	
	#k1.records = #k2.records
	all r2 : Record |
		r2 in k2.records implies one r1 : Record |
			r1 in k1.records and r1.id = r2.id implies r2.items.subseq[0, r2.items.lastIdx-1] = r1.items 
		
}

pred addReference_with_no_record[rd : ReferenceDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	k1.records = none and addReferenceDef[rd, k1, k2, s1, s2]
}
run addReference_with_no_record for 3 but exactly 2 State, 2 Kind

pred addReference_with_one_record[rd : ReferenceDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	#k1.records = 1 and addReferenceDef[rd, k1, k2, s1, s2]
}
run addReference_with_one_record for 4 but exactly 2 State, 2 Kind

pred addReference_on_other_with_no_record[rd : ReferenceDef, disj k1, k2, k3 : Kind, disj s1, s2 :  State]{
	rd.reference = k3.name and #k1.records = 0 and addReferenceDef[rd, k1, k2, s1, s2]
}
run addReference_on_other_with_no_record for 4 but exactly 2 State, 3 Kind

pred addReference_on_other_with_some_record[rd : ReferenceDef, disj k1, k2, k3 : Kind, disj s1, s2 :  State]{
	rd.reference = k3.name and #k1.records > 0 and addReferenceDef[rd, k1, k2, s1, s2]
}
run addReference_on_other_with_some_record for 4 but exactly 2 State, 3 Kind
