open model

pred copyValueDef[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	k1 in s1.kinds and k1 in s2.kinds
	k2 in s2.kinds and k2 not in s1.kinds
	k3 in s2.kinds and k3 not in s1.kinds	

	vd in k1.structure and vd not in k2.structure

	k3.structure = k2.structure + vd
//	k3.records = k2.records
	all r3 : Record |
		r3 in k3.records implies one r2 : Record | 
			r2 in k2.records and r3.items = r2.items + { vc : ValueContainer | vc.def = vd } //this should not exist in a model (as part of k1.records.items)
}
run copyValueDef

pred copyValueDef_no_record[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records = 0 and #k2.records = 0 and copyValueDef[vd, k1, k2, k3, s1, s2]
}
run copyValueDef_no_record for 3 but exactly 2 State, 3 Kind

pred copyValueDef_no_record_in_target[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k2.records = 0 and copyValueDef[vd, k1, k2, k3, s1, s2]
}
run copyValueDef_no_record_in_target for 3 but exactly 2 State, 3 Kind

pred copyValueDef_one_record_in_target[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k2.records = 1 and copyValueDef[vd, k1, k2, k3, s1, s2]
}
run copyValueDef_one_record_in_target for 3 but exactly 2 State, 3 Kind
