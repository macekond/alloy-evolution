open model

pred moveValueDef[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	k1 in s1.kinds and k1 in s2.kinds
	k2 in s1.kinds and k2 not in s2.kinds
	k3 in s2.kinds and k3 not in s1.kinds	

	vd in k1.structure and vd not in k2.structure

	k3.structure = k2.structure + vd

	#k1.records = #k2.records implies {
	all r1 : Record |
		r1 in k1.records implies one r2 : Record | r2 in k2.records and r1.id = r2.id

	all r3 : Record |
		r3 in k3.records implies one r1, r2 : Record | r1 in k1.records and r2 in k2.records and 
			r1.id = r2.id and  r2.id = r3.id and 
			r3.items = r2.items + {vc : ValueContainer | vc in r1.items and vc.def = vd }
	}

	#k1.records = 0 and #k2.records > 0 implies {
		all r3 : Record |
		r3 in k3.records implies one r2 : Record |r2 in k2.records and  r2.id = r3.id and 
			r3.items = r2.items + {vc : ValueContainer | vc.def = vd }
	}

	#k1.records > 0 and #k2.records = 0 implies {
		all r3 : Record |
		r3 in k3.records implies r3.items = {vc : ValueContainer | vc.def = vd }
	}
}

pred moveValueDef_no_record[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records = 0 and #k2.records = 0  and (k1.structure & k2.structure) = none and moveValueDef[vd, k1, k2, k3, s1, s2]
}
run moveValueDef_no_record for 3 but exactly 2 State, 3 Kind

pred moveValueDef_one_record_in_both[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records = 1 and #k2.records = 1 and (k1.structure & k2.structure) = none and moveValueDef[vd, k1, k2, k3, s1, s2]
}
run moveValueDef_one_record_in_both for 3 but exactly 2 State, 3 Kind

pred moveValueDef_one_record_in_target_only[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records = 0 and #k2.records = 1  and (k1.structure & k2.structure) = none and moveValueDef[vd, k1, k2, k3, s1, s2]
}
run moveValueDef_one_record_in_target_only for 3 but exactly 2 State, 3 Kind

pred moveValueDef_one_record_in_source_only[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records = 1 and #k2.records = 0  and (k1.structure & k2.structure) = none and moveValueDef[vd, k1, k2, k3, s1, s2]
}
run moveValueDef_one_record_in_source_only for 3 but exactly 2 State, 3 Kind
