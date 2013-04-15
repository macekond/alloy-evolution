//open evolution
open model
open addReferenceDef
open addValueDef
open copyValueDef
open changeValueDefToKind
open merge
open moveValueDef
open split
open addKind
open remKind

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

pred addValue_with_no_record[vd : ValueDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	k1.records = none and addValueDef[vd, k1, k2, s1, s2]
}
run addValue_with_no_record for 3 but exactly 2 State, 2 Kind

pred addValue_with_no_record_but_reference[vd : ValueDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	k1.records = none and one ref : ReferenceDef | ref in k1.structure.elems and addValueDef[vd, k1, k2, s1, s2]
}
run addValue_with_no_record_but_reference for 3 but exactly 2 State, 3 Kind

pred addValue_with_no_record_but_reference_on_self[rd: ReferenceDef, vd : ValueDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	k1.records = none 
	and rd.reference = k1.name
	and rd  in k1.structure.elems
	and addValueDef[vd, k1, k2, s1, s2]
}
run addValue_with_no_record_but_reference_on_self for 3 but exactly 2 State, 2 Kind


pred addValue_with_one_record[vd : ValueDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	#k1.records = 1 and addValueDef[vd, k1, k2, s1, s2]
}
run addValue_with_one_record for 2 but exactly 2 State, 2 Kind, 0 ReferenceDef

pred addValue_with_one_record_and_reference_on_self[rd: ReferenceDef, vd : ValueDef, disj k1, k2 : Kind, disj s1, s2 :  State]{
	#k1.records = 1
	and rd.reference = k1.name
	and rd  in k1.structure.elems
	and addValueDef[vd, k1, k2, s1, s2]
}
run addValue_with_one_record_and_reference_on_self for 4 but exactly 2 State, 2 Kind

pred addValue_with_one_record_and_reference_on_self_from_other[rd: ReferenceDef, vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 :  State]{
	#k1.records = 1
	and rd.reference = k1.name
	and rd  in k3.structure.elems
	and k3 in s1.kinds
	and addValueDef[vd, k1, k2, s1, s2]
}
run addValue_with_one_record_and_reference_on_self_from_other for 4 but exactly 2 State



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



pred changeValueDefToKind_no_records[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records = 0 and changeValueDefToKind[vd, k1, k2, k3, s1, s2]
}
run changeValueDefToKind_no_records for 3 but exactly 2 State, 3 Kind

pred changeValueDefToKind_one_record[vd : ValueDef, disj k1, k2, k3 : Kind, disj s1, s2 : State]{
	#k1.records = 1 and changeValueDefToKind[vd, k1, k2, k3, s1, s2]
}
run changeValueDefToKind_one_record for 3 but exactly 2 State, 3 Kind




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




pred moveValueDef_no_record[vd : ValueDef, disj k1, k2, k3, k4 : Kind, disj s1, s2 : State]{
	#k1.records = 0 and #k2.records = 0  and (k1.structure.elems & k2.structure.elems) = none and moveValueDef[vd, k1, k2, k3, k4, s1, s2]
}
run moveValueDef_no_record for 3 but exactly 2 State, 4 Kind

pred moveValueDef_one_record_in_both[vd : ValueDef, disj k1, k2, k3, k4  : Kind, disj s1, s2 : State]{
	#k1.records = 1 and #k2.records = 1 and (k1.structure.elems & k2.structure.elems)  = none and moveValueDef[vd, k1, k2, k3, k4, s1, s2]
}
run moveValueDef_one_record_in_both for 4 but exactly 2 State, 4 Kind

pred moveValueDef_one_record_in_target_only[vd : ValueDef, disj k1, k2, k3, k4  : Kind, disj s1, s2 : State]{
	#k1.records = 0 and #k2.records = 1 and (k1.structure.elems & k2.structure.elems)  = none and moveValueDef[vd, k1, k2, k3, k4, s1, s2]
}
run moveValueDef_one_record_in_target_only for 4 but exactly 2 State, 4 Kind





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
run split_with_no_record for 3 but exactly 2 State, 3 Kind


