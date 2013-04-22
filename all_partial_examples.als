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

//1
pred addReference_with_no_record[rd : Reference, disj k1, k2 : Class, disj s1, s2 :  State]{
	k1.instances = none and addReference[rd, k1, k2, s1, s2]
}
run addReference_with_no_record for 3 but exactly 2 State, 2 Class

pred addReference_with_one_record[rd : Reference, disj k1, k2 : Class, disj s1, s2 :  State]{
	#k1.instances = 1 and addReference[rd, k1, k2, s1, s2]
}
run addReference_with_one_record for 4 but exactly 2 State, 2 Class

pred addReference_on_other_with_no_record[rd : Reference, disj k1, k2, k3 : Class, disj s1, s2 :  State]{
	rd.reference = k3.name and #k1.instances = 0 and addReference[rd, k1, k2, s1, s2]
}
run addReference_on_other_with_no_record for 4 but exactly 2 State, 3 Class

pred addReference_on_other_with_some_record[rd : Reference, disj k1, k2, k3 : Class, disj s1, s2 :  State]{
	rd.reference = k3.name and #k1.instances > 0 and addReference[rd, k1, k2, s1, s2]
}
run addReference_on_other_with_some_record for 4 but exactly 2 State, 3 Class

//5
pred addValue_with_no_record[vd : Property, disj k1, k2 : Class, disj s1, s2 :  State]{
	k1.instances = none and addProperty[vd, k1, k2, s1, s2]
}
run addValue_with_no_record for 3 but exactly 2 State, 2 Class

pred addValue_with_no_record_but_reference[vd : Property, disj k1, k2 : Class, disj s1, s2 :  State]{
	k1.instances = none and one ref : Reference | ref in k1.structure.elems and addProperty[vd, k1, k2, s1, s2]
}
run addValue_with_no_record_but_reference for 3 but exactly 2 State, 3 Class

pred addValue_with_no_record_but_reference_on_self[rd: Reference, vd : Property, disj k1, k2 : Class, disj s1, s2 :  State]{
	k1.instances = none 
	and rd.reference = k1.name
	and rd  in k1.structure.elems
	and addProperty[vd, k1, k2, s1, s2]
}
run addValue_with_no_record_but_reference_on_self for 3 but exactly 2 State, 2 Class


pred addValue_with_one_record[vd : Property, disj k1, k2 : Class, disj s1, s2 :  State]{
	#k1.instances = 1 and addProperty[vd, k1, k2, s1, s2]
}
run addValue_with_one_record for 5 but exactly 2 State, 2 Class, 0 Reference

pred addValue_with_one_record_and_reference_on_self[rd: Reference, vd : Property, disj k1, k2 : Class, disj s1, s2 :  State]{
	#k1.instances = 1
	and rd.reference = k1.name
	and rd  in k1.structure.elems
	and addProperty[vd, k1, k2, s1, s2]
}
run addValue_with_one_record_and_reference_on_self for 5 but exactly 2 State, 2 Class

//10
pred addValue_with_one_record_and_reference_on_self_from_other[rd: Reference, vd : Property, disj k1, k2, k3 : Class, disj s1, s2 :  State]{
	#k1.instances = 1
	and rd.reference = k1.name
	and rd  in k3.structure.elems
	and k3 in s1.classes
	and addProperty[vd, k1, k2, s1, s2]
}
run addValue_with_one_record_and_reference_on_self_from_other for 4 but exactly 2 State


pred copyProperty_no_record[vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances = 0 and #k2.instances = 0 and copyProperty[vd, k1, k2, k3, s1, s2]
}
run copyProperty_no_record for 3 but exactly 2 State, 3 Class

pred copyProperty_no_record_in_target[vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k2.instances = 0 and copyProperty[vd, k1, k2, k3, s1, s2]
}
run copyProperty_no_record_in_target for 3 but exactly 2 State, 3 Class

pred copyProperty_one_record_in_target[vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k2.instances = 1 and copyProperty[vd, k1, k2, k3, s1, s2]
}
run copyProperty_one_record_in_target for 6 but exactly 2 State, 3 Class



pred changePropertyToClass_no_instances[vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances = 0 and changePropertyToClass[vd, k1, k2, k3, s1, s2]
}
run changePropertyToClass_no_instances for 3 but exactly 2 State, 3 Class

//15
pred changePropertyToClass_one_record[vd : Property, disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances = 1 and changePropertyToClass[vd, k1, k2, k3, s1, s2]
}
run changePropertyToClass_one_record for 3 but exactly 2 State, 3 Class




pred merge_with_no_record_no_ref[disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances = 0 and #k2.instances = 0 and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record_no_ref for 3 but exactly 3 Class, 2 State, 0 Reference

pred merge_with_no_record[disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances = 0 and #k2.instances = 0 and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record for 3 but exactly 3 Class, 2 State

pred merge_with_record_in_one[disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances = 1 and #k2.instances = 0 and merge[k1, k2, k3, s1, s2]
}
run merge_with_record_in_one for 3 but exactly 3 Class, 2 State

pred merge_with_record_in_both[disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances = 1 and #k2.instances = 1 and merge[k1, k2, k3, s1, s2]
}
run merge_with_record_in_both for 3 but exactly 3 Class, 2 State

pred merge_with_record_and_values_in_both[disj k1, k2, k3 : Class, disj s1, s2 : State]{
	#k1.instances.items.values = 1 and #k2.instances.items.values = 1 and merge[k1, k2, k3, s1, s2]
}
run merge_with_record_and_values_in_both for 3 but exactly 3 Class, 2 State

pred merge_with_no_record_and_reference[disj k1, k2, k3 : Class, disj s1, s2 : State, rd : Reference]{
	#k1.instances = 0 and #k2.instances = 0 and rd.reference = k2.name and rd in k2.structure.elems  and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record_and_reference for 3 but exactly 3 Class, 2 State

pred merge_with_no_record_and_reference2[disj k1, k2, k3 : Class, disj s1, s2 : State, rd : Reference]{
	#k1.instances = 0 and #k2.instances = 0 and rd.reference = k2.name and rd in k1.structure.elems  and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record_and_reference2 for 3 but exactly 3 Class, 2 State

pred merge_with_no_record_and_reference_in_other[disj k, k1, k2, k3 : Class, disj s1, s2 : State, rd : Reference]{
	#k.instances = 0 and #k1.instances = 0 and #k2.instances = 0 and rd.reference = k2.name and rd in k.structure.elems and k in s1.classes and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record_and_reference_in_other for 3 but exactly 5 Class, 2 State

pred merge_with_no_record_and_no_reference_in_other[disj k, k1, k2, k3 : Class, disj s1, s2 : State]{
	#k.instances = 0 and #k1.instances = 0 and #k2.instances = 0  and k in s1.classes and merge[k1, k2, k3, s1, s2]
}
run merge_with_no_record_and_no_reference_in_other for 3 but exactly 4 Class, 2 State, 0 Reference




pred moveProperty_no_record[vd : Property, disj k1, k2, k3, k4 : Class, disj s1, s2 : State]{
	#k1.instances = 0 and #k2.instances = 0  and (k1.structure.elems & k2.structure.elems) = none and moveProperty[vd, k1, k2, k3, k4, s1, s2]
}
run moveProperty_no_record for 3 but exactly 2 State, 4 Class

pred moveProperty_one_record_in_both[vd : Property, disj k1, k2, k3, k4  : Class, disj s1, s2 : State]{
	#k1.instances = 1 and #k2.instances = 1 and (k1.structure.elems & k2.structure.elems)  = none and moveProperty[vd, k1, k2, k3, k4, s1, s2]
}
run moveProperty_one_record_in_both for 4 but exactly 2 State, 4 Class

pred moveProperty_one_record_in_target_only[vd : Property, disj k1, k2, k3, k4  : Class, disj s1, s2 : State]{
	#k1.instances = 0 and #k2.instances = 1 and (k1.structure.elems & k2.structure.elems)  = none and moveProperty[vd, k1, k2, k3, k4, s1, s2]
}
run moveProperty_one_record_in_target_only for 4 but exactly 2 State, 4 Class





pred split_with_two_value_defs[disj k1, k2, k3 : Class, disj s1, s2 : State, vd : Property ]{
		#k1.structure.elems = 2 and splitStructure[vd, k1, k2, k3, s1, s2]
}
run split_with_two_value_defs for 4 but exactly 2 State, 3 Class


pred split_with_one_record[disj k1, k2, k3 : Class, disj s1, s2 : State, vd : Property ]{
	#k1.instances = 1 and splitStructure[vd, k1, k2, k3, s1, s2]
}
run split_with_one_record for 3 but exactly 2 State, 3 Class

pred split_with_no_record[disj k1, k2, k3 : Class, disj s1, s2 : State, vd : Property ]{
	#k1.instances = 0 and splitStructure[vd, k1, k2, k3, s1, s2]
}
run split_with_no_record for 3 but exactly 2 State, 3 Class


