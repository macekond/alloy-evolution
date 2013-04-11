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

pred scenario1[disj k1, k2, k3, k4 : Kind, disj s1, s2, s3, s4, s5, s6 : State, vd : ValueDef]{
	#s1.kinds = 0
	addKind[k1, s1, s2]
	addKind[k2, s2, s3]
	addValueDef[vd, k1, k3, s3, s4]
	copyValueDef[vd, k3, k2, k4, s4, s5]
	remKind[k4, s5, s6]
	remKind[k3, s6, s1]
}
run scenario1 for 6

pred scenario2[disj k1, k2, k3, k4 : Kind, disj s1, s2, s3, s4: State, vd : ValueDef]{
	#s1.kinds = 0
	vd in k1.structure.elems
	addKind[k1, s1, s2]
	splitStructure[vd, k1, k2, k3, s2, s3]
	merge[k2, k3, k4, s3, s4]
}
run scenario2 for 6 but exactly 4 State
