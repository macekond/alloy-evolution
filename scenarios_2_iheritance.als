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
open remParent
open addParent


pred pulldown[disj k1, k2, k3, k4 : Kind, vd : ValueDef, disj s1, s2 : State]{
	vd in k1.structure.elems
	k2.parent = k1.name
	k1 in s1.kinds
	k2 in s1.kinds
	moveValueDef[vd, k1, k2, k3, k4, s1, s2]
}
run pulldown for 4


