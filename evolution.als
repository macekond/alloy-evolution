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

sig Evolution {
	path : seq State
}{
	all s1, s2 : State |
		s1 in path.elems and add[1, path.idxOf[s1]] = path.idxOf[s2] implies{
			{one rd : ReferenceDef, disj k1, k2 : Kind | addReferenceDef[rd, k1, k2, s1, s2]} or 
			{one vd : ValueDef, disj k1, k2 : Kind | addValueDef[vd, k1, k2, s1, s2]} or
			{one vd : ValueDef, disj k1, k2, k3 : Kind | copyValueDef[vd, k1, k2, k3, s1, s2]} or
			{one vd : ValueDef, disj k1, k2, k3, k4 : Kind | moveValueDef[vd, k1, k2, k3, k4, s1, s2]} or
			{one disj k1, k2, k3 : Kind | merge[k1, k2, k3, s1, s2]} or
			{one vd : ValueDef, disj k1, k2, k3 : Kind | splitStructure[vd, k1, k2, k3, s1, s2]} or
			{one k1 : Kind | addKind[k1, s1, s2]} or
			{one k1 : Kind | remKind[k1, s1, s1]} 
			//or	skip[s1, s2]
		}
}

fact states_are_in_evolution{
	all s : State |
		some e : Evolution | s in e.path.elems
}

pred skip[s1, s2: State]{
	s1 = s2
} 

run {}
