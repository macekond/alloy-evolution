open model
open addReference
open addProperty
open copyProperty
open changePropertyToClass
open merge
open moveProperty
open split
open addClass
open remClass

sig Evolution {
	path : seq State
}{
	all s1, s2 : State |
		s1 in path.elems and add[1, path.idxOf[s1]] = path.idxOf[s2] implies{
			{one rd : Reference, disj k1, k2 : Class | addReference[rd, k1, k2, s1, s2]} or 
			{one vd : Property, disj k1, k2 : Class | addProperty[vd, k1, k2, s1, s2]} or
			{one vd : Property, disj k1, k2, k3 : Class | copyProperty[vd, k1, k2, k3, s1, s2]} or
			{one vd : Property, disj k1, k2, k3, k4 : Class | moveProperty[vd, k1, k2, k3, k4, s1, s2]} or
			{one disj k1, k2, k3 : Class | merge[k1, k2, k3, s1, s2]} or
			{one vd : Property, disj k1, k2, k3 : Class | splitStructure[vd, k1, k2, k3, s1, s2]} or
			{one k1 : Class | addClass[k1, s1, s2]} or
			{one k1 : Class | remClass[k1, s1, s1]} 
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
