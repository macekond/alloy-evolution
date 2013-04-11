open model

pred addKind[k : Kind, disj s1, s2 : State]{
	k not in s1.kinds
	s2.kinds = s1.kinds + k
}
