open model

pred remKind[k : Kind, disj s1, s2 : State]{
	k in s1.kinds
	s2.kinds = s1.kinds - k
}
