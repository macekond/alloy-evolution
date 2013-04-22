sig State{
	classes : set Class
}

sig Class{
	parentName: lone Name,
	parent :  lone Class,
	name : one Name,
	instances : set Instance,
	structure : seq Def
}{
	some s : State |
		this in s.classes

	 !structure.hasDups	
}

sig Instance{
	items : seq Container,
	id : Int
}{
	//record in a kind
	some k : Class |
		this in k.instances

	//if multiple owning classes => they have same name => the same kind in different states
	all k1, k2 : Class |
		this in k1.instances and this in k2.instances implies k1.name = k2.name		
	
	//no duplicates of containers 
	!items.hasDups
	
	//number of items is equal to number of definitions defying the structure of the owning kind
	#items = #(this.~instances.structure)	
}

abstract sig Container{
	//values : set (Value + Int)
}{
	some r : Instance |
		this in r.items.elems
	
	all disj k1, k2 : Class |
		this in k1.instances.items.elems and this in k2.instances.items.elems implies k1.~classes & k2.~classes = none
}

sig ValueContainer extends Container{
	
}{
	//values in Value
	//#values >= 1
}

sig ReferenceContainer extends Container{
		values : set Int
}{

}

/*
sig Value{}{
	one vc : ValueContainer |
		this in vc.values
}
*/
sig Name{}{
	some k : Class |
		this in k.name
}

abstract sig Def{

}{
	some k : Class |
		this in k.structure.elems
}

sig Property extends Def{

}


sig Reference extends Def{
	reference : one Name
}{

}

/* ************************************************************************************************** */

fact not_same_ids_in_classes{
	all disj r1, r2 : Instance |
		r1.id = r2.id implies r1.(~instances) != r2.(~instances)

	//no duplicate ids
	all k : Class, disj r1, r2 : Instance |
		r1 in k.instances and r2 in k.instances implies r1.id != r2.id
}

fact not_same_name_of_classes_in_same_states{
	all disj k1, k2 : Class |
		k1.name = k2.name implies no s : State | s in k1.~classes and s in k2.~classes
}

fact structure_of_record_in_kind{
	all k : Class, r : Instance, vc : ValueContainer |
		vc in r.items.elems and r in k.instances implies
				 one vd : Property | vd in k.structure.elems and k.structure.idxOf[vd] = r.items.idxOf[vc]

	all k : Class, r : Instance, rc : ReferenceContainer |
			rc in r.items.elems and r in k.instances implies
				 one rd : Reference | rd in k.structure.elems and k.structure.idxOf[rd] = r.items.idxOf[rc]

	all k : Class, r : Instance, vd : Property |
		vd in k.structure.elems   and r in k.instances implies
			 one vc : ValueContainer | vc in r.items.elems and k.structure.idxOf[vd] = r.items.idxOf[vc]		
}

fact no_same_defs_in_classes_of_a_state{
	all disj k1, k2 : Class, d : Def |
		d in k1.structure.elems and d in k2.structure.elems implies k1.~classes != k2.~classes
}

fact refereces_are_ids_of_referenced{
	all k : Class, rd : Reference, rc : ReferenceContainer, r : Instance |
		r in k.instances	
		and rd in k.structure.elems
		and rc in r.items.elems
		and r.items.idxOf[rc] = k.structure.idxOf[rd] implies
			rc.values in rd.reference.~name.instances.id 
}

fact referenced_name_and_reference_are_in_same_state{
	all rd : Reference |
	{s : State | rd in s.classes.structure.elems} in rd.reference.~name.~classes
}

fact no_overriding{
	all disj k1, k2 : Class |
		k1.parentName= k2.name implies
			no d : Def | d in k1.structure.elems and d in k2.structure.elems
}

fact parent_and_child_in_same_states{
	all k1, k2 : Class |
		k1.parentName= k2.name implies some s : State | s in k1.~classes and s in k2.~classes
}

fact no_cyclical_inheritance{
	no k : Class | k.parentName= k.name
	all k1, k2 : Class | k2.parent = k1 implies k2 not in k1.*parent
}

fact parent_definition{
	all k1, k2 : Class |
		k1.parent = k2 implies some s : State | s in k2.~classes and s in k1.~classes //or (k1.~classes in k2.~classes)

	all k1 : Class |
		k1.parentName= none implies k1.parent = none 

	all k1 : Class |
		k1.parentName!=none implies k1.parent != none

	all k1, k2 : Class |
		  k1.parent = k2 implies k1.parentName= k2.name
}

fact ids_in_hierarchy_are_same{
	all disj k1, k2 : Class |
		k1.parentName= k2.name and k1.~classes in k2.~classes implies 
			all r1 : Instance | r1 in k1.instances implies 
				one r2 : Instance | r2 in k2.instances and r1.id = r2.id
}

/* ************************************************************************************************** */
fun children(k: Class, s : State) : set Class{
	{ k1 : Class | k1.parent = k and k in s.classes and k1 in s.classes}
}

fun coupling(k1, k2 : Class, s : State) : one Int{
	k1 in s.classes and k2 in s.classes implies
		#{rd : Reference | rd in k1.structure.elems and rd.reference = k2.name}
	else 0
}

fun parentsInState(k : Class, s : State) : set Class{
	k.{ k1, k2 : Class | 
			k1 in s.classes and k2 in k1.*parent and k2 in s.classes and k1 != k2}
}
/* ************************************************************************************************** */
//PREDICATES EXAMINING MAX INHERITANCE DEPTH
pred depth_preserved[s1, s2 : State]{
	{(not depth_increased[s1, s2]) and (not depth_decreased[s1, s2])}
}

pred depth_decreased[s1, s2 : State]{
	#s1.classes = 0 and #s2.classes > 0 implies #s1.classes != 0 else
		all k2 : Class | k2 in s2.classes implies some k1 : Class | k1 in s1.classes and #parentsInState[k1, s1] > #parentsInState[k2, s2]
}

pred depth_increased[s1, s2 : State]{
		#s1.classes = 0 and #s2.classes > 0 implies #s1.classes != 0 else
		all k1 : Class | k1 in s1.classes implies some k2 : Class | k2 in s2.classes and #parentsInState[k1, s1] < #parentsInState[k2, s2]
}

// PREDICATES EXAMINING MAX NUMBER OF CHILDREN
pred children_preserve[s1, s2: State]{
	(not children_increase[s1, s2]) and (not children_decrease[s1, s2])
}

pred children_increase[s1, s2 : State]{
	({#s1.classes = 0 and #s2.classes > 0} or {#s1.classes = 0 and #s2.classes = 0}) implies #s1.classes != 0 else
	all k1 : Class | k1 in s1.classes implies some k2 : Class | k2 in s2.classes and #k1.children[s1] < #k2.children[s2]
}

pred children_decrease[s1, s2 : State]{
	((#s1.classes = 0 and #s2.classes = 0) or (#s1.classes = 0 and #s2.classes > 0)) implies #s1.classes != 0  else
	all k2 : Class | k2 in s2.classes implies some k1 : Class | k1 in s1.classes and #k1.children[s1] > #k2.children[s2]
}

//PREDICATES EXAMINING COUPLING
pred coupling_preserve[s1,s2 : State]{
	(not coupling_increase[s1,s2]) and (not coupling_decrease[s1, s2])
}

pred coupling_increase[s1,s2 : State]{
	({#s1.classes = 0 and #s2.classes = 0}) implies #s1.classes != 0 else
	all k1, k12 : Class | 
		(k1 in s1.classes and k12 in s1.classes) implies 
			some k2, k22 : Class | k2 in s2.classes and k22 in s2.classes and coupling[k1, k12, s1] < coupling[k2, k22, s2]
}

pred coupling_decrease[s1,s2 : State]{
	({#s1.classes = 0 and #s2.classes > 0} or {#s1.classes = 0 and #s2.classes = 0}) implies #s1.classes != 0 else
	all k2, k22 : Class | 
		(k2 in s2.classes and k22 in s2.classes) implies 
			some k1, k12 : Class | k1 in s1.classes and k12 in s1.classes and coupling[k1, k12, s1] > coupling[k2, k22, s2]
}
/* ************************************************************************************************** */

run {
	some k1, k2 : Class |
		k1.parentName= none and k2.parentName= k1.name
} for 5 but exactly 2 State

run {
	some k1, k2, k3 : Class |
		k1.parentName= k2.name and k2.parentName= k3.name //and k1 = k3
} for 5 but exactly 2 State
