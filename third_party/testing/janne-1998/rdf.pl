g(B) :- rdf(A), flatten(A, B), format("~s", [B]), fail.
rdf([A,B,C]) :- A="<?xml version='1.0'?>\n<rdf:RDF xmlns:rdf='http://www.w3.org/1999/02/22-rdf-syntax-ns#'\n xmlns:a='http://www.example.org/'>", obj(B), C="\n</rdf:RDF>\n".
obj(A) :- container(A).
obj(A) :- description(A).

description([A,B,C,D,E]) :- A="\n<rdf:Description", idAboutAttr(B),
	                  bagIdAttr(C), propAttr(D), E=" />".
description([A,B,D,E]) :- A="\n<rdf:Description", idAboutAttr(B),
	                  propAttr(D), E=" />".
description([A,C,D,E]) :- A="\n<rdf:Description",
	                  bagIdAttr(C), propAttr(D), E=" />".
description([A,D,E]) :- A="\n<rdf:Description", propAttr(D), E=" />".
description([A,B,C,D,E,F]) :- A="<rdf:Description", idAboutAttr(B),
	bagIdAttr(C), propAttr(C),D=">",
	propertyElt(E), F="\n</rdf:Description>".
description(A) :- typedNode(A).

container(A) :- sequence(A).
container(A) :- bag(A).
container(A) :- alternative(A).

idAboutAttr(A) :- aboutAttr(A).
idAboutAttr(A) :- idAttr(A).
idAboutAttr(A) :- aboutEachAttr(A).

idAttr([A,B,C]) :- A=" rdf:ID='", idsymbol(B), C="'".

aboutAttr([A,B,C]) :- A=" rdf:about='", urireference(B), C="'".

aboutEachAttr([A,B,C]) :- A=" rdf:aboutEach='", urireference(B), C="'".
aboutEachAttr([A,B,C]) :- A=" rdf:aboutEachPrefix='", string(B),C="'".

/*HACK: bagIdAttr([A,B,C]) :- A=" rdf:bagID='",idsymbol(B), C="'". */
 bagIdAttr([A,B,C]) :- A=" rdf:bagID='",B="bagID1", C="'".

propAttr([A,B]) :- A=" ", typeAttr(B).
propAttr([A,B,C,D,E]) :- A=" ", propName(B), C="='", string(D), E="'".
typeAttr([A,B,C]) :- A="rdf:type='", urireference(B), C="'".

propertyElt([A,B,C,E,F,G,B,H]) :- A="\n<",propName(B), idAttr(C), E=">",
		value(F), G="</", propName(B), H=">".
propertyElt([A,B,E,F,G,B,H]) :- A="\n<",propName(B), E=">",
		value(F), G="</", propName(B), H=">".

propertyElt([A,B,C,D,E,F,G,B,H]) :- A="\n<",propName(B), idAttr(C),
		parseLiteral(D),E=">",
		literal(F), G="</",propName(B), H=">".
propertyElt([A,B,D,E,F,G,B,H]) :- A="\n<",propName(B),
		parseLiteral(D),E=">",
		literal(F), G="</",propName(B), H=">".

/*
propertyElt([A,B,C,D,E,F,G,B,H]) :- A="\n<",propName(B), idAttr(C),
		parseResource(D), E=">",
		propertyElt(F), G="</",propName(B), H=">".
propertyElt([A,B,D,E,F,G,B,H]) :- A="\n<",propName(B),
		parseResource(D), E=">",
		propertyElt(F), G="</",propName(B), H=">".
*/

propertyElt([A,B,C,D,F]) :- A="\n<",propName(B),idRefAttr(C),bagIdAttr(D),
		F=" />".
propertyElt([A,B,C,D,E,F]) :- A="\n<",propName(B),idRefAttr(C),bagIdAttr(D),
		propAttr(E),F=" />".

propertyElt([A,B,D,F]) :- A="\n<",propName(B),bagIdAttr(D),
		F=" />".
propertyElt([A,B,C,F]) :- A="\n<",propName(B),idRefAttr(C),
		F=" />".
propertyElt([A,B,F]) :- A="\n<",propName(B),
		F=" />".

propertyElt([A,B,D,E,F]) :- A="\n<",propName(B),bagIdAttr(D),
		propAttr(E),F=" />".
propertyElt([A,B,C,E,F]) :- A="\n<",propName(B),idRefAttr(C),
		propAttr(E),F=" />".
propertyElt([A,B,E,F]) :- A="\n<",propName(B),
		propAttr(E),F=" />".

typedNode([A,B,C,D,E,F]) :- A="\n<",typeName(B),idAboutAttr(C),bagIdAttr(D),
		propAttr(E),F=" />".
typedNode([A,B,C,D,F]) :- A="\n<",typeName(B),idAboutAttr(C),bagIdAttr(D),
		F=" />".

typedNode([A,B,C,E,F]) :- A="\n<",typeName(B),idAboutAttr(C),
		propAttr(E),F=" />".
typedNode([A,B,C,F]) :- A="\n<",typeName(B),idAboutAttr(C),
		F=" />".

typedNode([A,B,E,F]) :- A="\n<",typeName(B),
		propAttr(E),F=" />".
typedNode([A,B,D,F]) :- A="\n<",typeName(B),bagIdAttr(D),
		F=" />".
typedNode([A,B,F]) :- A="\n<",typeName(B),
		F=" />".

typedNode([A,B,C,D,E,F,G,H,B,J]) :- A="\n<",typeName(B),idAboutAttr(C),
		bagIdAttr(D),propAttr(E),F=">",propertyElt(G),H="\n</",
		typeName(B),J=">".
typedNode([A,B,C,D,E,F,H,B,J]) :- A="\n<",typeName(B),idAboutAttr(C),
		bagIdAttr(D),propAttr(E),F=">",H="\n</",
		typeName(B),J=">".

typedNode([A,B,C,E,F,G,H,B,J]) :- A="\n<",typeName(B),idAboutAttr(C),
		propAttr(E),F=">",propertyElt(G),H="\n</",
		typeName(B),J=">".
typedNode([A,B,C,E,F,H,B,J]) :- A="\n<",typeName(B),idAboutAttr(C),
		propAttr(E),F=">",H="\n</",
		typeName(B),J=">".

typedNode([A,B,D,E,F,G,H,B,J]) :- A="\n<",typeName(B),
		bagIdAttr(D),propAttr(E),F=">",propertyElt(G),H="\n</",
		typeName(B),J=">".
typedNode([A,B,D,E,F,H,B,J]) :- A="\n<",typeName(B),
		bagIdAttr(D),propAttr(E),F=">",H="\n</",
		typeName(B),J=">".

typedNode([A,B,E,F,G,H,B,J]) :- A="\n<",typeName(B),
		propAttr(E),F=">",propertyElt(G),H="\n</",
		typeName(B),J=">".
typedNode([A,B,E,F,H,B,J]) :- A="\n<",typeName(B),
		propAttr(E),F=">",H="\n</",
		typeName(B),J=">".

/* HACK: propName(A) :- qname(A). */
propName(A) :- A="a:id1".

/* HACK: typeName(A) :- qname(A). */
typeName(A) :- A="a:id2".

idRefAttr(A) :- idAttr(A).
idRefAttr(A) :- resourceAttr(A).
resourceAttr([A,B,C]) :- A=" rdf:resource='",urireference(B),C="'".
urireference(A) :- member(A,["http://foo.bar.org/"]).
/* HACK: qname([A,B,C]) :- nsprefix(A),B=":", name(C). */
qname([A,B,C]) :- nsprefix(A),B=":", C="author".
idsymbol(A) :- member(A,["idA"]).
name(A) :- member(A,["creator"]).
nsprefix(A) :- member(A,["a"]).

sequence([A,B,C,D,E]) :- A="\n<rdf:Seq", idAttr(B), C=">",
		mem(D), E="</rdf:Seq>".
sequence([A,B,C,E]) :- A="\n<rdf:Seq", idAttr(B), C=">",
		E="</rdf:Seq>".
sequence([A,C,D,E]) :- A="\n<rdf:Seq", C=">",
		mem(D), E="</rdf:Seq>".
sequence([A,C,E]) :- A="\n<rdf:Seq", C=">",
		E="</rdf:Seq>".
sequence([A,B,C,D]) :- A="\n<rdf:Seq", idAttr(B), memberAttr(C), D=" />".
sequence([A,B,D]) :- A="\n<rdf:Seq", idAttr(B), D=" />".
sequence([A,C,D]) :- A="\n<rdf:Seq", memberAttr(C), D=" />".
sequence([A,D]) :- A="\n<rdf:Seq", D=" />".

bag([A,B,C,D,E]) :- A="\n<rdf:Bag", idAttr(B), C=">", mem(D), E="</rdf:Bag>".
bag([A,B,C,E]) :- A="\n<rdf:Bag", idAttr(B), C=">", E="</rdf:Bag>".
bag([A,C,D,E]) :- A="\n<rdf:Bag", C=">", mem(D), E="</rdf:Bag>".
bag([A,C,E]) :- A="\n<rdf:Bag", C=">", E="</rdf:Bag>".
bag([A,B,C,D]) :- A="\n<rdf:Bag", idAttr(B), memberAttr(C), D=" />".
bag([A,B,D]) :- A="\n<rdf:Bag", idAttr(B), D=" />".
bag([A,C,D]) :- A="\n<rdf:Bag", memberAttr(C), D=" />".
bag([A,D]) :- A="\n<rdf:Bag", D=" />".

alternative([A,B,C,D,E]) :- A="\n<rdf:Alt", idAttr(B), C=">",
		mem(D), E="</rdf:Alt>".
alternative([A,C,D,E]) :- A="\n<rdf:Alt", C=">",
		mem(D), E="</rdf:Alt>".
alternative([A,B,C,D]) :- A="\n<rdf:Alt", idAttr(B), memberAttr(C), D=" />".
alternative([A,C,D]) :- A="\n<rdf:Alt", memberAttr(C), D=" />".

mem(A) :- referencedItem(A).
mem(A) :- inlineItem(A).

referencedItem([A,B,C]) :- A="<rdf:li", resourceAttr(B), C=" />".
inlineItem([A,B,C]) :- A="<rdf:li>", value(B), C="</rdf:li>".
memberAttr([A,B,C]) :- A=" rdf:_n='", string(B), C="'".
parseLiteral([A]) :- A=" rdf:parseType='Literal'".
parseResource([A]) :- A=" rdf:parseType='Resource'".

string(A) :- member(A, ["Janne"]).
value(A) :- string(A).
literal(A) :- A="<a:mathml>some markup</a:mathml>".
/* value(A) :- obj(A). */
