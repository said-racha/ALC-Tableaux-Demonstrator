/* Concepts atomiques, roles et instances*/

/*Predicats pour les concepts atomiques*/
cnamea(personne).
cnamea(livre).
cnamea(objet).
cnamea(sculpture).
cnamea(anything).
cnamea(nothing).

/*Predicats pour les concepts non atomiques*/
cnamena(auteur).
cnamena(editeur).
cnamena(sculpteur).
cnamena(parent).

/*Predicats pour les instances*/
iname(michelAnge).
iname(david).
iname(sonnets).
iname(vinci).
iname(joconde).

/*Predicats pour les roles*/
rname(aCree).
rname(aEcrit).
rname(aEdite).
rname(aEnfant).

/*TBox*/

equiv(sculpteur,and(personne,some(aCree,sculpture))).
equiv(auteur,and(personne,some(aEcrit,livre))).
equiv(editeur,and(personne,and(not(some(aEcrit,livre)),some(aEdite,livre)))).
equiv(parent,and(personne,some(aEnfant,anything))).

/*ABox*/

/*Predicats pour les instantiations de concepts*/
inst(michelAnge,personne).
inst(david,sculpture).
inst(sonnets,livre).
inst(vinci,personne).

/*Predicats pour les instantiations de roles*/
inst(joconde,objet).
instR(michelAnge, david, aCree).
instR(michelAnge, sonnets, aEcrit).
instR(vinci, joconde, aCree).
