/*1. Verification de la correction semantique*/

/*a ecrire dans la console pour pouvoir verifier (pas demande mais bon)?*/
semantique :- setof(X, cnamea(X), ListeConceptsAtomiques),
            setof(X, cnamena(X), ListeConceptsNonAtomiques),
            setof(X, iname(X), ListeInstances),
            setof(X, rname(X), ListeRoles).

/*2. Verification syntaxique*/

/*2.1 Grammaire*/
concept(not(C)) :- concept(C).
concept(and(C1, C2)) :- concept(C1), concept(C2).
concept(or(C1, C2)) :- concept(C1), concept(C2).
concept(some(R, C)) :- role(R), concept(C).
concept(all(R, C)) :- role(R), concept(C).

/*2.2 Concepts atomiques et non atomiques*/
atomic_concept(X) :- cnamea(X).
atomic_concept(X) :- cnamena(X).
