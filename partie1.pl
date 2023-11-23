/*Verification de la correction semantique*/
/*a ecrire dans la console pour pouvoir verifier?*/
semantique :- setof(X, cnamea(X), ListeConceptsAtomiques),
            setof(X, cnamena(X), ListeConceptsNonAtomiques),
            setof(X, iname(X), ListeInstances),
            setof(X, rname(X), ListeRoles).