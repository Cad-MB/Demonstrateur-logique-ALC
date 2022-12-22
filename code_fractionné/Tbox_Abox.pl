/*Représentation de la Tbox et la Abox*/

/*Alphabet*/
    /*Concepts Atomiques*/
cnamea(personne).
cnamea(livre).
cnamea(objet).
cnamea(sculpture).
cnamea(anything).
cnamea(nothing).
    /*Concepts Non-Atomiques*/
cnamena(auteur).
cnamena(editeur).
cnamena(sculpteur).
cnamena(parent).
    /*Rôles*/
rname(aCree).
rname(aEcrit).
rname(aEdite).
rname(aEnfant).
    /*Instances*/
iname(michelAnge).
iname(david).
iname(sonnets).
iname(vinci).
iname(joconde).


/*Base de connaissances*/
    /*TBox*/
        /*Définitions*/
            /*Sculpteur*/
equiv(sculpteur,and(personne,some(aCree,sculpture))).
            /*Auteur*/
equiv(auteur,and(personne,some(aEcrit,livre))).
            /*Editeur*/
equiv(editeur,and(personne,and(not(some(aEcrit,livre)),some(aEdite,livre)))).
            /*Enfant*/
equiv(parent,and(personne,some(aEnfant,anything))).

    /*ABox*/
        /*Assertions de concepts*/
inst(michelAnge,personne).
inst(david,sculpture).
inst(sonnets,livre).
inst(vinci,personne).
inst(joconde,objet).
        /*Assertions de rôles*/
instR(michelAnge, david, aCree).
instR(michelAnge, sonnets, aEcrit).
instR(vinci, joconde, aCree).