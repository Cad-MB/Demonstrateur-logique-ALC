compteur(1).
/*Quelques utilitaires précieux*/

/*Règles de mise sous forme normale négative (nnf : negative normal form) */
nnf(not(and(C1,C2)),or(NC1,NC2)):- nnf(not(C1),NC1),
nnf(not(C2),NC2),!.
nnf(not(or(C1,C2)),and(NC1,NC2)):- nnf(not(C1),NC1), 
nnf(not(C2),NC2),!.
nnf(not(all(R,C)),some(R,NC)):- nnf(not(C),NC),!.
nnf(not(some(R,C)),all(R,NC)):- nnf(not(C),NC),!.
nnf(not(not(X)),X):-!.
nnf(not(X),not(X)):-!.
nnf(and(C1,C2),and(NC1,NC2)):- nnf(C1,NC1),nnf(C2,NC2),!.
nnf(or(C1,C2),or(NC1,NC2)):- nnf(C1,NC1), nnf(C2,NC2),!.
nnf(some(R,C),some(R,NC)):- nnf(C,NC),!.
nnf(all(R,C),all(R,NC)) :- nnf(C,NC),!.
nnf(X,X).

/*member(X,L): Testes si l’élément X appartient à la liste L*/

/*concatenèner les deux listes L1 et L2 et renvoie la liste L3*/
concaten([],L1,L1).
concaten([X|Y],L1,[X|L2]) :- concaten(Y,L1,L2).

/*Supprimer X de la liste L1 et renvoie la liste résultante dans L2*/
enleve(X,[X|L],L) :-!.
enleve(X,[Y|L],[Y|L2]) :- enleve(X,L,L2).

/*Génère un nouvel identificateur qui est fourni en sortie dans Nom*/
genereR(Nom) :-  compteur(V),
                nombre(V,L1),
                concaten([105,110,115,116],L1,L2),
                V1 is V+1,
                dynamic(compteur/1),
                retract(compteur(V)),
                dynamic(compteur/1),
                assert(compteur(V1)),nl,nl,nl,
                name(Nom,L2).

nombre(0,[]).

nombre(X,L1) :- R is (X mod 10), 
                Q is ((X-R)//10),
                chiffre_car(R,R1),
                char_code(R1,R2),
                nombre(Q,L),
                concaten(L,[R2],L1).

chiffre_car(0,'0').
chiffre_car(1,'1').
chiffre_car(2,'2').
chiffre_car(3,'3').
chiffre_car(4,'4').
chiffre_car(5,'5').
chiffre_car(6,'6').
chiffre_car(7,'7').
chiffre_car(8,'8').
chiffre_car(9,'9').

/*flatten(Liste1,Liste2) : Aplanit Liste1 et met le résultat dans Liste2. Liste1 peut 
contenir de nombreuses listes imbriquées récursivement. flatten/2 extrait tous les 
éléments contenus dans Liste1 et stocke le résultat dans une liste "plane" (à une seule 
dimension)*/