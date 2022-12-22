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

/*Partie 1 - Etape préliminaire de vérification et de mise en forme de la Tbox et de la Abox*/
/*Implémentation de la partie 1*/

/*Correction sémantique et syntaxique*/
    /*Concept*/
        /*Atomique*/
concept(C) :-   setof(X,cnamea(X),L), 
                member(C,L),!.
        /*Non-Atomique*/
concept(C) :-   setof(X,cnamena(X),L), 
                member(C,L),!.
        /*¬*/
concept(not(C)) :- concept(C),!.
        /*⊔*/
concept(or(C1, C2)) :-  concept(C1), 
                        concept(C2),!.
        /*⊓*/
concept(and(C1, C2)) :- concept(C1), 
                        concept(C2),!.
        /*∃*/
concept(some(R, C)) :-  role(R), 
                        concept(C),!.
        /*∀*/
concept(all(R, C)) :-   role(R), 
                        concept(C),!.
        /*Role*/
role(R) :-      setof(X,rname(X),L), 
                member(R,L),!.
        /*Instance*/
instance(I) :- setof(X,iname(X),L), 
                member(I,L),!.
        /*Assertions de concepts*/
instanciation(I,C) :-   instance(I), 
                        concept(C),!.
        /*Assertions de rôles*/
instanciationR(I1,I2,R) :-      instance(I1), 
                                instance(I2), 
                                role(R),!.

/*Test concept complexe auto-référent*/
        /*cas trivial*/
autoref(Ca,Ca).
        /*¬*/
autoref(Cna,not(D)) :- autoref(Cna,D),!.
        /*⊔*/
autoref(Cna,or(D,_)) :- autoref(Cna,D),!.
autoref(Cna,or(_,D)) :- autoref(Cna,D),!.
        /*⊓*/
autoref(Cna,and(D,_)) :- autoref(Cna,D),!.
autoref(Cna,and(_,D)) :- autoref(Cna,D),!.
        /*∃*/
autoref(Cna,some(_,D)) :- autoref(Cna,D),!.
        /*∀*/
autoref(Cna,all(_,D)) :- autoref(Cna,D),!.
        /*≡*/
autoref(Cna,equiv(D,_)) :- autoref(Cna,D),!.
autoref(Cna,equiv(_,D)) :- autoref(Cna,D),!.
/*Test concept complexe pas auto-référent*/
pas-autoref(Cna,D) :- not(autoref(Cna,D)).

/*Remplacement d'une expression conceptuelle équivalente à un concept complexe défini dans la Tbox par une expression où ne figurent plus que des identificateurs de concepts atomiques et qui a été mise en nnf*/
        /*Dissection d'un concepte complexe*/
                /*Concepte atomique (deja traitee)*/
traitement_box_couple(Ca,Ca) :- cnamea(Ca),!.
                /*¬*/
traitement_box_couple(not(Cna),not(Ca)) :- traitement_box_couple(Cna,Ca),!.
                /*⊔*/
traitement_box_couple(or(Cna1,Cna2),or(Ca1,Ca2)) :-    traitement_box_couple(Cna1,Ca1), 
                                                        traitement_box_couple(Cna2,Ca2),!.
                /*⊓*/
traitement_box_couple(and(Cna1,Cna2),and(Ca1,Ca2)) :-  traitement_box_couple(Cna1,Ca1), 
                                                        traitement_box_couple(Cna2,Ca2),!.
                /*∃*/
traitement_box_couple(some(R,Cna),some(R,Ca)) :- traitement_box_couple(Cna,Ca),!.
                /*∀*/
traitement_box_couple(all(R,Cna),all(R,Ca)) :- traitement_box_couple(Cna,Ca),!.
                /*≡*/
traitement_box_couple(Cna,Ca) :-        equiv(Cna,D),
                                        traitement_box_couple(D,Ca),!.


        /*Traitement*/
                /*TBox*/
traitement_Tbox([],[]).
traitement_Tbox([(Cna,D)|Reste_Tbox_non_traitee],[(Cna,DTnnf)|Reste_Tbox_traitee]) :-   traitement_box_couple(D,DT), 
                                                                                        nnf(DT,DTnnf), 
                                                                                        traitement_Tbox(Reste_Tbox_non_traitee,Reste_Tbox_traitee).
                /*ABox*/
traitement_Abox([],[]).
traitement_Abox([(I,C)|Reste_Abox_non_traitee],[(I,CTnnf)|Reste_Abox_traitee]) :-           traitement_box_couple(C,CT), 
                                                                                        nnf(CT,CTnnf), 
                                                                                        traitement_Abox(Reste_Abox_non_traitee,Reste_Abox_traitee).
                                                                                
/*Predicat de cette 1er partie*/
premiere_etape(Tbox,Abi,Abr) :-         
                                        setof((Cna,D),(equiv(Cna,D)),Tb),
                                        traitement_Tbox(Tb,Tbox),
                                        setof((I,C),inst(I,C),Ai),
                                        traitement_Abox(Ai,Abi),
                                        setof((I1,I2,R),instR(I1,I2,R),Abr),!.

/*Predicat de cette 1er partie*/


/*Partie 2 - Saisie de la proposition à démontrer*/
/*Implémentation de la partie 1*/

/*Predicat de cette 2eme partie*/
deuxieme_etape(Abi,Abi1,Tbox) :-    
                                    saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

/**/
saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :- nl,
                                                        write('Entrez le numero du type de proposition que vous voulez demontrer :'),
                                                        nl,
                                                        write('1 Une instance donnee appartient a un concept donne.'),
                                                        nl,
                                                        write('2 Deux concepts n"ont pas d"elements en commun(ils ont une intersection vide).'),
                                                        nl, 
                                                        read(R), 
                                                        suite(R,Abi,Abi1,Tbox).

/**/
suite(1,Abi,Abi1,Tbox) :- acquisition_prop_type1(Abi,Abi1,Tbox),!.

/**/
suite(2,Abi,Abi1,Tbox) :- acquisition_prop_type2(Abi,Abi1,Tbox),!.

/**/
suite(R,Abi,Abi1,Tbox) :-   nl,
                            write('Cette reponse est incorrecte.'),
                            nl,
                            saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox),!.

/*Proposition de type -> I:C*/
acquisition_prop_type1(Abi,Abi1,Tbox) :-    nl,
                                            write('L instance I = '),
                                            read(I),
                                            nl,
                                            write('Le concept C = '),
                                            read(C),
                                            instanciation(I,C),
                                            pas-autoref(I,C),
                                            traitement_box_couple(C,CT),
                                            nnf(CT, CTnnf),
                                            concaten([(I,CTnnf)],Abi,Abi1),
                                            nl.
                                            

/*Proposition de type -> C1⊓C2 ⊑ ⊥*/
acquisition_prop_type2(Abi,Abi1,Tbox) :-    nl,
                                            write('Le concept C1 = '),
                                            read(C1),
                                            nl,
                                            write('Le concept C2 = '),
                                            read(C2),
                                            concept(C1),
                                            concept(C2),
                                            traitement_box_couple(and(C1,C2),CT),
                                            nnf(CT, CTnnf),
                                            genereR(Nom),
                                            concaten([(Nom,CTnnf)],Abi,Abi1),
                                            nl.



                                            /*Partie 3 - Saisie de la proposition à démontrer*/
/*Implémentation de la partie 3*/

/*Predicat de cette 3eme partie*/
troisieme_etape(Abi,Abr) :-    
                                tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
                                resolution(Lie,Lpt,Li,Lu,Ls,Abr),
                                nl,
                                write('Youpiiiiii, on a demontre la proposition initiale !!!').

/*tri_Abox : Abe ---> Lie,Lpt,Li,Lu,Ls,Abr*/
    /*∃ --> Lie*/
tri_Abox([(I,some(R,C))|Abe_rest],Lie1,Lpt,Li,Lu,Ls) :- instance(I),
                                                        concept(some(R, C)),
                                                        tri_Abox(Abe_rest,Lie0,Lpt,Li,Lu,Ls), 
                                                        concaten([(I,some(R,C))],Lie0,Lie1).

    /*∀ --> Lpt*/
tri_Abox([(I,all(R,C))|Abe_rest],Lie,Lpt1,Li,Lu,Ls) :-  instance(I),
                                                        concept(all(R, C)),
                                                        tri_Abox(Abe_rest,Lie,Lpt0,Li,Lu,Ls), 
                                                        concaten([(I,all(R,C))],Lpt0,Lpt1). 

    /*⊓ --> Li*/
tri_Abox([(I,and(C1,C2))|Abe_rest],Lie,Lpt,Li1,Lu,Ls) :-    instance(I),
                                                            concept(and(C1, C2)),
                                                            tri_Abox(Abe_rest,Lie,Lpt,Li0,Lu,Ls), 
                                                            concaten([(I,and(C1,C2))],Li0,Li1). 

    /*⊔ --> Lu*/
tri_Abox([(I,or(C1,C2))|Abe_rest],Lie,Lpt,Li,Lu1,Ls) :- concept(or(C1, C2)),
                                                        tri_Abox(Abe_rest,Lie,Lpt,Li,Lu0,Ls), 
                                                        concaten([(I,or(C1,C2))],Lu0,Lu1).

    /*Autre --> Ls*/
tri_Abox([(I,not(C))|Abe_rest],Lie,Lpt,Li,Lu,Ls1) :-    concept(not(C)),
                                                        tri_Abox(Abe_rest,Lie,Lpt,Li,Lu,Ls0),
                                                        concaten([(I,not(C))],Ls0,Ls1).
                                                        
tri_Abox([(I,C)|Abe_rest],Lie,Lpt,Li,Lu,Ls1) :- instance(I),
                                                concept(C),
                                                tri_Abox(Abe_rest,Lie,Lpt,Li,Lu,Ls0),
                                                concaten([(I,C)],Ls0,Ls1).

    /*Condition d'arret*/
tri_Abox([],[],[],[],[],[]).

/*Ajout d'un nouvelle assertion dans les listes  Lie, Lpt, Li, Lu ou Ls*/
    /*∃ --> Lie*/
evolue((I,some(R,C)),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt,Li,Lu,Ls) :-     concept(some(R, C)),
                                                                concaten([(I,some(R,C))],Lie,Lie1).

    /*∀ --> Lpt*/
evolue((I,all(R,C)),Lie,Lpt,Li,Lu,Ls,Lie,Lpt1,Li,Lu,Ls) :-  instance(I),
                                                            concept(all(R, C)),
                                                            concaten([(I,all(R,C))],Lpt,Lpt1). 

    /*⊓ --> Li*/
evolue((I,and(C1,C2)),Lie,Lpt,Li,Lu,Ls,Lie,Lpt,Li1,Lu,Ls) :-    instance(I),
                                                                concept(and(C1, C2)),
                                                                concaten([(I,and(C1,C2))],Li,Li1).

    /*⊔ --> Lu*/
evolue((I,or(C1,C2)),Lie,Lpt,Li,Lu,Ls,Lie,Lpt,Li,Lu1,Ls) :-     instance(I),
                                                                concept(or(C1, C2)),
                                                                concaten([(I,or(C1,C2))],Lu,Lu1).

    /*Autre --> Ls*/
evolue((I,not(C)),Lie,Lpt,Li,Lu,Ls,Lie,Lpt,Li,Lu,Ls1) :-    instance(I),
                                                            concept(not(C)),
                                                            concaten([(I,not(C))],Ls,Ls1).
evolue((I,C),Lie,Lpt,Li,Lu,Ls,Lie,Lpt,Li,Lu,Ls1):-  instance(I),
                                                    concept(C),
                                                    concaten([(I,C)],Ls,Ls1).

/*Predicats d'affichage*/
    /*Evolution Abox*/
affiche_evolution_Abox(Ls0, Lie0, Lpt0, Li0, Lu0, Abr0, Ls1, Lie1, Lpt1, Li1, Lu1, Abr1) :- write("before"),
                                                                                            nl,
                                                                                            write("Assertions de concept"),
                                                                                            nl,
                                                                                            affiche_liste(Ls0),
                                                                                            affiche_liste(Lie0),
                                                                                            affiche_liste(Lpt0),
                                                                                            affiche_liste(Li0),
                                                                                            affiche_liste(Lu0),
                                                                                            write("Assertions de roles"),
                                                                                            nl,
                                                                                            affiche_listeAbr(Abr0),
                                                                                            nl,
                                                                                            write("after"),
                                                                                            nl,
                                                                                            write("Assertions de concept"),
                                                                                            nl,
                                                                                            affiche_liste(Ls1),
                                                                                            affiche_liste(Lie1),
                                                                                            affiche_liste(Lpt1),
                                                                                            affiche_liste(Li1),
                                                                                            affiche_liste(Lu1),
                                                                                            write("Assertions de roles"),
                                                                                            nl,
                                                                                            affiche_listeAbr(Abr1),
                                                                                            nl.

    /*liste*/
affiche_liste([]).
affiche_liste([(I , F)| Reste]) :-  write(I),
                                    write(" : "),
                                    affiche_formule(F),
                                    nl,
                                    affiche_liste(Reste).

    /*Abr*/
affiche_listeAbr([]).
affiche_listeAbr([(A , B , R)| Reste]) :-   write("<"),
                                            write(A),
                                            write(","),
                                            write(B),
                                            write("> : "),
                                            write(R),
                                            nl,
                                            affiche_listeAbr(Reste).

    /*Formule*/
affiche_formule(F) :-   setof(C, cnamena(C),L), 
                        member(F,L),
                        write(F).

affiche_formule(F) :-   setof(C, cnamea(C),L), 
                        member(F,L),
                        write(F).

affiche_formule(or(F0,F1)) :-   write("(") , 
                                affiche_formule(F0) , 
                                write(") ⊔ (") , 
                                affiche_formule(F1), 
                                write(")").

affiche_formule(and(F0,F1)) :-  write("(") , 
                                affiche_formule(F0) , 
                                write(") ⊓ (") , 
                                affiche_formule(F1), 
                                write(")").

affiche_formule(all(R,F)) :-    write("∀."),
                                write(R) , 
                                write("(") , 
                                affiche_formule(F),
                                write(")").

affiche_formule(some(R,F)) :-   write("∃."),
                                write(R) , 
                                write("(") , 
                                affiche_formule(F),
                                write(")").

affiche_formule(not(F)) :-  write(" ¬"),
                            affiche_formule(F).

/*Predicats de la boucle de controle*/
    /*Resolution (verification s'il y a feuille ouverte)*/
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- complete_some(Lie,Lpt,Li,Lu,Ls,Abr),
                                    transformation_and(Lie,Lpt,Li,Lu,Ls,Abr),
                                    deduction_all(Lie,Lpt,Li,Lu,Ls,Abr),
                                    transformation_or(Lie,Lpt,Li,Lu,Ls,Abr).

    /*∃*/
complete_some([],_,_,_,_,_).
complete_some([(I,some(R,C))|Lie0_reste],Lpt0,Li0,Lu0,Ls0,Abr0):-   genereR(N),
                                                                    evolue((N,C), Lie0_reste, Lpt0, Li0, Lu0, Ls0, Lie1, Lpt1, Li1, Lu1, Ls1),
                                                                    concaten([(I,N,R)],Abr,Abr1),
                                                                    affiche_evolution_Abox(Ls0, Lie0_reste, Lpt0, Li0, Lu0, Abr0, Ls1, Lie1, Lpt1, Li1, Lu1, Abr1),
                                                                    resolution(Lie1, Lpt1 ,Li1 ,Lu1 ,Ls1 ,Abr1).

    /*⊓*/
transformation_and(_,_,[],_,_,_).
transformation_and(Lie0;Lpt0,[(I,and(C1,C2))|Li0_reste],Lu0,Ls0,Abr0):- evolue((I,C1), Lie0, Lpt0, Li0_reste, Lu0, Ls0, Lie1, Lpt1, Li1, Lu1, Ls1),
                                                                        evolue((I,C2), Lie0, Lpt0, Li0_reste, Lu0, Ls0, Lie1, Lpt1, Li1, Lu1, Ls1),
                                                                        affiche_evolution_Abox(Ls0, Lie0, Lpt0, Li0_reste, Lu0, Abr0, Ls1, Lie1, Lpt1, Li1, Lu1, Abr1),
                                                                        resolution(Lie1, Lpt1 ,Li1 ,Lu1 ,Ls1 ,Abr1).
    /*∀*/
deduction_all(_,[],_,_,_,_).
deduction_all(Lie0,[(I,all(R,C))|Lpt0_reste],Li0,Lu0,Ls0, Abr0) :-  member((I,X,R),Abr0),
                                                                    evolue((X,C), Lie0, Lpt0_reste, Li0, Lu0, Ls0, Lie1, Lpt1, Li1, Lu1, Ls1),
                                                                    affiche_evolution_Abox(Ls0, Lie0, Lpt0_reste, Li0, Lu0, Abr0, Ls1, Lie1, Lpt1, Li1, Lu1, Abr1),
                                                                    resolution(Lie1, Lpt1, Li1, Lu1, Ls1, Abr1).
    /*⊔*/
transformation_or(_,_,_,[],_,_).
transformation_or(Lie0 ,Lpt0 ,Li0 ,[(I,or(C1,C2))|Lu0_reste], Ls0, Abr0) :-  evolue((I,C1), Lie0, Lpt0, Li0, Lu0_reste, Ls0, Lie1, Lpt1, Li1, Lu1, Ls1),
                                                                            evolue((I,C2), Lie0, Lpt0, Li0, Lu0_reste, Ls0, Lie1, Lpt1, Li1, Lu1, Ls1),
                                                                            affiche_evolution_Abox(Ls0, Lie0, Lpt0, Li0, Lu0_reste, Abr0, Ls1, Lie1, Lpt1, Li1, Lu1, Abr1),
                                                                            resolution(Lie1, Lpt1, Li1, Lu1, Ls1, Abr1).


                                                                            /*main*/
programme :- 

 premiere_etape(Tbox,Abi,Abr),
 deuxieme_etape(Abi,Abi1,Tbox),
 troisieme_etape(Abi1,Abr),!.