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