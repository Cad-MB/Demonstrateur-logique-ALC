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
