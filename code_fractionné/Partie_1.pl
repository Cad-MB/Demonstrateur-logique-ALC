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