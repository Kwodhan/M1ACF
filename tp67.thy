theory tp67
imports Main  "~~/src/HOL/Library/Code_Target_Int" "~~/src/HOL/Library/Code_Char"
begin

(* Types des expressions, conditions et programmes (statement) *)
datatype expression= Constant int | Variable string | Sum expression expression | Sub expression expression

datatype condition= Eq expression expression

datatype statement= Seq statement statement | 
                    Aff string expression | 
                    Read string | 
                    Print expression | 
                    Exec expression | 
                    If condition statement statement |
                    Skip
(* Un exemple d'expression *)

(* expr1= (x-10) *)
definition "expr1= (Sub (Variable ''x'') (Constant 10))"

(* Des exemples de programmes *)

(* p1= exec(0) *)
definition "p1= Exec (Constant 0)"

(* p2= {
        print(10)
        exec(0+0)
       }
*)

definition "p2= (Seq (Print (Constant 10)) (Exec (Sum (Constant 0) (Constant 0))))"

(* p3= {
         x:=0
         exec(x)
       }
*)

definition "p3= (Seq (Aff ''x'' (Constant 0)) (Exec (Variable ''x'')))"

(* p4= {
         read(x)
         print(x+1)
       }
*)
definition "p4= (Seq (Read ''x'') (Print (Sum (Variable ''x'') (Constant 1))))"


(* Le type des evenements soit X: execute, soit P: print *)
datatype event= X int | P int

(* les flux de sortie, d'entree et les tables de symboles *)

type_synonym outchan= "event list"
definition "el1= [X 1, P 10, X 0, P 20]"                   (* Un exemple de flux de sortie *)

type_synonym inchan= "int list"           
definition "il1= [1,-2,10]"                                (* Un exemple de flux d'entree [1,-2,10]              *)

type_synonym symTable= "(string * int) list"
definition "(st1::symTable)= [(''x'',10),(''y'',12)]"      (* Un exemple de table de symbole *)


(* La fonction (partielle) de recherche dans une liste de couple, par exemple une table de symbole *)
datatype 'a option= None | Some 'a

fun assoc:: "'a \<Rightarrow> ('a * 'b) list \<Rightarrow> 'b option"
where
"assoc _ [] = None" |
"assoc x1 ((x,y)#xs)= (if x=x1 then Some(y) else (assoc x1 xs))"

fun change:: "('a * 'b) \<Rightarrow> ('a * 'b) list \<Rightarrow> ('a * 'b) list"
where
"change _ [] = []" |
"change (x1,val1) ((x,y)#xs)= (if x=x1 then ((x1,val1)#xs) else (x,y)#(change (x1,val1) xs))"


(* Exemples de recherche dans une table de symboles *)

value "assoc ''x'' st1"     (* quand la variable est dans la table st1 *)
value "assoc ''z'' st1"     (* quand la variable n'est pas dans la table st1 *)


(* Evaluation des expressions par rapport a une table de symboles *)
fun evalE:: "expression \<Rightarrow> symTable \<Rightarrow> int"
where
"evalE (Constant s) e = s" |
"evalE (Variable s) e= (case (assoc s e) of None \<Rightarrow> -1 | Some(y) \<Rightarrow> y)" |
"evalE (Sum e1 e2) e= ((evalE e1 e) + (evalE e2 e))" |
"evalE (Sub e1 e2) e= ((evalE e1 e) - (evalE e2 e))" 

(* Exemple d'évaluation d'expression *)

value "evalE expr1 st1"

(* Evaluation des conditions par rapport a une table de symboles *)
fun evalC:: "condition \<Rightarrow> symTable \<Rightarrow> bool"
where
"evalC (Eq e1 e2) t= ((evalE e1 t) = (evalE e2 t))"


value "evalC (Eq (Variable ''x'') (Constant 10)) st1"

(* Evaluation d'un programme par rapport a une table des symboles, a un flux d'entree et un flux de sortie. 
   Rend un triplet: nouvelle table des symboles, nouveaux flux d'entree et sortie *)
fun evalS:: "statement \<Rightarrow> (symTable * inchan * outchan) \<Rightarrow> (symTable * inchan * outchan)"
where
"evalS Skip x=x" |
"evalS (Aff s e)  (t,inch,outch)=  (((s,(evalE e t))#t),inch,outch)" |
"evalS (If c s1 s2)  (t,inch,outch)=  (if (evalC c t) then (evalS s1 (t,inch,outch)) else (evalS s2 (t,inch,outch)))" |
"evalS (Seq s1 s2) (t,inch,outch)= 
    (let (t2,inch2,outch2)= (evalS s1 (t,inch,outch)) in
        evalS s2 (t2,inch2,outch2))" |
"evalS (Read _) (t,[],outch)= (t,[],outch)" |
"evalS (Read s) (t,(x#xs),outch)= (((s,x)#t),xs,outch)" |
"evalS (Print e) (t,inch,outch)= (t,inch,((P (evalE e t))#outch))" |
"evalS (Exec e) (t,inch,outch)= 
  (let res= evalE e t in
   (t,inch,((X res)#outch)))"



(* Exemples d'évaluation de programmes *)
(* Les programmes p1, p2, p3, p4 ont été définis plus haut *)
(* p1= exec(0) *)

value "evalS p1 (st1,il1,el1)" (* bad *)

(* ------------------------------------ *)
(* p2= {
        print(10)
        exec(0+0)
       }
*)

value "evalS p2 ([],[],[])" (* bad *)

(* ------------------------------------ *)
(* p3= {
         x:=0
         exec(x)
       }
*)

value "evalS p3 ([],[],[])" (* bad *)

(* ------------------------------------ *)
(* p4= {
         read(x)
         print(x+1)
       }
*)

value "evalS p4 ([],[10],[])"


definition "bad1= (Exec (Constant 0))"
definition "bad2= (Exec (Sub (Constant 2) (Constant 2)))"
definition "bad3= (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Variable ''x'')) (Exec (Sub (Variable ''x'') (Constant 1)))))"
definition "bad4= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) Skip (Aff ''y'' (Constant 1))) (Exec (Sum (Variable ''y'') (Constant 1)))))" (*demande*)
definition "bad5= (Seq (Read ''x'') (Seq (Aff ''y'' (Sum (Variable ''x'') (Constant 2))) (Seq (If (Eq (Variable ''x'') (Sub (Constant 0) (Constant 1))) (Seq (Aff ''x'' (Sum (Variable ''x'') (Constant 2))) (Aff ''y'' (Sub (Variable ''y'') (Variable ''x'')))) (Seq (Aff ''x'' (Sub (Variable ''x'') (Constant 2))) (Aff ''y'' (Sub (Variable ''y'') (Variable ''x''))))) (Exec (Variable ''y'')))))"
definition "bad6= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 1)) (Aff ''z'' (Constant 0))) (Exec (Variable ''z''))))"
definition "bad7= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 0)) (Aff ''z'' (Constant 1))) (Exec (Variable ''z''))))"
definition "bad8= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Variable ''x'') (Variable ''y'')) (Exec (Constant 1)) (Exec (Constant 0)))))"
definition "ok0= (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''y'') (Seq (If (Eq (Variable ''y'') (Constant 0)) (Seq (Print (Sum (Variable ''y'') (Variable ''x'')))
(Print (Variable ''x''))
) (Print (Variable ''y''))
) (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Variable ''x''))
 (Seq (Aff ''x'' (Constant 2)) (Seq (Print (Variable ''x''))
 (Seq (Aff ''x'' (Constant 3)) (Seq (Print (Variable ''x''))
 (Seq (Read ''y'') (Seq (If (Eq (Variable ''y'') (Constant 0)) (Aff ''z'' (Sum (Variable ''x'') (Variable ''x''))) (Aff ''z'' (Sub (Variable ''x'') (Variable ''y'')))) (Print (Variable ''z''))
)))))))))))"
definition "ok1= (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Sum (Variable ''x'') (Variable ''x'')))
 (Seq (Exec (Constant 10)) (Seq (Read ''y'') (If (Eq (Variable ''y'') (Constant 0)) (Exec (Constant 1)) (Exec (Constant 2)))))))"
definition "ok2= (Exec (Variable ''y''))"
definition "ok3= (Seq (Read ''x'') (Exec (Sum (Variable ''y'') (Constant 2))))"
definition "ok4= (Seq (Aff ''x'' (Constant 0)) (Seq (Aff ''x'' (Sum (Variable ''x'') (Constant 20))) (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 0)) (Aff ''z'' (Constant 4))) (Seq (Exec (Variable ''z'')) (Exec (Variable ''x''))))))"
definition "ok5= (Seq (Read ''x'') (Seq (Aff ''x'' (Constant 4)) (Exec (Variable ''x''))))"
definition "ok6= (Seq (If (Eq (Constant 1) (Constant 2)) (Aff ''x'' (Constant 0)) (Aff ''x'' (Constant 1))) (Exec (Variable ''x'')))"
definition "ok7= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Constant 1)) (If (Eq (Variable ''x'') (Constant 4)) (Aff ''x'' (Constant 1)) (Aff ''x'' (Constant 1)))) (Exec (Variable ''x''))))"
definition "ok8= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Constant 1)) (Aff ''x'' (Constant 2))) (Exec (Sub (Variable ''x'') (Constant 3)))))"
definition "ok9= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Constant 0)) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Sum (Variable ''y'') (Sum (Variable ''y'') (Variable ''x''))))))))"
definition "ok10= (Seq (Read ''x'') (If (Eq (Variable ''x'') (Constant 0)) (Exec (Constant 1)) (Exec (Variable ''x''))))"
definition "ok11= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Sum (Variable ''x'') (Constant 1))) Skip) (Exec (Variable ''x''))))"
definition "ok12= (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''z'') (If (Eq (Variable ''z'') (Constant 0)) (Exec (Variable ''y'')) (Exec (Variable ''z'')))))"
definition "ok13= (Seq (Aff ''z'' (Constant 4)) (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''y'') (Seq (Aff ''x'' (Sum (Variable ''x'') (Sum (Variable ''z'') (Variable ''x'')))) (Seq (Aff ''z'' (Sum (Variable ''z'') (Variable ''x''))) (Seq (If (Eq (Variable ''y'') (Constant 1)) (Aff ''x'' (Sub (Variable ''x'') (Variable ''y''))) Skip) (Seq (If (Eq (Variable ''y'') (Constant 0)) (Seq (Aff ''y'' (Sum (Variable ''y'') (Constant 1))) (Exec (Variable ''x''))) Skip) (Exec (Variable ''y'')))))))))"
definition "ok14= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Constant 0)) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Variable ''y''))))))"

definition "ok15= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Constant 0)) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Variable ''y''))))))"


(* Le TP commence ici! *)

fun BAD:: "(symTable * inchan * outchan ) \<Rightarrow> bool"
where
"BAD (t , inch , outch) = (List.member  outch (X 0))"

fun san1 :: "statement \<Rightarrow> bool"
where
 "san1 (Exec e) = False" 
|"san1 (If _ s1 s2)  =( (san1 s1) \<and> (san1 s2))"
|"san1 (Seq s1 s2) =( (san1 s1) \<and> (san1 s2)) "
|"san1 _ = True"

lemma "(san1 sta) \<longrightarrow> (\<forall> (inch::inchan). \<not>(BAD (evalS sta ([],inch,[]))))"
(*quickcheck [tester=narrowing,timeout=18000]*)
sorry



fun san2 :: "statement \<Rightarrow> bool"
where
 "san2 (Exec (Constant a))  =(if( ( a) = (0::int)) then False else True)" 
|"san2 (Exec e)  =False" 
|"san2 (If _ s1 s2)  =( (san2 s1) \<and> (san2 s2))"
|"san2 (Seq s1 s2) =( (san2 s1) \<and> (san2 s2)) "
|"san2 _ = True"

lemma "(san2 sta) \<longrightarrow> (\<forall> (inch::inchan). \<not>(BAD (evalS sta ([],inch,[]))))"
(*quickcheck [tester=narrowing,timeout=18000]*)
sorry


datatype absInt = Integer int|Any
datatype absCond = Ok|Ko|Unk 
type_synonym symTableAbs= "(string * absInt  ) list"

(*
Valeur X sur Rien \<longrightarrow> Valeur X
Valeur X sur Valeur Y \<longrightarrow>  Any
Valeur X sur Valeur X \<longrightarrow> Valeur X
Any sur Valeur X \<longrightarrow> Any
Valeur X sur Any \<longrightarrow> Any

Politique d'ajout des variables dans une sta lors d'une fusion de deux sta pour un if
*)
fun ajoutVarFusion:: "(string*absInt) \<Rightarrow> symTableAbs  \<Rightarrow> symTableAbs "
where
 "ajoutVarFusion (x,v) [] = [(x,v)]" 
|"ajoutVarFusion (x1,v1) ((x2,v2) # va) = (if(x1=x2) then (if( v2 = v1) then ((x2,v2)#va)else ((x2,Any)#va) ) else ( (x2,v2)#(ajoutVarFusion (x1,v1) va) ))"

lemma avf1:"\<exists> w.(assoc x  (ajoutVarFusion (x,c) stv)) = Some(w) "
apply (induct stv)
apply auto
done

lemma avf2:"(assoc x  (ajoutVarFusion (x,Any) stv)) = Some(Any) "
apply (induct stv)
apply auto
done

lemma avf3:"((assoc (x) stv) = Some(Integer v)) \<longrightarrow> ((assoc x  (ajoutVarFusion (x,(Integer v)) stv )) = Some(Integer v) )"
apply (induct stv)
apply auto
done

lemma avf4:"((assoc (x) stv) = Some(Integer v1)) \<and> (v1\<noteq>v2) \<longrightarrow> ((assoc x  (ajoutVarFusion (x,(Integer v2)) stv )) = Some(Any) )"
apply (induct stv)
apply auto
by (smt absInt.inject assoc.simps(2) tp67.option.inject)


(*  le sta2 demande à la sta1 ce qui lui manque*)
fun preFusionTable:: "symTableAbs \<Rightarrow> symTableAbs \<Rightarrow> symTableAbs"
where
"preFusionTable ((x1,v1)#xs) stv = (case (assoc x1 stv) of None \<Rightarrow> preFusionTable xs (ajoutVarFusion (x1,(Integer (-1))) stv) | Some(y) \<Rightarrow> preFusionTable xs stv )"|
"preFusionTable [] b = b"

lemma pft1:"\<exists> w.((assoc x stv1) = Some(w) \<or> (assoc x stv2) = Some(w))  \<longrightarrow> (assoc x (preFusionTable stv1 stv2) = Some(w)) \<and> ( assoc x (preFusionTable stv2 stv1) = Some(w))"
nitpick
sorry


lemma pft2:"((assoc x (stv1) = None) \<and> (assoc x (stv2) = Some(w) )) \<longrightarrow>assoc x (preFusionTable stv2 stv1) = Some(Integer (-1))  "
(*quickcheck[tester=narrowing,timeout=3600]*)
sorry

(* fusion les tables lors d'un if*)
fun fusionTable:: "symTableAbs \<Rightarrow> symTableAbs \<Rightarrow> symTableAbs"
where
"fusionTable ((x,e1)#xs) b =(ajoutVarFusion ( x,e1) (fusionTable (xs) b) )"|
"fusionTable [] b = b"


(* main prépare les sta avant de les fusionner lors d'un if*)
fun ifsymTableAbs ::"symTableAbs \<Rightarrow> symTableAbs \<Rightarrow> symTableAbs"
where
"ifsymTableAbs a b = fusionTable (preFusionTable a b ) (preFusionTable b a)" 

lemma "\<exists> w.(((assoc x stv1) = Some(w) \<or> (assoc x stv2) = Some(w))\<longrightarrow>  ((assoc x (ifsymTableAbs stv1 stv2)) = Some(w)) \<and>  ((assoc x (ifsymTableAbs stv2 stv1)) = Some(w))  ) "
nitpick
sorry

fun absPlus::" absInt \<Rightarrow> absInt \<Rightarrow> absInt"
where
 "absPlus Any _ = Any "
|"absPlus _ Any = Any "
|"absPlus (Integer i1) (Integer i2)  = (Integer (i1+i2))  "

fun absMoins::" absInt \<Rightarrow> absInt \<Rightarrow> absInt"
where
 "absMoins Any _ = Any "
|"absMoins _ Any = Any "
|"absMoins (Integer i1) (Integer i2)  = (Integer (i1-i2))  "


fun absExpression ::"expression \<Rightarrow> symTableAbs \<Rightarrow>  absInt"
where
 "absExpression (Constant i1) _ = (Integer (i1)) "
|"absExpression (Variable v) s = (case (assoc v s) of None \<Rightarrow> (Integer (-1)) | Some(y) \<Rightarrow> y)" 
|"absExpression (Sum v va) s =  (absPlus (absExpression v s) (absExpression va s))"
|"absExpression (Sub v va) s = (absMoins (absExpression v s) (absExpression va s))"

(* savoir si une condition peut etre verifier ou pas*)
fun absCondition ::"condition \<Rightarrow>symTableAbs \<Rightarrow> absCond"
where
 "absCondition (Eq x y) t = (if( ( (absExpression x t) = Any)  \<or>  ((absExpression y t) = Any)) then Unk else (if ((absExpression x t) = (absExpression y t)) then Ok else Ko)) "







fun san3 :: "statement \<Rightarrow> symTableAbs \<Rightarrow> (symTableAbs*bool)"
where
"san3 Skip t =(t, True)"
|"san3 (Seq s1 s2) t =( let (t1,bol) = (san3 s1 t) in (if(bol)then (san3 s2 t1) else (t1,False)) ) "
|"san3 (Aff v e) t =   ((v,(absExpression e t))#t,True) "
|"san3 (Print v) t = (t,True) "
|"san3 (Read s ) t =  ((s,Any)#t,True) "
|"san3 (If c s1 s2) t =(if((absCondition c t) = Unk) then (( let (t1,bol1) = (san3 s1 t) in (let (t2,bol2) = (san3 s2 t) in((ifsymTableAbs t1 t2,bol1 \<and> bol2) ))))else  (if((absCondition c t) = Ko) then (san3 s2 t) else (san3 s1 t)) )"
|"san3 (Exec e) t = (if(( (absExpression e t) = Integer 0) \<or> (absExpression e t) = Any) then (t,False) else  (t,True)) " 

fun san:: "statement \<Rightarrow> bool"
where
"san s= (let (_,b) = san3 s [] in b)"

lemma "(san sta) \<longrightarrow> (\<forall> inch. \<not>(BAD (evalS sta ([],inch,[]))))"
(*quickcheck [tester=narrowing,timeout=18000]*)(* ne sert à rien*)
sorry




(* ----- Restriction de l'export Scala (Isabelle 2014) -------*)
(* ! ! !  NE PAS MODIFIER ! ! ! *)
(* Suppression de l'export des abstract datatypes (Isabelle 2014) *)

code_reserved Scala
  expression condition statement 
code_printing
  type_constructor expression \<rightharpoonup> (Scala) "expression"
  | constant Constant \<rightharpoonup> (Scala) "Constant"
  | constant Variable \<rightharpoonup> (Scala) "Variable"
  | constant Sum \<rightharpoonup> (Scala) "Sum"
  | constant Sub \<rightharpoonup> (Scala) "Sub"  

  | type_constructor condition \<rightharpoonup> (Scala) "condition"
  | constant Eq \<rightharpoonup> (Scala) "Eq"

  | type_constructor statement \<rightharpoonup> (Scala) "statement"
  | constant Seq \<rightharpoonup> (Scala) "Seq"
  | constant Aff \<rightharpoonup> (Scala) "Aff"
  | constant Read \<rightharpoonup> (Scala) "Read"
  | constant Print \<rightharpoonup> (Scala) "Print"
  | constant Exec \<rightharpoonup> (Scala) "Exec"
  | constant If \<rightharpoonup> (Scala) "If"
  | constant Skip \<rightharpoonup> (Scala) "Skip"
  | code_module "" \<rightharpoonup> (Scala) 

{*// Code generated by Isabelle
package tp67

import utilities.Datatype._
// automatic conversion of utilities.Datatype.Int.int to Int.int
object AutomaticConversion{ 
	implicit def int2int(i:utilities.Datatype.Int.int):Int.int =
			i match {
			case utilities.Datatype.Int.int_of_integer(i)=>Int.int_of_integer(i)
	}
}
import AutomaticConversion._
*}


(* Directive pour l'exportation de l'analyseur *)
export_code san in Scala 
 file "/home/kwodhan/workspace/san.scala"   (* à adapter en fonction du chemin de votre projet TP67 *)



end
