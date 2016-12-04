theory tp89
imports Main "~~/src/HOL/Library/Code_Target_Nat" 
begin





(*
transid
c identifie un client
m identifie un marchand
i numéro de transaction entre c et m

am transaction montant retenu pour la transaction

Client \<longrightarrow> Marchand
Pay (c,m,i) am \<longrightarrow> c accepte de payer le montant am à m pour la transaction id

Marchand \<longrightarrow> Client
Ack (c,m,i) am \<longrightarrow> m demande un montant am au client c pour la transaction id
Cancel (c,m,i) \<longrightarrow> m annule toutes les transactions pour transaction id 

le marchand doit diminuer am
le client doit augmenter am
*)
type_synonym transid= "nat*nat*nat"

datatype message= 
  Pay transid nat  
| Ack transid nat
| Cancel transid

datatype etatTrans=
  Encours
| Ok
| Abort

datatype SomeTrans =
  None
| Integer nat

datatype SomeEtat =
  Nothing
| Etat  etatTrans
type_synonym transaction= "transid * nat"


(* transid * am marchand * am client * etat  *)

type_synonym ligneBdd = "(transid * SomeTrans *SomeTrans * etatTrans )"

type_synonym transBdd ="ligneBdd list"

(* select dans la bdd, l'etat de la transi*)
fun selectEtat ::"transid \<Rightarrow> transBdd \<Rightarrow> SomeEtat "
where
 "selectEtat _ [] = Nothing"
|"selectEtat id1 ((id2::transid,sm2,sc2,etat2)#xs) =( if(id1=id2) then (Etat etat2)  else selectEtat id1 xs )"

(* select dans la bdd de la proposition du marchand*)
fun selectMarch ::"transid \<Rightarrow> transBdd \<Rightarrow> SomeTrans "
where
 "selectMarch _ [] = None"
|"selectMarch id1 ((id2::transid,sm2,sc2,etat2)#xs) =( if(id1=id2) then sm2  else selectMarch id1 xs )"

(* select dans la bdd de la proposition du client*)
fun selectClient ::"transid \<Rightarrow> transBdd \<Rightarrow> SomeTrans"
where
 "selectClient _ [] = None"
|"selectClient id1 ((id2::transid,sm2,sc2,etat2)#xs) =( if(id1=id2) then sc2  else selectClient id1 xs )"







fun updateLignePay :: "  nat \<Rightarrow> ligneBdd \<Rightarrow>  ligneBdd"
where
 "updateLignePay _ ((x2::transid),m2,c2,Abort) =  ((x2::transid),m2,c2,Abort)"
|"updateLignePay v1 ((x2::transid),Integer m2,None,Encours) = (if (v1\<ge>m2) then  ((x2::transid),Integer m2, Integer v1,Ok) else  ((x2::transid),Integer m2,Integer v1,Encours) )"
|"updateLignePay v1 ((x2::transid),Integer m2,Integer v2,Encours) = (if (v1>v2) then  (if(v1\<ge>m2) then  ((x2::transid),Integer m2,Integer v1,Ok)  else  ((x2::transid),Integer m2,Integer v1,Encours)) else ( ((x2::transid),Integer m2,Integer v2,Encours)))"
|"updateLignePay _ ((x2::transid),m2,c2,Ok) = ((x2::transid),m2,c2,Ok)"
|"updateLignePay v1 (v,None, None, Encours) =  (v,None, Integer v1, Encours)"
|"updateLignePay v1 (v,None, Integer v2, Encours) = (if (v1>v2) then (v,None, Integer v1, Encours)  else (v,None, Integer v2, Encours)) "

fun updatePay:: "(transid * nat) \<Rightarrow> transBdd \<Rightarrow>  transBdd"
where
 "updatePay ((x1::transid),c1) [] = [((x1::transid),None,Integer c1,Encours)] "
|"updatePay ((x1::transid),c1) (((x2::transid),m2,c2,e2)#xs)= (if (x2=x1) then (updateLignePay  (c1) ((x2::transid),m2,c2,e2)  )#xs  else (((x2::transid),m2,c2,e2)#(updatePay ((x1::transid),c1) xs ))  )"


fun updateLigneAck :: "nat \<Rightarrow> ligneBdd \<Rightarrow>  ligneBdd"
where
 "updateLigneAck _ ((x2::transid),m2,c2,Abort) =  ((x2::transid),m2,c2,Abort)"
|"updateLigneAck m1 ((x2::transid),Integer m2,None,Encours) = (if (m1\<le>m2) then  ((x2::transid),Integer m1, None,Encours) else  ((x2::transid),Integer m2,None,Encours) )"
|"updateLigneAck m1 ((x2::transid),Integer m2,Integer v2,Encours) = (if (m1\<le>m2) then  (if(m1\<le>v2) then  ((x2::transid),Integer m1,Integer v2,Ok)  else  ((x2::transid),Integer m1,Integer v2,Encours)) else ( ((x2::transid),Integer m2,Integer v2,Encours)))"
|"updateLigneAck _ ((x2::transid),m2,c2,Ok) = ((x2::transid),m2,c2,Ok)"
|"updateLigneAck m1 (v,None, None, Encours) =  (v,Integer m1,None, Encours)"
|"updateLigneAck m1 (v,None, Integer v2, Encours) = (if (m1\<le>v2) then (v,Integer m1, Integer v2, Ok)  else (v, Integer m1,Integer v2, Encours)) "

fun updateAck:: "(transid * nat) \<Rightarrow> transBdd \<Rightarrow>  transBdd"
where
 "updateAck ((x1::transid),c1) [] = [((x1::transid),Integer c1,None,Encours)] "
|"updateAck ((x1::transid),c1) (((x2::transid),m2,c2,e2)#xs)= (if (x2=x1) then (updateLigneAck  (c1) ((x2::transid),m2,c2,e2)  )#xs  else (((x2::transid),m2,c2,e2)#(updateAck ((x1::transid),c1) xs ))  )"

fun updateLigneCancel :: " ligneBdd \<Rightarrow>  ligneBdd"
where
 "updateLigneCancel  ((x2::transid),m2,c2,e2) =  ((x2::transid),m2,c2,Abort)"

fun updateCancel:: "transid \<Rightarrow> transBdd \<Rightarrow>  transBdd"
where
 "updateCancel (x1::transid) [] = [((x1::transid),None,None,Abort)] "
|"updateCancel (x1::transid) (((x2::transid),m2,c2,e2)#xs)= (if (x2=x1) then (updateLigneCancel  ((x2::transid),m2,c2,e2)  )#xs  else (((x2::transid),m2,c2,e2)#(updateCancel ((x1::transid)) xs ))  )"


fun traiterMessage ::"message \<Rightarrow> transBdd \<Rightarrow> transBdd "
where
 "traiterMessage ( Pay transid am) tb = (if(am>0) then updatePay (transid, am) tb else tb)" 
|"traiterMessage ( Ack transid am) tb = (if(am\<ge>0) then  updateAck (transid, am) tb else tb)"
|"traiterMessage ( Cancel transid) tb = updateCancel transid tb "

fun export:: "transBdd \<Rightarrow> transaction list"
where
 "export [] = []"
|"export  (((x2::transid),m2,Integer c2,e2)#xs) = (if (e2=Ok) then (x2,c2)#(export xs ) else(export xs ) )"
|"export  (((x2::transid),m2,c2,e2)#xs) = (export xs )"

fun traiMessList:: "message list \<Rightarrow> transBdd \<Rightarrow> transBdd"
where
 "traiMessList [] tb = tb"
|"traiMessList (v # va) tb =traiMessList va (traiterMessage v tb) "

fun traiterMessageList:: "message list \<Rightarrow> transBdd"
where
 "traiterMessageList ml = traiMessList ml []"



lemma lem1:"( (List.member  (export  (traiterMessageList lm)) (a,b)) \<longrightarrow> (b>0))"
apply (induct lm)
apply auto
apply (simp add: member_rec(2))
oops




lemma lem2:"List.distinct (exportid (export  (traiterMessageList lm))) " 
apply (induct lm)
apply auto

oops

lemma lem3:"(selectEtat a  (traiterMessage (Cancel  a) (traiterMessageList lm))) = Etat Abort"

apply (induct lm)
apply auto

oops

lemma lem4:"(List.member (export (traiterMessage (Cancel  a) (traiterMessageList lm))) (a,b)) = False"
apply (induct lm)
apply auto
apply (simp add: member_rec(2))

oops


lemma lem5:"pc\<ge>pm \<and> pc>0 \<and>  \<not>(List.member  lm (Cancel a )) \<longrightarrow> (\<exists> pc. List.member (export (traiterMessage (Pay a pc)  (traiterMessage (Ack  a pm) (traiterMessageList lm)))) (a,pc))"
apply (induct lm)
apply auto
apply (metis gr_implies_not0 member_rec(1))
apply (simp add: member_rec(1))

oops

lemma lem6:"(selectEtat a (traiterMessageList lm) = Etat Ok) \<longrightarrow>(\<exists> pc pm.(List.member lm (Ack a pm)) \<and> (List.member lm (Pay a pc)) \<and> pc \<ge> pm) "
apply (induct lm)
apply auto


oops

lemma lem71:"( selectClient a  (traiterMessageList lm)) = Integer pm \<and> pm> mo \<longrightarrow> ( selectClient a (traiterMessage (Pay  a mo)  (traiterMessageList lm))) = Integer pm "

oops


lemma lem72:"( selectMarch a  (traiterMessageList lm)) = Integer pm \<and> pm < mo \<longrightarrow> ( selectMarch a (traiterMessage (Ack  a mo) (traiterMessageList lm))) = Integer pm "

oops

lemma lem81:"(selectEtat a (traiterMessageList lm) = Etat Ok) \<and> (selectClient a (traiterMessage (Pay  a pm) (traiterMessageList lm)) = Integer pm) \<longrightarrow> (selectClient a (traiterMessage (Pay  a autre) (traiterMessageList lm)) = Integer pm)"

oops

lemma lem82:"(selectEtat a (traiterMessageList lm) = Etat Ok) \<and> (selectMarch a (traiterMessageList lm) = Integer pm) \<longrightarrow> (selectMarch a  (traiterMessage (Ack  a autre) (traiterMessageList lm)) = Integer pm)"

oops

lemma lem9:"(selectEtat a (traiterMessageList lm) = Etat Ok) \<and> (selectMarch a (traiterMessageList lm) = Integer pm) \<and>  (selectClient a  (traiterMessageList lm) = Integer pc) \<longrightarrow> (List.member (export (traiterMessageList lm)) (a,pc)) "
oops

(* ----- Exportation en Scala (Isabelle 2014) -------*)

(* Directive d'exportation *)
export_code export traiterMessage in Scala


end

