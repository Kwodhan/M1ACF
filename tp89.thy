theory tp89
imports Main (* "~~/src/HOL/Library/Code_Target_Nat" *)
begin



(* 
quickcheck_params [size=6,tester=narrowing,timeout=120]
nitpick_params [timeout=120]
*)

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
type_synonym transaction= "transid * nat"
(* transid * am m * am c * etat  *)

type_synonym ligneBdd = "(transid * SomeTrans *SomeTrans * etatTrans )"
type_synonym transBdd ="ligneBdd list"

fun updateLignePay :: "  nat \<Rightarrow> ligneBdd \<Rightarrow>  ligneBdd"
where
 "updateLignePay v1 ((x2::transid),m2,c2,Abort) =  ((x2::transid),m2,c2,Abort)"
|"updateLignePay v1 ((x2::transid),Integer m2,None,Encours) = (if (v1\<ge>m2) then  ((x2::transid),Integer m2, Integer v1,Ok) else  ((x2::transid),Integer m2,Integer v1,Encours) )"
|"updateLignePay v1 ((x2::transid),Integer m2,Integer v2,Encours) = (if (v1>v2) then  (if(v1\<ge>m2) then  ((x2::transid),Integer m2,Integer v1,Ok)  else  ((x2::transid),Integer m2,Integer v1,Encours)) else ( ((x2::transid),Integer m2,Integer v2,Encours)))"
|"updateLignePay v1 ((x2::transid),m2,c2,Ok) = ((x2::transid),m2,c2,Ok)"
|"updateLignePay v1 (v,None, None, Encours) =  (v,None, Integer v1, Encours)"
|"updateLignePay v1 (v,None, Integer v2, Encours) = (if (v1>v2) then (v,None, Integer v1, Encours)  else (v,None, Integer v2, Encours)) "

fun updatePay:: "(transid * nat) \<Rightarrow> transBdd \<Rightarrow>  transBdd"
where
 "updatePay ((x1::transid),c1) [] = [((x1::transid),None,Integer c1,Encours)] "
|"updatePay ((x1::transid),c1) (((x2::transid),m2,c2,e2)#xs)= (if (x2=x1) then (updateLignePay  (c1) ((x2::transid),m2,c2,e2)  )#xs  else (((x2::transid),m2,c2,e2)#(updatePay ((x1::transid),c1) xs ))  )"


fun updateLigneAck :: "nat \<Rightarrow> ligneBdd \<Rightarrow>  ligneBdd"
where
 "updateLigneAck m1 ((x2::transid),m2,c2,Abort) =  ((x2::transid),m2,c2,Abort)"
|"updateLigneAck m1 ((x2::transid),Integer m2,None,Encours) = (if (m1\<le>m2) then  ((x2::transid),Integer m1, None,Encours) else  ((x2::transid),Integer m2,None,Encours) )"
|"updateLigneAck m1 ((x2::transid),Integer m2,Integer v2,Encours) = (if (m1\<le>m2) then  (if(m1\<le>v2) then  ((x2::transid),Integer m1,Integer v2,Ok)  else  ((x2::transid),Integer m1,Integer v2,Encours)) else ( ((x2::transid),Integer m2,Integer v2,Encours)))"
|"updateLigneAck m1 ((x2::transid),m2,c2,Ok) = ((x2::transid),m2,c2,Ok)"
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
|"traiterMessage ( Ack transid am) tb = (if(am>0) then  updateAck (transid, am) tb else tb)"
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


lemma lem1:"( (List.member  (export  (traiterMessageList lm)) (a,b)) \<longrightarrow> (b>0))"
apply (induct lm)
apply auto
apply (simp add: member_rec(2))
nitpick[timeout=140]


definition "messagelist =[(Cancel ((0) ,0 ,0) ),(Cancel ((1) ,0 ,0) )]"

definition "message =(Cancel (0 ,0 ,0) )"

definition "bdd1=[((0, 0, 0), SomeTrans.None, SomeTrans.None, Encours), ((0, 0, 0), SomeTrans.None, Integer 0, Ok)]"

value "traiterMessageList messagelist"

lemma lem3:"(List.member (export (traiterMessage (Cancel  a) (traiterMessageList lm))) (a,b)) = False"
apply (induct lm)
apply auto
apply (simp add: member_rec(2))






lemma lem4:" (List.member (traiterMessage (message) bdd) ((a::transid),b,c,d) \<longrightarrow> (List.member bdd ((a::transid),b,c,Abort)  ))"
sorry

lemma lem81:" (List.member (traiterMessage (Ack a em ) bdd) ((a::transid),b,c,Ok) \<longrightarrow> (List.member bdd ((a::transid),b,c,Ok)  ))"
sorry

lemma lem82:" (List.member (traiterMessage (Pay a em) bdd) ((a::transid),b,c,Ok) \<longrightarrow> (List.member bdd ((a::transid),b,c,Ok)  ))"
sorry
(* ----- Exportation en Scala (Isabelle 2014) -------*)

(* Directive d'exportation *)
export_code export traiterMessage in Scala



end

