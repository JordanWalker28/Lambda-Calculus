exception runtime_error;

val vx = (ID "x");
val vy = (ID "y");
val vz = (ID "z");
val t1 = (LAM("x",vx));
val t2 = (LAM("y",vx));
val t3 = (APP(APP(t1,t2),vz));
val t4 = (APP(t1,vz));
val t5 = (APP(t3,t3));
val t6 = (LAM("x",(LAM("y",(LAM("z", (APP(APP(vx,vz),(APP(vy,vz))))))))));
val t7 = (APP(APP(t6,t1),t1));
val t8 = (LAM("z", (APP(vz,(APP(t1,vz))))));
val t9 = (APP(t8,t3));

(*M'*)
datatype IEXP = IAPP of IEXP * IEXP | ILAM of string * IEXP | IID of string;

fun printIEXP (IID v) = print v |
printIEXP (ILAM (v,e)) = (
print "[";
print v;
print "]";
printIEXP e
)|
printIEXP (IAPP(e1,e2)) =
(print "<";
printIEXP e1;
print ">";
printIEXP e2
);

val Ivx=(IID "x");
val Ivy=(IID "y");
val Ivz=(IID "z");
val It1=(ILAM("x",Ivx));
val It2=(ILAM("y",Ivx));
val It3=(IAPP(Ivz,IAPP(It2,It1)));
val It4=(IAPP(Ivz,It1));
val It5=(IAPP(It3,It3));
val It6=(ILAM("x",(ILAM("y",(ILAM("z",(IAPP(IAPP(Ivz,Ivy),(IAPP(Ivz,Ivx))))))))));
val It7=(IAPP(It1,IAPP(It1,It6)));
val It8=(ILAM("z",(IAPP(IAPP(Ivz,It1),Ivz))));
val It9=(IAPP(It3,It8));

(* w *)
datatype BEXP = BAPP of BEXP * BEXP | BLAM of BEXP | BID of int;

fun printBEXP(BID v)= print (Int.toString v) |
printBEXP(BLAM(e))= (
print "\\";
printBEXP e;
print " "
)|
printBEXP(BAPP(e1,e2))=
(print "(";
printBEXP e1;
print " ";
printBEXP e2;
print ")"
);

val Bv1= (BID 1);
val Bv2= (BID 2);
val Bv3= (BID 3);
val Bt1= (BLAM(Bv1));
val Bt2= (BLAM(Bv2));
val Bt3= (BAPP(BAPP(Bt1,Bt2),Bv3));
val Bt4=(BAPP(Bt1,Bv3));
val Bt5=(BAPP(Bt3,Bt3));
val Bt6=(BLAM(BLAM(BLAM(BAPP(BAPP(Bv3,Bv1),(BAPP(Bv2,Bv1)))))));
val Bt7=(BAPP(BAPP(Bt6,Bt1),Bt1));
val Bt8=(BLAM(BAPP(Bv1,(BAPP(Bt1,Bv1)))));
val Bt9=(BAPP(Bt8,Bt3));

(* w' *)
datatype IBEXP = IBAPP of IBEXP * IBEXP | IBLAM of IBEXP | IBID of int;

fun printIBEXP (IBID v) = print (Int.toString(v)) | printIBEXP (IBLAM(e)) = (print "["; print "]"; printIBEXP e)|
printIBEXP (IBAPP(e1,e2)) =
(print "<"; printIBEXP e1; print ">"; printIBEXP e2);

val IBv1= (IBID 1);
val IBv2= (IBID 2);
val IBv3= (IBID 3);
val IBt1=(IBLAM(IBv1));
val IBt2=(IBLAM(IBv2));
val IBt3=(IBAPP(IBv3,IBAPP(IBt2,IBt1)));
val IBt4=(IBAPP(IBv3,IBt1));
val IBt5=(IBAPP(IBt3,IBt3));
val IBt6=(IBLAM(IBLAM(IBLAM(IBAPP(IBAPP(IBv1,IBv2),(IBAPP(IBv1,IBv3)))))));
val IBt7=(IBAPP(IBt1,IBAPP(IBt1,IBt6)));
val IBt8=(IBLAM(IBAPP(IBAPP(IBv1,IBt1),IBv1)));
val IBt9=(IBAPP(IBt3,IBt8));



val et1 = (LAM("x",APP(ID "y",ID "x")));
val et2 = (APP(et1,et1));
val et3 = (APP(et2,et2));
val et4 = (LAM("x",APP(et1,et1)));
val et5 = (APP(t1,et1));

(*M''*)
datatype COM = CAPP of COM*COM | CID of string | CI | CK | CS;
val Cvx= (CID "x");
val Cvy= (CID "y");
val Cvz= (CID "z");
val Ct1= (CI);
val Ct2= (CAPP(CK,Cvx));
val Ct3= (CAPP(CAPP(Ct1,Ct2),Cvz));
val Ct4=(CAPP(Ct1,Cvz));
val Ct5=(CAPP(Ct3,Ct3));
val Ct6= (CS);
val Ct7 = (CAPP(CAPP(Ct6,Ct1),Ct1));
val Ct8 = (CAPP(CAPP(CS,CI),CI));
val Ct9 = (CAPP(Ct8, Ct3));

fun printCOM (CID v)= print v | printCOM(CI)=print "I''"|
printCOM(CK)=print "K''"|
printCOM(CS)=print "S''"|
printCOM(CAPP (e1,e2))=
(print "(";
printCOM e1;
print " ";
printCOM e2;
print ")"
);

(* necessary for all translations *)

fun cfree id1 (CID id2) = if (id1 = id2) then true else false |
    cfree id1 (CAPP(e1,e2)) = (cfree id1 e1) orelse (cfree id1 e2) |
    cfree id1 (CI) = false |
    cfree id1 (CK) = false |
    cfree id1 (CS) = false ;

fun cfunf id (CID id1) =
          if id = id1 then CI
          else CAPP(CK,(CID id1)) |
    cfunf id(CAPP(e1,e2))=
          if not(cfree id (CAPP(e1,e2)))
          then CAPP(CK,CAPP(e1,e2))
          else
          if((CID id) = e2) andalso not (cfree id e1)
          then e1
          else CAPP(CAPP(CS,(cfunf id e1)),(cfunf id e2)) |
    cfunf id (_) = raise runtime_error;

(* U : M->M'' *)
fun toC (ID id) = (CID id)
|   toC (LAM(id,e)) = cfunf id (toC e)
|   toC(APP(e1,e2)) = CAPP(toC e1, toC e2);

(* T : M'->M'' *)
fun tooC (IID id) = (CID id)
|   tooC (ILAM(id,e)) = cfunf id (tooC e)
|   tooC (IAPP(e1,e2)) = CAPP(tooC e2, tooC e1);

(*  V : M->M'  *)
    fun Itran (ID id) = (IID id)
    |   Itran (APP(e1,e2)) = (IAPP((Itran e2),(Itran e1)))
    |   Itran (LAM(id,e)) = (ILAM (id,(Itran e)));

(*  subterms for M'' Q7 *)
fun subterms(CID id)=[CID id]
|   subterms(CK)=[CK]
|   subterms(CI)=[CI]
|   subterms(CS)=[CS]
|   subterms(CAPP(e1,e2))=  [CAPP(e1,e2)] @ (subterms e1) @ (subterms e2);



(* beta reduction in M'' *)
fun iscredex(CAPP(CI,_))=true
|   iscredex(CAPP(CAPP(CK,_),_))=true
|   iscredex(CAPP(CAPP(CAPP(CS,_),_),_))=true
|   iscredex(_)=false;

fun has_credex (CID id) = false
|   has_credex (CK)= false
|   has_credex (CI)= false
|   has_credex (CS)= false
|   has_credex (CAPP(e1,e2)) = if (iscredex  (CAPP(e1,e2))) then true else
                                ((has_credex e1) orelse (has_credex e2));

fun cred(CAPP(CI,e1))= e1
|   cred(CAPP(CAPP(CK,e1),e2)) = e1
|   cred(CAPP(CAPP(CAPP(CS,e1),e2),e3)) = (CAPP(CAPP(e1,e3),CAPP(e2,e3)))
|   cred(_) = raise runtime_error;

fun one_creduce (CID id) = (CID id)
|   one_creduce (CAPP(e1,e2)) = if (iscredex (CAPP(e1,e2))) then (cred (CAPP(e1,e2))) else
                                if (has_credex e1) then CAPP(one_creduce e1, e2) else
                                if (has_credex e2) then CAPP(e1, (one_creduce e2)) else (CAPP(e1,e2))
|   one_creduce (_) = raise runtime_error;

fun Creduce(CID id)= [(CID id)]
|   Creduce(CK)=[(CK)]
|   Creduce(CI)=[(CI)]
|   Creduce(CS)=[(CS)]
|   Creduce (CAPP(e1,e2)) = (let val l1 = if (iscredex (CAPP(e1,e2))) then  (Creduce (cred (CAPP(e1,e2)))) else
            if (has_credex e1) then (Creduce (CAPP(one_creduce e1, e2))) else
            if (has_credex e2) then  (Creduce (CAPP(e1, (one_creduce e2)))) else []
            in [CAPP(e1,e2)]@l1
            end);

fun printlistcreduce [] = ()
|   printlistcreduce (e::[]) = (printCOM e)
|   printlistcreduce (e::l) = (printCOM e; print "-->\n" ; (printlistcreduce l));

(* functions to print the steps *)

fun printSteps(e)= print (Int.toString((length e)-1));

fun printcreduce e = (let val tmp =  (Creduce e)
                      in (printlistcreduce tmp; print "\nNumber Of Steps: ";printSteps tmp;print"\n") end);

(* eta reduction in M *)

fun free id1 (ID id2) = if (id1 = id2) then  true else false|
    free id1 (APP(e1,e2))= (free id1 e1) orelse (free id1 e2) | 
    free id1 (LAM(id2, e1)) = if (id1 = id2) then false else (free id1 e1);


fun is_eta_redex (LAM(id,(APP( e1, e2)))) =
    if free id e1 then false else (if (ID id) =  e2 then true else false)
|   is_eta_redex _ = false;


fun has_eta_redex (ID id) = false |
    has_eta_redex(APP(e1,e2)) =  (has_eta_redex e1) orelse (has_eta_redex e2) |
    has_eta_redex (LAM(id,e)) = if (is_eta_redex(LAM(id,e))) then true else (has_eta_redex e) ;

fun ered (LAM(id,(APP(e1,e2)))) = e1 |
    ered (_) = raise runtime_error;

fun one_eta_reduce (ID id) = (ID id)|
    one_eta_reduce (LAM(id,e)) = if (is_eta_redex (LAM(id,e))) then (ered (LAM(id,e))) else LAM(id, (one_eta_reduce e))|
    one_eta_reduce (APP(e1,e2)) =  if (has_eta_redex e1) then APP(one_eta_reduce e1, e2) else
    if (has_eta_redex e2) then APP(e1, (one_eta_reduce e2)) else (APP(e1,e2));

fun etareduce (ID id) =  [(ID id)] |
    etareduce (LAM(id,e)) = (let val l1 = if (is_eta_redex (LAM(id,e))) then  etareduce (ered (LAM(id,e))) else
				 if (has_eta_redex e) then (etareduce (LAM(id, (one_eta_reduce e)))) else []
				 in [(LAM(id,e))]@l1
			      end) |
    etareduce (APP(e1,e2)) = (let val l1 =  if (has_eta_redex e1) then (etareduce (APP(one_eta_reduce e1, e2))) else
				 if (has_eta_redex e2) then  (etareduce (APP(e1, (one_eta_reduce e2)))) else []
				 in [APP(e1,e2)]@l1
			      end);

fun printlistreduce [] = ()|
    printlistreduce (e::[]) = (printLEXP e) |
    printlistreduce (e::l) = (printLEXP e; print "-->\n" ; (printlistreduce l));			      
			      
fun print_eta_reduce e = (let val tmp =  (etareduce e)
    in printlistreduce tmp end);


(* Omegas *)
val oLEXP = (LAM("x",APP(ID "x", ID"x")));
val oIEXP = (ILAM("x",(IAPP(Ivx, Ivx))));
val oBEXP =(BLAM(BAPP(Bv1, Bv1)));
val oIBEXP = (IBLAM(IBAPP(IBv1, IBv1)));
val oCom =(CAPP(CAPP(CS, CI),(CI)));

val omegaLEXP = (APP(oLEXP, oLEXP));
val omegaIEXP = (IAPP(oIEXP, oIEXP));
val omegaBEXP =(BAPP(oBEXP, oBEXP));
val omegaIBEXP = (IBAPP (oIBEXP, oIBEXP));
val omegaCom = (CAPP(oCom, oCom));

val Et1 = (LAM("x",APP(ID "y",ID "x")));
val Et2 = (APP(et1,et1));
val Et3 = (APP(et2,et2));
val Et4 = (LAM("x",APP(et1,et1)));
val Et5 = (APP(t1,et1));
val Et6 = (LAM("x",APP(vx, vx)));
val Et7 = (LAM("y",APP((LAM("x",APP((LAM("z",ID "z")),ID "x"))),ID "y")));

(*Right Reduce *) 

fun one_rightreduce (ID id) = (ID id)
|   one_rightreduce (LAM(id,e)) = LAM(id, (one_rightreduce e))
|   one_rightreduce (APP(e1,e2)) =  if (has_redex e2) then APP(e1, (one_rightreduce e2)) else
                                 if (is_redex (APP(e1,e2))) then (red (APP(e1,e2))) else
                                 if (has_redex e1) then APP(one_rightreduce e1, e2)
                                 else (APP(e1,e2));


fun rightreduce (ID id) =  [(ID id)]
|   rightreduce (LAM(id,e)) = (addlam id (rightreduce e))
|   rightreduce (APP(e1,e2)) = (let val l1 = if (has_redex e2) then(rightreduce (APP(e1, (one_rightreduce e2)))) else
         if (is_redex (APP(e1,e2))) then  (rightreduce (red (APP(e1,e2)))) else
				 if (has_redex e1) then (rightreduce (APP(one_rightreduce e1, e2)))  else []
				 in [APP(e1,e2)]@l1
			      end);

fun printrightreduce e = (let val tmp =  (rightreduce e)
		      in printlistreduce tmp end);
		      
		      
val lr1 = (APP(t2,omegaLEXP));