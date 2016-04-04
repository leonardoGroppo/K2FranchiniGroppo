// Copyright (c) 2014-2015 K Team. All Rights Reserved.

require "builtins/string.k"
require "io/io.k"
require "builtins/list.k"

module IMP-SYNTAX

  syntax AExp  ::= Int | Id | String
                  	| AExp "/" AExp     [left, strict]
				  	| AExp "*" AExp		[left, strict]
                  	> AExp "+" AExp     [left, strict]
        			| AExp "-" AExp		[left, strict]
                  	| "(" AExp ")"      [bracket]

  syntax BExp  ::= Bool
                  | AExp "<=" AExp      [seqstrict, latex({#1}\leq{#2})]
				  | AExp ">=" AExp     	[seqstrict, latex({#1}\geq{#2})]
				  | AExp "==" AExp 		[strict]
                  | "!" BExp            [strict]
                  > BExp "&&" BExp      [left, strict(1)]
				  | BExp "||" BExp		[left, strict(1)]
				  | BExp "==" BExp 		[strict]
                  | "(" BExp ")"        [bracket]

  syntax Block ::= "{" "}"
                  | "{" Stmt "}"

  syntax Stmt  ::= Block
                  | AExp "=" AExp ";"                                                              	[strict(2)] 
                  | "int" Ids ";"
                  | "String" Ids ";"
                  | "if" "(" BExp ")" Block "else" Block                                           	[strict(1)]
                  | "while" "(" BExp ")" Block

				  | "INSPECT" AExp "TALLYING" Id "FOR ALL-CHARACTERS"                              	[strict(1)]
				  | "INSPECT" AExp "TALLYING" Id "FOR ALL" AExp                                    	[strict(1,3)]
				  | "INSPECT" Id "REPLACING ALL" AExp "BY" AExp                                    	[strict(2,3)]

				  | "STRING" Id "DELIMITED BY SIZE"  Id "DELIMITED BY SIZE INTO"  Id "END-STRING"   [strict]   
				  | "STRING" Id "DELIMITED BY SPACE" Id "DELIMITED BY SIZE INTO"  Id "END-STRING" 	[strict]
				  | "STRING" Id "DELIMITED BY SIZE"  Id "DELIMITED BY SPACE INTO" Id "END-STRING" 	[strict]
				  | "STRING" Id "DELIMITED BY SPACE" Id "DELIMITED BY SPACE INTO" Id "END-STRING" 	[strict]
				  															

                  | "UNSTRING" AExp "DELIMITED BY SPACE INTO" AExps
                    "END-UNSTRING" 																	[strict]
                  | "UNSTRING" AExp "DELIMITED BY SPACE INTO" AExp
                    "WITH POINTER" AExp 
                    "END-UNSTRING" 																	[strict]

                    //REGOLE INTERMEDIE


                    | "STRING" AExp Id 	 "INTO" Id "END-STRING" 						[strict(1)]
                    | "STRING" AExp AExp "INTO" Id "END-STRING" 						[strict(1,2)]

                    | "STRING" AExp "DELIMITED BY SPACE" Id "INTO" Id "END-STRING" 	[strict(2)]
                    | "STRING" Id AExp Id      "INTO" Id "END-STRING" 						[strict(2)]
                    | "STRING" Id AExp Id Id   "INTO" Id "END-STRING" 						[strict(2)]
                    | "STRING" Id AExp AExp Id "INTO" Id "END-STRING" 						[strict(2,3)]


                 > Stmt Stmt   [left]

  syntax Ids    ::= List{Id,","}			[seqstrict]
  syntax AExps  ::= List{AExp, ","}         [seqstrict]

endmodule


module IMP

  imports IMP-SYNTAX 

  syntax KResult ::= Int | Bool | String

  configuration
	<T>
		<k> $PGM:K </k>
		<env> .Map </env> 
		<store> .Map </store > 
    	<support> .Map </support> // cella contenente le variabili di supporto per la realizzazione della semantica
		<streams >
			<in stream="stdin"> .List </in>
			<out stream="stdout"> .List </out> 
		</streams>
	</T>

////////////////////////////////////////       ENV & STORE CELL DEFINITION         ////////////////////////////////

// lettura di variabile intera
  rule <k> X => I ...</k> 
  <env>... X |-> N ...</env> 
  <store>... N |-> I:Int ...</store>

// lettura di variabile string
  rule <k> X => S ...</k> 
  <env>... X |-> N ...</env> 
  <store>... N |-> S:String ...</store>

// int variable declaration
  rule <k> X = I:Int; => . ...</k>
  <env>... X |-> N ...</env>
  <store>... N |-> (_ => I) ...</store>

// string variable declaration
  rule <k> X = S:String; => . ...</k> 
  <env>... X |-> L ...</env>
  <store>... L |-> (_ => S) ...</store>

 // Pgm
 rule <k> int (X:Id, X1:Ids => X1); ...</k>
      <env> Rho:Map => Rho[X <- !N:Int] </env>
      <store>... .Map => !N |-> 0 ...</store>
  when notBool(X in keys(Rho))

 rule <k> String (X:Id, X1:Ids => X1); ...</k>
      <env> Rho:Map => Rho[X <- !N:Int] </env>
      <store>... .Map => !N |-> "" ...</store>
  when notBool(X in keys(Rho))

  rule int .Ids; => .K [structural]
  rule String .Ids; => .K [structural]

//////////////////////////////////////////////////      BASIC RULE       //////////////////////////////////

// AExp
  rule I1 / I2 => I1 /Int I2  when I2 =/=Int 0
  rule I1 * I2 => I1 *Int I2
  rule I1 + I2 => I1 +Int I2
  rule I1 - I2 => I1 -Int I2
  rule S1 + S2 => S1 +String S2
  
// BExp
  rule I1 <= I2 => I1 <=Int I2
  rule I1 >= I2 => I1 >=Int I2
  rule I1 == I2 => I1 ==Int I2
  rule S1 == S2 => S1 ==String S2
  rule ! T => notBool T
  rule true && B => B
  rule false && _ => false
  rule true || _ => true
  rule false || B => B
  rule true == true => true
  rule true == false => false
  rule false == false => true
  rule false == true => false
  
// Block
  rule {} => .   [structural]
  rule {S} => S  [structural]

// Stmt
  rule S1:Stmt S2:Stmt => S1 ~> S2    [structural]

  //conditions
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) { S while (B) S } else {}       [structural]


//////////////////////////////////     INSPECT	   ///////////////////////////////////////////////

	rule <k> INSPECT S1:String TALLYING I1:Id FOR ALL-CHARACTERS => .K ...</k>
	  	<env>... I1 |-> N ...</env>
	  	<store>... N |-> (_ => lengthString(S1)) ...</store>
	  
	rule <k> INSPECT S1:String TALLYING I1:Id FOR ALL S2:String => .K ...</k> 
	     <env> ... I1 |-> N ...</env>
	     <store> ... N |-> (_ => countAllOccurrences(S1,S2)) ...</store> when lengthString(S2) =Int 1

	  
	rule <k> INSPECT S1:Id REPLACING ALL S2:String BY S3:String => .K ...</k>
	    <env>... S1 |-> N ...</env>
	    <store>... N |-> (S => replaceAll(S,S2,S3) ) ...</store>
	   //replace all funziona già di suo con s2 s3 caratteri e non stringhe. Il when non serve



//////////////////////////////      CONCATENAMENTO       //////////////////////////////////

	// CASO SIZE SIZE 
	//FETCH VALORE PRIMA STRINGA
	// Vado in memoria, recupero il valore di S1 e lo passo alla regola semantica intermedia.
  	rule <k> STRING S1:Id DELIMITED BY SIZE S2:Id DELIMITED BY SIZE INTO S3:Id END-STRING => 
  		 	 STRING S1value:String S2:Id INTO S3:Id END-STRING ...</k>
      	<env>... S1 |-> N ...</env>
     	<store>... N |-> S1value ...</store>

    //FETCH VALORE SECONDA STRINGA 
    // Vado in memoria, recupero il valore di S2 e lo passo alla regola semantica finale. 
  	rule <k> STRING S1value:String S2:Id INTO S3:Id END-STRING => 
  			 STRING S1value:String S2value:String INTO S3:Id END-STRING ...</k>
 		<env>... S2 |-> N ...</env>
     	<store>... N |-> S2value ...</store>

    //CONCATENAMENTO DEI DUE VALORI
    // In S3 salvo il risultato dell'operazione (concatenamento di due stringhe)
    rule <k> STRING S1value:String S2value:String INTO S3:Id END-STRING => .K ...</k>
		<env>... S3 |-> N ...</env>
     	<store>... N |-> (_ => S1value +String S2value ) ...</store>



// CASO SPACE SIZE 
	//PRENDO VALORE S1
	// Vado in memoria, recupero il valore di S1 e lo passo alla regola semantica intermedia.
	rule <k> STRING S1:Id DELIMITED BY SPACE S2:Id DELIMITED BY SIZE INTO S3:Id END-STRING =>
			 STRING S1:Id S1value:String S2:Id INTO S3:Id END-STRING ...</k>
		<env>... S1 |-> N ...</env>
     	<store>... N |-> S1value ...</store>

    //CREO POS
    // Creo il puntatore che mi servirà per trovare il primo spazio
    rule <k> STRING S1:Id S1value:String S2:Id INTO S3:Id END-STRING =>
    		 STRING S1:Id S1value:String P:Id S2:Id INTO S3:Id END-STRING ...</k>
    	<env>... P |-> N ...</env> 
  		<store>... N |-> 0 ...</store>

	// CERCO POSIIONE PRIMO SPAZIO
	// Trovo la posizione del primo spazio e la passo alla regola intermedia successiva
	rule <k> STRING S1:Id S1value:String P:Id    S2:Id INTO S3:Id END-STRING => 
			 STRING S1:Id S1value:String Pos:Int S2:Id INTO S3:Id END-STRING ...</k>
	  	<env>... P |-> N ...</env>
	  	<store>... N |-> (Pos => findChar(S1value," ", Pos) ) ...</store>

	//CALCOLO VALORE PRIMA STRINGA, MI RICONDUCO A CASO SIZE SIZE
	// Sovrascrivo S1 con S1 meno tutti i caratteri successivi al primo spazio
  	rule <k> STRING S1:Id S1value:String Pos:Int S2:Id INTO S3:Id END-STRING => 
  			 STRING S1:Id DELIMITED BY SIZE S2:Id DELIMITED BY SIZE INTO S3:Id END-STRING ...</k>
      	<env>... S1 |-> N ...</env>
      	<store>... N |-> (_ => substrString(S1value,0, Pos) ) ...</store>


/*
  rule STRING S1:String DELIMITED BY Del1:String S2:String DELIMITED BY Del2:String INTO S3:String WITH POINTER I:Int END-STRING => 
    if( ( Del1 ==String "SPACE" || Del1 ==String "SIZE" ) && ( Del2 ==String "SPACE" || Del2 ==String "SIZE" ) )
      { if(Del1 ==String "SPACE") { findChar(S1," ", Pos) ~> S1 = substrString(S1,0,Pos) }
        if(Del2 ==String "SPACE") { findChar(S2," ",Pos) ~> S2 = substrString(S2,0,Pos) }
        S3 =String S1 +String S2 ~> I =Int lengthString(S3) }

  rule STRING S1:String DELIMITED BY Del1:String S2:String DELIMITED BY Del2:String INTO S3:String WITH POINTER I:Int ON OVERFLOW DISPLAY S4:String END-STRING => 
    if((Del1 ==String "SPACE" || Del1 ==String "SIZE") && (Del2 ==String "SPACE" || Del2 ==String "SIZE"))
      { if(Del1 ==String "SPACE") { findChar(S1," ",Pos) S1 =String substrString(S1,0,Pos) }
        if(Del2 ==String "SPACE") { findChar(S2," ",Pos) S2 =String substrString(S2,0,Pos) }
        S3length =String lengthString(S3) ~> S3 =String S1 +String S2 ~> I =String lengthString(S3) 
      }
    requires I >Int S3
        
  //UNSTRING
  rule UNSTRING S1:String DELIMITED BY SPACE INTO List END-UNSTRING =>

    StartPos =Int 0 ~> Index =Int 0 ~> 
  while( Index <Int size(List) ){
      //cerco la posizione dello spazio                  splitto                                    riaggiusto l'indice per cercare lo spazio successivo
      findChar(substrString(S1,StartPos,stringLength(S1))," ",EndPos) ~> List[i] =String substrString(S1,StartPos,EndPos) ~> StartPos =Int EndPos ~> i =Int i +Int 1
    }
*/  


endmodule