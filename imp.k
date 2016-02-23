// Copyright (c) 2014-2015 K Team. All Rights Reserved.
// AsciaugsCVW apkhdbvc 

require "builtins/string.k"
require "io/io.k"
require "builtins/list.k"

module IMP-SYNTAX

  syntax AExp  ::= Int | Id | String
                  | AExp "/" AExp              [left, strict]
				  | AExp "*" AExp			   [left, strict]
                  > AExp "+" AExp              [left, strict]
				  | AExp "-" AExp			   [left, strict]
                  | "(" AExp ")"               [bracket]

  syntax BExp  ::= Bool
                  | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
				  | AExp ">=" AExp             [seqstrict, latex({#1}\geq{#2})]
				  | AExp "==" AExp 			   [strict]
                  | "!" BExp                   [strict]
                  > BExp "&&" BExp             [left, strict(1)]
				  | BExp "||" BExp			   [left, strict(1)]
				  | BExp "==" BExp 			   [strict]
                  | "(" BExp ")"               [bracket]

  syntax Block ::= "{" "}"
                  | "{" Stmt "}"

  syntax Stmt  ::= Block
                  | Id "=" AExp ";"                                                                       [strict(2)] 
                  | "int" Ids ";"
                  | "if" "(" BExp ")"
                   Block "else" Block                                                                     [strict(1)]
                  | "while" "(" BExp ")" Block

        				  | "INSPECT" AExp "TALLYING" AExp "FOR ALL CHARACTERS"                                   [seqstrict]
        				  | "INSPECT" AExp "TALLYING" AExp "FOR ALL" AExp                                         [seqstrict]
        				  | "INSPECT" AExp "REPLACING ALL" AExp "BY" AExp                                         [seqstrict]

        				  | "STRING" AExp "DELIMITED BY" AExp " " AExp "DELIMITED BY" AExp "INTO" AExp "END-STRING" [strict]
        				  | "STRING" AExp "DELIMITED BY" AExp " " AExp "DELIMITED BY" AExp "INTO" AExp 
        				  	"WITH POINTER" AExp 
        				  	"END-STRING" [strict]
        				  | "STRING" AExp "DELIMITED BY" AExp " " AExp "DELIMITED BY" AExp "INTO" AExp 
        					  "WITH POINTER" AExp "ON OVERFLOW DISPLAY" AExp 
        					  "END-STRING" [strict]

                  | "UNSTRING" AExp "DELIMITED BY SPACE INTO" AExp //List
                    "END-UNSTRING" [strict]
                  | "UNSTRING" AExp "DELIMITED BY SPACE INTO" AExp
                    "WITH POINTER" AExp 
                    "END-UNSTRING" [strict]

                 > Stmt Stmt                                                                               [left]

  syntax Ids    ::= List{Id,","}																			[seqstrict]
  syntax AExps  ::= List{AExp, ","}                                                                      	[seqstrict]

endmodule


module IMP

  imports IMP-SYNTAX

  syntax KResult ::= Int | Bool | String

  configuration
	<T>
		<k> $PGM:K </k>
		<env> .Map </env> 
		<store> .Map </store > 
		<streams >
			<in stream="stdin"> .List </in>
			<out stream="stdout"> .List </out> 
		</streams>
	</T>


// AExp
  rule <k> X:Id => I ...</k> 
  <env>... X |-> N ...</env> 
  <store>... N |-> I ...</store>
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
  //variables declaration
  rule <k> X = I:Int; => . ...</k> 
  <env>... X |-> N ...</env>
  <store>... N |-> (_ => I) ...</store>
  
  rule S1:Stmt S2:Stmt => S1 ~> S2                                          [structural]

  //conditions
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) { S while (B) S } else {}                        [structural]

  //INSPECT 
  rule INSPECT S1:String TALLYING I1:Int FOR ALL CHARACTERS => I1 =Int lengthString(S1)
  rule INSPECT S1:String TALLYING I1:Int FOR ALL S2:String => I1 =Int countAllOccurrences(S1,S2) when lengthString(S2) ==Int 1
  rule INSPECT S1:String REPLACING ALL S2:String BY S3:String => replaceAll(S1,S2,S3) requires (lengthString(S2) ==Int 1) && (lengthString(S3) ==Int 1)

  //STRING 
  rule STRING S1:String DELIMITED BY Del1:String S2:String DELIMITED BY Del2:String INTO S3:String END-STRING => 
		if( ( Del1 ==String "SPACE" || Del1 ==String "SIZE" ) && ( Del2 ==String "SPACE" || Del2 ==String "SIZE" ) )
		    then 
				if(Del1 ==String "SPACE")findChar(S1," ",Pos) ~> S1 =String substrString(S1,0,Pos)
				if(Del2 ==String "SPACE")findChar(S2," ",Pos) ~> S2 =String substrString(S2,0,Pos)
				~> S3 =String S1 +String S2;

  rule STRING S1:String DELIMITED BY Del1:String S2:String DELIMITED BY Del2:String INTO S3:String WITH POINTER I:Int END-STRING => 
		if( ( Del1 ==String "SPACE" || Del1 ==String "SIZE" ) && ( Del2 ==String "SPACE" || Del2 ==String "SIZE" ) )
			{	if(Del1 ==String "SPACE") { findChar(S1," ", Pos) ~> S1 = substrString(S1,0,Pos) }
				if(Del2 ==String "SPACE") { findChar(S2," ",Pos) ~> S2 = substrString(S2,0,Pos) }
				S3 =String S1 +String S2 ~> I =Int lengthString(S3) }

  rule STRING S1:String DELIMITED BY Del1:String S2:String DELIMITED BY Del2:String INTO S3:String WITH POINTER I:Int ON OVERFLOW DISPLAY S4:String END-STRING => 
		if((Del1 ==String "SPACE" || Del1 ==String "SIZE") && (Del2 ==String "SPACE" || Del2 ==String "SIZE"))
			{	if(Del1 ==String "SPACE") { findChar(S1," ",Pos) S1 =String substrString(S1,0,Pos) }
				if(Del2 ==String "SPACE") { findChar(S2," ",Pos) S2 =String substrString(S2,0,Pos) }
				S3length =String lengthString(S3) ~> S3 =String S1 +String S2 ~> I =String lengthString(S3) 
			}
		requires I >Int S3
				
  //UNSTRING
  rule UNSTRING S1:String DELIMITED BY SPACE INTO List END-UNSTRING =>

    StartPos =Int 0 ~> Index =Int 0 ~> 
	while( Index <Int size(List) ){
      //cerco la posizione dello spazio 								 splitto                          					riaggiusto l'indice per cercare lo spazio successivo
      findChar(substrString(S1,StartPos,stringLength(S1))," ",EndPos) ~> List[i] =String substrString(S1,StartPos,EndPos) ~> StartPos =Int EndPos ~> i =Int i +Int 1
    }
				
// Pgm
  rule <k> int (X,Xs => Xs); ...</k>
  <env> Rho => Rho[X <- !N:Int] ...</env>
  <store>... .Map => !N |-> 0 ...</store>
  rule int .Ids; => . [structural]

endmodule