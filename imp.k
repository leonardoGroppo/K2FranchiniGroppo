////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
//
//                                PROJECT K2 
//                     Groppo Leonardo - Franchini Andrea
//
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////
//
//                                TODO
//
//	-i PERFORM funzionano solo su blocchi precedentemente dichiarati
//
////////////////////////////////////////////////////////////////////////////


require "builtins/string.k"
require "io/io.k"
require "builtins/list.k"

////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
//
//
//                                SYNTAX MODULE 
//
//
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////

module IMP-SYNTAX

  	syntax AExp  ::= Int | Id | String
                  	| AExp "/" AExp     [left, strict]
				  	| AExp "*" AExp		[left, strict]
                  	> AExp "+" AExp     [left, strict]
        			| AExp "-" AExp		[left, strict]
                  	| "(" AExp ")"      [bracket]

  	syntax BExp  ::= Bool
                 	| AExp "<=" AExp     [seqstrict, latex({#1}\leq{#2})]
				  	| AExp ">=" AExp     [seqstrict, latex({#1}\geq{#2})]
				  	| AExp "==" AExp 	 [strict]
                  	| "!" BExp           [strict]
                  	> BExp "&&" BExp     [left, strict(1)]
				  	| BExp "||" BExp	 [left, strict(1)]
				  	| BExp "==" BExp 	 [strict]
                  	| "(" BExp ")"       [bracket]

  	syntax Block ::=  AExp ":{" "}"		
                  	| AExp ":{" Stmt "}"	
                  	| "{" "}"
                  	| "{" Stmt "}"

  	syntax Stmt  ::= Block
                  	| AExp "=" AExp ";"                     [strict(2)] 
                  	| "int" Ids ";"
                  	| "String" Ids ";"
                  	| "if" "(" BExp ")" Block "else" Block  [strict(1)]
                  	| "while" "(" BExp ")" Block

	////////////////////////////////////////////////////////////////////////////
	//                              STRING STATEMENT 
	////////////////////////////////////////////////////////////////////////////

			//STRING INSPECT
			| "INSPECT" AExp "TALLYING" Id "FOR ALL-CHARACTERS"                              	[strict(1)]
			| "INSPECT" AExp "TALLYING" Id "FOR ALL" AExp                                    	[strict(1,3)]
			| "INSPECT" Id "REPLACING ALL" AExp "BY" AExp                                    	[strict(2,3)]

			//STRING CONCATENATION
			| "STRING" Id "DELIMITED BY SIZE"  Id "DELIMITED BY SIZE INTO"  Id "END-STRING"   	[strict]   
			| "STRING" Id "DELIMITED BY SPACE" Id "DELIMITED BY SIZE INTO"  Id "END-STRING" 	[strict]
			| "STRING" Id "DELIMITED BY SIZE"  Id "DELIMITED BY SPACE INTO" Id "END-STRING" 	[strict]
			| "STRING" Id "DELIMITED BY SPACE" Id "DELIMITED BY SPACE INTO" Id "END-STRING" 	[strict]	

					//INTERMEDIATE RULES
	                | "STRING" AExp Id 	 "INTO" Id       "END-STRING" 		[strict(1)]
	                | "STRING" AExp AExp "INTO" Id       "END-STRING" 	    [strict(1,2)]
	                | "STRING" Id AExp 	 "INTO" Id       "END-STRING"		[strict(2)]
	                | "STRING" AExp Id   "SPACE INTO" Id "END-STRING"		[strict(1)]				

			//STRING SPLIT
            | "UNSTRING" AExp "DELIMITED BY SPACE INTO" Ids  "END-UNSTRING" 	[strict(1)]



	////////////////////////////////////////////////////////////////////////////
	//                              LOOP STATEMENT 
	////////////////////////////////////////////////////////////////////////////

            //PERFORM TIMES
            | "PERFORM" AExp AExp "TIMES" 	

            //PERFORM VARYING
            | "PERFORM" AExp "VARYING" Id "FROM" AExp "BY" AExp "UNTIL" Id "=" AExp

            		//INTERMEDIATE RULES
            		| "PERFORM" AExp "VARYING" Id "BY" AExp "UNTIL" AExp
 


            > Stmt Stmt   [left]

  	syntax Ids    ::= List{Id,","}			[seqstrict]
  	syntax AExps  ::= List{AExp, ","}       [seqstrict]

endmodule

////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
//
//
//                             SEMANTIC MODULE 
//
//
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////

module IMP

  	imports IMP-SYNTAX 

  	syntax KResult ::= Int | Bool | String

  	//syntax K ::= "search" "(" Stmt ")" [function]
  	//rule search(Statement:Stmt PGM) => #if isBuiltin(Statement) #then search(PGM) #else search(PGM) #fi
  	//rule search(Statement:Stmt) => .K

  	configuration
		<T>
			//<k> search($PGM) ~> $PGM:K </k>
			<k> $PGM:K </k>
			<env> .Map </env> 
			<store> .Map </store>
			<block> .Map </block>
		</T>


	/////////////////////////////////////////////////////////////////////////////
	//                        <env> & <store> BEHAVIOR
	////////////////////////////////////////////////////////////////////////////

	//////////////////////
	//        INT
	//////////////////////

	//INT DECLARATION
	rule <k> int (X:Id, X1:Ids => X1); ...</k>
	    <env> Rho:Map => Rho[X <- !N:Int] </env>
	    <store>... .Map => !N |-> 0 ...</store>
	  	when notBool(X in keys(Rho))

	//MANAGEMENT OF INT EMPTY LIST
	rule int .Ids; => .K [structural]

	//INT ASSIGN
  	rule <k> X = I:Int; => . ...</k>
  		<env>... X |-> N ...</env>
  		<store>... N |-> (_ => I) ...</store>

	//READING INT
  	rule <k> X => I ...</k> 
  		<env>... X |-> N ...</env> 
  		<store>... N |-> I:Int ...</store>

  	//////////////////////
	//      STRING
	//////////////////////

	//STRING DECLARATION
	rule <k> String (X:Id, X1:Ids => X1); ...</k>
	    <env> Rho:Map => Rho[X <- !N:Int] </env>
	    <store>... .Map => !N |-> "" ...</store>
		when notBool(X in keys(Rho))

	//MANAGEMENT OF STRING EMPTY LIST
	rule String .Ids; => .K [structural]

	//STRING ASSIGN
	rule <k> X = S:String; => . ...</k> 
	  	<env>... X |-> L ...</env>
	  	<store>... L |-> (_ => S) ...</store>

	//READING STRING
  	rule <k> X => S ...</k> 
		<env>... X |-> N ...</env> 
		<store>... N |-> S:String ...</store>

	/////////////////////////////////////////////////////////////////////////////
	//                             BASIC RULES
	////////////////////////////////////////////////////////////////////////////

	//INT OPERATIONS
	rule I1 / I2 => I1 /Int I2  when I2 =/=Int 0
	rule I1 * I2 => I1 *Int I2
	rule I1 + I2 => I1 +Int I2
	rule I1 - I2 => I1 -Int I2
	rule S1 + S2 => S1 +String S2
	  
	//BOOLEAN OPERATION
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
	  
	//BLOCK MANAGEMENT
	rule { } => .   							[structural]
	rule {S} => S  								[structural]
	rule L:String :{ } => . 					[structural]

	//STATEMENT MANAGEMENT
    rule S1:Stmt S2:Stmt => S1 ~> S2    [structural]

	//CONDITION MANAGEMENT
	rule if (true)  S else _ => S
	rule if (false) _ else S => S
	rule while (B) S => if (B) { S while (B) S } else {}       [structural]





////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
//                              STRING RULES 
//
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


	//////////////////////////////////////////
	//				STRING INSPECT	   
	//////////////////////////////////////////

	//Count the occurrences of all characters, in other words, the string's length
	rule <k> INSPECT S1:String TALLYING I1:Id FOR ALL-CHARACTERS => .K ...</k>
	  	<env>... I1 |-> N ...</env>
	  	<store>... N |-> (_ => lengthString(S1)) ...</store>
		  
	//Count the occurrences of the given character
	rule <k> INSPECT S1:String TALLYING I1:Id FOR ALL S2:String => .K ...</k> 
	     <env> ... I1 |-> N ...</env>
	     <store> ... N |-> (_ => countAllOccurrences(S1,S2)) ...</store> when lengthString(S2) =Int 1
		  
	//Replace all the occurrences of the first character with the second one
	rule <k> INSPECT S1:Id REPLACING ALL S2:String BY S3:String => .K ...</k>
	    <env>... S1 |-> N ...</env>
	    <store>... N |-> (S => replaceAll(S,S2,S3) ) ...</store>  //replaceAll test itself if s2 s3 are character



	///////////////////////////////////////////////  
	//				STRING CONCATENATION	   
	///////////////////////////////////////////////

	//CASE "SIZE SIZE" 

	//Fetch first string value
  	rule <k> STRING S1:Id DELIMITED BY SIZE S2:Id DELIMITED BY SIZE INTO S3:Id END-STRING => 
  		 	 STRING S1value:String S2:Id INTO S3:Id END-STRING ...</k>
      	<env>... S1 |-> N ...</env>
     	<store>... N |-> S1value ...</store>

				//Fetch second string value
			  	rule <k> STRING S1value:String S2:Id INTO S3:Id END-STRING => 
			  			 STRING S1value:String S2value:String INTO S3:Id END-STRING ...</k>
			 		<env>... S2 |-> N ...</env>
			     	<store>... N |-> S2value ...</store>

			    //Concatenation
			    rule <k> STRING S1value:String S2value:String INTO S3:Id END-STRING => .K ...</k>
					<env>... S3 |-> N ...</env>
			     	<store>... N |-> (_ => S1value +String S2value ) ...</store>


	//CASE "SPACE SIZE" 

	//Fetch first string value and substringing it
	rule <k> STRING S1:Id DELIMITED BY SPACE S2:Id DELIMITED BY SIZE INTO S3:Id END-STRING =>
			 STRING substrString(S1value, 0, findChar(S1value, " ", 0)) S2:Id INTO S3:Id END-STRING ...</k>
		<env>... S1 |-> N ...</env>
     	<store>... N |-> S1value ...</store>

     			//I will bring me to the case "SIZE SIZE" -> Fetch second string value -> Concatenation


    //CASE "SIZE SPACE"

    //Fetch second string value and substringing it
	rule <k> STRING S1:Id DELIMITED BY SIZE S2:Id DELIMITED BY SPACE INTO S3:Id END-STRING =>
			 STRING S1:Id substrString(S2value, 0, findChar(S2value, " ", 0)) INTO S3:Id END-STRING ...</k>
		<env>... S2 |-> N ...</env>
     	<store>... N |-> S2value ...</store>

			    //Fetch first string value
			    rule <k> STRING S1:Id S2value:String INTO S3:Id END-STRING =>
			    		 STRING S1value:String S2value:String INTO S3:Id END-STRING ...</k>
			      	<env>... S1 |-> N ...</env>
			     	<store>... N |-> S1value ...</store>

			    //I will bring me to the case "SIZE SIZE" -> Concatenation


    //CASE "SPACE SPACE" 

    //Fetch first string value and substringing it
	rule <k> STRING S1:Id DELIMITED BY SPACE S2:Id DELIMITED BY SPACE INTO S3:Id END-STRING =>
			 STRING substrString(S1value, 0, findChar(S1value, " ", 0)) S2:Id SPACE INTO S3:Id END-STRING ...</k>
		<env>... S1 |-> N ...</env>
     	<store>... N |-> S1value ...</store>

	     		//Fetch second string value and substringing it
			    rule <k> STRING S1value:String S2:Id SPACE INTO S3:Id END-STRING =>
					     STRING S1value:String substrString(S2value, 0, findChar(S2value, " ", 0)) INTO S3:Id END-STRING ...</k>
					<env>... S2 |-> N ...</env>
			     	<store>... N |-> S2value ...</store>

			    //I will bring me to the case "SIZE SIZE" -> Concatenation



    ///////////////////////////////////////////////  
	//				  STRING SPLIT	   
	///////////////////////////////////////////////

	//Split the list by the space into the list of variables
    rule <k> UNSTRING S1:String DELIMITED BY SPACE INTO X:Id, VarList:Ids END-UNSTRING => 

    					//recursive calling itself passing the string without the splitted word
    		 UNSTRING 	substrString(S1, findChar(S1, " ", 0)+Int 1, lengthString(S1)) 
    		 			DELIMITED BY SPACE INTO VarList 
    		 END-UNSTRING ... </k>

    	//save the word of the string
    	<env>... X |-> N ...</env>
		<store>... N |-> (_ => substrString(S1, 0, findChar(S1, " ", 0))) ...</store> 

		//until it's reached the last word of the string
		when findChar(S1, " ", 0) =/=Int -1

				//base case: it's reached the last word of the string
			    rule <k> UNSTRING S1:String DELIMITED BY SPACE INTO X:Id, VarList:Ids END-UNSTRING => .K ... </k>
			    	<env>... X |-> N ...</env>
			    	//save the last word
					<store>... N |-> (_ => S1) ...</store> 
					when findChar(S1, " ", 0) ==Int -1

				//base case: there are no variables left in the list
				rule UNSTRING S1:String DELIMITED BY SPACE INTO .Ids END-UNSTRING => .K





////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
//
//                              LOOP RULES
//
////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////


	///////////////////////////////////////
	//			BLOCK CONTROL	
	///////////////////////////////////////


	rule <k> L:String :{S} => S ...</k>

		//<pgm>... LBL:String :{STM} => .K ...</pgm>
		//<block> Rho:Map => Rho[L <- S]</block>
		when L ==String "START"

	rule <k> L:String :{S} => S ...</k>
		<block> Rho:Map => Rho[L <- S]</block>
		when L =/=String "START"	



	///////////////////////////////////////
	//			PERFORM TIMES	
	///////////////////////////////////////

	//Recursive rule
	rule <k> PERFORM LBL:String N:Int TIMES => STM PERFORM LBL N-Int 1 TIMES ...</k>
		<block>... LBL |-> STM ...</block>
		when N =/=Int 0

				//base case
				rule <k> PERFORM LBL:String N:Int TIMES => .K ...</k>
					when N ==Int 0

	///////////////////////////////////////
	//			PERFORM VARYING	
	///////////////////////////////////////

	//starting rule
	rule <k> PERFORM Lbl:String VARYING Var:Id FROM StartValue:Int BY Increment:Int UNTIL Var:Id = EndValue:Int => 
			 PERFORM Lbl VARYING Var BY Increment UNTIL EndValue </k>

		<env>... Var |-> N ...</env>
		<store>... N |-> (VarValue => StartValue) ...</store> 

		when ((VarValue +Int Increment) <=Int EndValue) andBool Increment =/=Int 0

				//starting rule case base
				rule <k> PERFORM Lbl:String VARYING Var:Id FROM StartValue:Int BY Increment:Int UNTIL Var:Id = EndValue:Int => .K ...</k>

					<env>... Var |-> N ...</env>
					<store>... N |-> VarValue ...</store> 

					when ((VarValue +Int Increment) >Int EndValue) andBool Increment ==Int 0

				//recursive rule
				rule <k> PERFORM Lbl:String VARYING Var:Id BY Increment:Int UNTIL EndValue:Int => 
						 STM PERFORM Lbl VARYING Var BY Increment UNTIL EndValue </k>

					<block>... LBL |-> STM ...</block>
					<env>... Var |-> N ...</env>
					<store>... N |-> (VarValue => VarValue +Int Increment) ...</store>

					when (VarValue +Int Increment) <=Int EndValue

				//base case
				rule <k> PERFORM Lbl:String VARYING Var:Id BY Increment:Int UNTIL EndValue:Int => .K </k>

					<env>... Var |-> N ...</env>
					<store>... N |-> VarValue ...</store> 

					when (VarValue +Int Increment) >Int EndValue

endmodule