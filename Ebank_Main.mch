MACHINE Ebanking

/* Specifiers:Meherkhan */
/* Date : 5/5/2017 */
/* An Electronic Banking is a collection of online accounts */
/* which are available for customers  */


SETS
 	Account;
	Person;
	Admin;
	Exception = {OK, UnknownCustomer, UnknownAccount, UnknownNumber, UnknownLogin, UnknownLogoff, CustomerLogin, CustomerLogoff, CustomerNotStart, 
CustomerNotFinish }
	
VARIABLES 
	accounts,
	customers,
	login,
	balance,
	start,
	finish,
	loans,
	bill,
	admins,	
	adminslogin,
	raise
	

INVARIANT
	
	accounts: POW(Account) &
	customers:  POW(Person)&
	balance: Account <-> NAT	&
	dom (balance) <: Account&
	ran (balance) <: NAT&
	login: Account <-> NAT&
	dom (login) <: Account&
	start : Person <->NAT&
	finish : Person <->NAT&
	dom (finish) <: dom(start)&
	
	loans: Account <->  Person &
	dom (loans) <: Account&	
	ran (loans) <:Person&
	
	bill: NAT&
	admins: POW(Admin)&
	adminslogin: Admin <->NAT& 
	dom (adminslogin) <: Admin& 
	raise:Exception

INITIALISATION 
	accounts := {} ||
	customers := {}||
	balance:={}||	
	login :={}||
	start:={}||
	finish:={}||
	loans:={}||
	bill:=0||
	admins:={}||
	adminslogin:={}||
	raise := OK

OPERATIONS
 		reset =
		raise := OK
        		;
 

/* A Customer (person) and a  Account can be added to the online system by an admin */
/* this operation cannot be performed if the person  */ 
/* is already a customer.  */ 

	openAccount(a,c) =
	  	
		PRE
		a:Account&
		c: Person&
		c/: customers
	  	THEN
		accounts := accounts \/ {a} || customers := customers \/ {c}
		END;
	
/* DELETEACCOUNT       */
 /* accounts can be deleted when there is no longer a need them*/ 
/* They should not be on loan or reserved when */ /* deleted.        */ 
	
	deleteAccount(a,c) =
	  	
		PRE
		a:Account&
		c:Person&
		a/: dom (loans)
	  	THEN
		accounts := accounts - {a} || customers := customers - {c}
		END;

	openSavingAccount(a,c) =
	  	
		PRE
		a:Account&
		c: Person&
		c: customers
	  	THEN
		accounts := accounts \/ {a} 
		END;

	deleteSavingAccount(a,c) =
	  	
		PRE
		a:Account&
		a/: dom (loans)&
		c: customers
	  	THEN
		accounts := accounts - {a} 
		END;

	
	createLogin(a,p)  =

	         	PRE		
		a:Account&
		p: NAT&
		a/: dom (login)
		THEN		
		login := login  \/ {a |->p }
 		END;

	closeLogin(l,c)  =

	         	PRE		
		l : login&
		c: Person&
		c/: dom (start)
		THEN		
		login := login  - {l}
 		END;

	customerlogin (c,t)=
			
		PRE raise = OK
		
		THEN /* *** Exceptional behaviour *** */
		IF c /: Person THEN raise := UnknownCustomer ELSE
		IF t /: NAT THEN raise := UnknownNumber ELSE
		IF c : (dom(finish) \/ dom(start)) THEN raise := CustomerLogin ELSE
		
		/* *** Functional behaviour **** */
		start := start \/ { c |->t}
		END END END
		END;

	customerlogoff (c,t)=	
	
		PRE raise = OK
		
		THEN /* *** Exceptional behaviour *** */
		
		IF c /: dom(start) THEN raise := UnknownCustomer ELSE 
		IF t/:NAT THEN raise := UnknownNumber ELSE 
		IF c : dom(finish) THEN raise := UnknownLogoff ELSE
		
		/* *** Functional Behaviour **** */
		finish := finish \/ { c |->t}
		END END END	
		END;

	balancetransfer(c,a,b)=
		
		PRE
		c:Person&
		a:Account&
		b: NAT&
		c/: dom(finish)	
		THEN
		balance := balance - {a |->b}
		END;


/* APPLYLOAN:       */ 
/* A  loan can be applied by a customer.  The loan must not  */ 
/* already on appliedloans.  Also it must not be applied by */ /* customer.*/

	applyloan(a,c)=
		
		PRE
		a:Account&
		c:Person&
		a/: dom(loans)&
		c/: ran(loans)
			
		THEN
		loans := loans \/ {a |-> c}
		END;

	billpay(a,c)=
		
		PRE
		a:Account&
		c:Person&
		c/: dom(finish)	&
		balance(a) >= bill  
					
		THEN
		balance := balance - {a |-> bill}
		END;

	createAdminLogin(a,p)  =

	         	PRE		
		a:Admin&
		p: NAT
		
		THEN		
		adminslogin := adminslogin  \/ {a |->p }
 		END;
	

 /* accountsONLOAN:       */ 
/* Lists the accounts on loan to a given online customer.  */ 

	ListLoanaccounts<-- accountsOnLoanTo(person) = 
		PRE    person : Person &
		            person : ran(loans)  
		THEN   
		ListLoanaccounts := {x | x : Account & loans(x) = person}  
		END; 


/* CUSTOMERSCOUNT:       */ /*Interrogates Operation make a reports total number of Customers in the Online Banking System  */ 

	numberOfCustomers<-- customerCount =  
	  numberOfCustomers := card(customers) 




END
