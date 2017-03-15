; **************** BEGIN INITIALIZATION FOR ACL2s B MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#|
Pete Manolios
Fri Jan 27 09:39:00 EST 2012
----------------------------

Made changes for spring 2012.


Pete Manolios
Thu Jan 27 18:53:33 EST 2011
----------------------------

The Beginner level is the next level after Bare Bones level.

|#

; Put CCG book first in order, since it seems this results in faster loading of this mode.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "ccg/ccg" :uncertified-okp nil :dir :acl2s-modes :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "base-theory" :dir :acl2s-modes)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :ttags :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading trace-star and evalable-ld-printing books.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "trace-star" :uncertified-okp nil :dir :acl2s-modes :ttags ((:acl2s-interaction)) :load-compiled-file nil)
(include-book "hacking/evalable-ld-printing" :uncertified-okp nil :dir :system :ttags ((:evalable-ld-printing)) :load-compiled-file nil)

;theory for beginner mode
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s beginner theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "beginner-theory" :dir :acl2s-modes :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s Beginner mode.") (value :invisible))
;Settings specific to ACL2s Beginner mode.
(acl2s-beginner-settings)

; why why why why 
(acl2::xdoc acl2s::defunc) ; almost 3 seconds

(cw "~@0Beginner mode loaded.~%~@1"
    #+acl2s-startup "${NoMoReSnIp}$~%" #-acl2s-startup ""
    #+acl2s-startup "${SnIpMeHeRe}$~%" #-acl2s-startup "")


(acl2::in-package "ACL2S B")

; ***************** END INITIALIZATION FOR ACL2s B MODE ******************* ;
;$ACL2s-SMode$;Beginner
#|

CS 2800 Homework 8 - Spring 2017

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

This homework is to be done in a group of 2-3 students. It is designed
to give you practice with function admissibility and introduce you to
measure functions.

If your group does not already exist:

 * One group member will create a group in BlackBoard
 
 * Other group members then join the group
 
 Submitting:
 
 * Homework is submitted by one group member. Therefore make sure the person
   submitting actually does so. In previous terms when everyone needed
   to submit we regularly had one person forget but the other submissions
   meant the team did not get a zero. Now if you forget, your team gets 0.
   - It wouldn't be a bad idea for group members to send confirmation 
     emails to each other to reduce anxiety.

 * Submit the homework file (this file) on Blackboard.  Do not rename 
   this file.  There will be a 10 point penalty for this.

 * You must list the names of ALL group members below, using the given
   format. This way we can confirm group membership with the BB groups.
   If you fail to follow these instructions, it costs us time and
   it will cost you points, so please read carefully.


Names of ALL group members: Izaak Branch, Chris Kenyon

Note: There will be a 10 pt penalty if your names do not follow 
this format.

For this homework you will NOT need to use ACL2s. However, you could
use the Eclipse/ACL2s text editor to write up your solution.

|#


#|

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Admissible or not?
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

For each of the definitions below, check whether it is theoretically 
admissible, i.e. it satisfies all rules of the definitional principle. 
You can assume that Rule 1 is met: the symbol used in the defunc is a new 
function symbol in each case.

If you claim admissibility, BRIEFLY

1. Explain in English why the body contracts hold.
2. Explain in English why the contract theorem holds.
3. Suggest a measure function that can be used to show termination.
   (You DO NOT have to prove the measure function properties in this problem.)

Otherwise, identify a rule in the Definitional Principle that is violated.

If you blame one of the purely syntactic rules (variable names,
non-wellformed body etc), explain the violation in English.

If you blame one of the semantic rules (body contract, contract theorem or
termination), you must provide an input that satisfies the input contract, but
causes a violation in the body or violates the output contract or causes
non-termination.

Remember that the rules are not independent: if you claim the function does
not terminate, you must provide an input on which the function runs forever
*without* causing a body contract violation: a body contract violation is
not a counterexample to termination. Similarly, if you claim the function
fails the contract theorem, you must provide an input on which it
terminates and produces a value, which then violates the output contract.

Your explanations should be brief but clear. We are not looking for a page 
of text per question but we also want to clearly see that you understand 
the function and if/what is wrong with it.

I used the term "theoretically admissible" because for some functions below
you can demonstrate they are admissible but ACL2s won't actually admit it 
without a lot of extra guidance from you (this isn't your responsibility).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SECTION 1: Admissibility
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
1.

(defunc f1 (p)
  :input-contract (posp p)
  :output-contract (posp (f1 p))
  (if (equal p 0)
    0
    (f1 (- p 1))))
    
 This is not admissible. The stopping condition is when p = 0, but when p = 0,
 the input contract is violated. (posp 0) is nil, so (f1 1) will violate body contract


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
2.

(defunc f2 (a b)
  :input-contract  (and (posp a) (posp b))
  :output-contract (posp (f2 a b))
  (cond ((or (equal a 1) (equal b 1)) 1)
        ((> a b)          (f2 a (- b 1)))
        (t                (f2 b a))))

This is not admissible. It does not terminate given positive integers a b that
are equal and not equal to 1. (f2 5 5) will call (f2 5 5)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
3.

(defunc f3 (x y)
  :input-contract (and (natp x) (posp y))
  :output-contract (natp (f3 x y))
  (cond ((equal y 1) y)
        ((equal x 0) x)
        ((< y x)     (f3 y x))
        (t           (f3 x (- y 1)))))

This is admissible. 
1. The body contracts hold, for < because all natp and posp are rationalp. f3 contracts hold
as (f3 y x) could only violate the (posp y) input contract if x were 0, which is not possible
due to the previous condition in the cond block. (f3 x (- y 1)) could violate the (posp y) input
contract only if y were 1, but this is not possible due to the (equal y 1) condition earlier
2. Contract theorem holds because given a valid input, the stopping condition (equal y 1) or
(equal x 0) will return a pos or nat respectively, and all pos's are nats, satisifying the oc
3. (defunc m-f3 (x y)
      :input-contract (and (natp x) (posp y))
      :output-contract (natp (m-f3 x y))
      (+ x (/ y 2)))
      
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
4.

(defunc f4 (x y)
  :input-contract (and (listp x) (natp y))
  :output-contract (listp (f4 x y))
  (if (equal y 0)
    (list y)
    (f4 (list (first x)) (- y 1))))

This is not admissible. It fails the body contract if x is nil. (f4 nil 10) causes error

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
5.

(defunc f5 (z)
  :input-contract (posp z)
  :output-contract (integerp (f5 z))
  (if (equal z 1)
    9
    (- 5 (f5 (- z 1)))))
    
This is admissible.
1. The body contracts are satisfied, the - call will always have a 5 and an integer thanks
to the output contract of f5, and f5's input contract will be satisfied because it can only
be broken if z were 1 to make the call be (f5 0), which cannot happen because it would evaluate
to 9 if (equal z 1) were true.
2. Contract theorem holds because with valid input, the stopping condition of (equal z 1) will
return a result of subtraction of 5's, 9's, and pos's, which assures an integer output.
3. 
(defunc m-f5 (z)
  :input-contract (posp z)
  :output-contract (natp (m-f5 z))
  z)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
6.

(defunc f6 (i)
  :input-contract (integerp i)
  :output-contract (integerp (f6 i))
  (if (< i -5)
    i
    (f6 (- f6 i))))

This is not admissible. It contains a free variable f6 which violates the input contract of -
    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
7.

(defunc f7 (x y)
  :input-contract (and (listp x)(natp y))
  :output-contract (natp (m-f7 x y))
  (cond ((equal y 0) (len x))
        ((endp x)    0)
        (t           (f7 (list y) (len x)))))

This is not admissible. With any input other than an empty list as x or 0 as y, the function
will not terminate, as it will always execute the t branch of the cond block, calling f7 with
a list of length 1 for x and a nat for y

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
8.

(defunc f8 (x y)
  :input-contract (and (integerp x) (integerp y))
  :output-contract (integerp (f8 x y))
  (if (>= x 0)
    (+ x y)
    (+ (* 2 y) (f8 (+ x 1) (- y 1)))))

This is admissible. 
1. It holds the body contracts for >=, +, -, and f8 as all the inputs are integers regardless
of the inputs of f8
2. Contract theorem holds because with valid input, the stopping condition of (>= x 0) will
always be achieved as x increases.
3. 
(defunc m-f8 (x y)
  :input-contract (and (integerp x) (integerp y))
  :output-contract (natp (m-f8 x y))
  (- 0 x))
    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
9.

(defunc f9 (i x i)
  :input-contract (and (integerp i) (listp x) (integerp i))
  :output-contract (posp (f9 i x i))
  (if (endp x)
    0
    (f9 i (rest x) i)))
    
This is not admissible. Variable names in a function definition must be unique,
and the variable i appears twice in the declaration of this function.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
10.

(defunc f10 (x y)
  :input-contract (and (listp x) (listp y))
  :output-contract (posp (f10 x y))
  (if (endp x)
    0
    (f10 x (rest y))))

This is not admissible. It does not check (endp y), yet blindly calls (rest y), 
therefore violating the body contract if y is nil, as (rest nil) is a violation.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
11.

(defunc f11 (x n)
  :input-contract (and (listp x) (integerp n))
  :output-contract (listp (f11 x n))
  (if (equal n 0)
    (list n)
    (f11 (cons n (rest x)) (- n 1))))

This is not admissible, due to a body contract violation on (rest x). We
never check (endp x), but if n != 0 then we will attempt to call (rest x).
Example of failure would be (f11 '() 2)

    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
12.

(defunc f12 (p)
  :input-contract (posp p)
  :output-contract (posp (f12 p))
  (if (equal p 1)
      6
    (f12 (- 7 (f12 (- p 1))))))

This is admissible.
1. Body contract calls to f12 can only fail if p=1, which would result in 
us attempting to call (f12 0), which would violate the function contract of f12.
However, if p=1 we simply return 6, and we would never call (f12 0)
2. Contract theorem holds because as long as input is positive (the IC), the result will either be
6 (in the case that p=1), or p will be monotonically decreased until it is 1 in the recursive call,
resulting in the recursive call returning 6, calling (f12 (- 7 6)) and returning 1. For sufficiently
large values of p, this function will blow out your memory stack, but with infinite memory it works.
3.
(defunc m-f12 (p)
 :ic (posp p)
 :oc (natp (m-f12 p))
 p)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
13.

(defunc f13 (p i)
  :input-contract (and (posp p)(integerp i))
  :output-contract (posp (f13 p i))
  (cond ((equal p 1)   9)
        ((< i 1)       (f13 (- p 1) i))
        (t             (f13 i (- p 2)))))
 
This is admissible.
1. Body contract for < passes, as i is an integer. Body contract calls to f13
pass - p must be positive, but if it fails the first cond then it must also be greater
than 1, therefore calling (f13 (- p 1) i) will result in a new value of p no lower
than 1, until the value of p is 1 and 9 is returned. In cases where the second cond
also fails, we are guaranteed that i>=2, which satisfies the input contract f13.
2. Contract theorem holds because as far as I can tell this function will either
recurse (with valid inputs, as discussed in body contract checking) or return 9, which is posp.
3.
(defunc m-f13 (p i)
 :ic (and (posp p)(integerp i))
 :oc (natp (m-f13 p i))
 (+ (abs i) p))
 
 or, if you guys really want to be sticklers,
 
(defunc m-f13 (p i)
 :ic (and (posp p)(integerp i))
 :oc (natp (m-f13 p i))
 (if (< 0 i) (+ (unary-- i) p)
             (+ i p))

 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

14.

(defunc f14 (x y)
  :input-contract  (and (posp x) (posp y))
  :output-contract (posp (f14 x y))
  (cond ((equal x y)    1)
        ((> x y)        (f14 y x))
        (t              (f14 (- x y) y))))

This is not admissible due to a body contract violation. If it tries to recurse
and y > x (which is the implied third condition, as they are not equal and x is not greater than y),
then the input for x will be a negative number, violating the (posp x) requirement of f14.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
15.

(defunc f15 (x y)
  :input-contract (and (posp x) (posp y))
  :output-contract (integerp (f15 x y))
  (cond ((< x 1)     (f15 x y))
        ((equal x y) 5)
        ((< x y)     (f15 y x))
        (t           (* 5 (f15 (- x 1) y)))))

This is admissible.
1. The first cond will never be executed, as x >= 1 by the IC. Additionally, we
are guaranteed by the third cond that if x and y are not equal, x is greater than y
(because if x is less than y, we just recurse with the variable positions switched, and the first
cond will still pass because y is under the same IC constraint as x). If x and y are equal, we are done.
The final case is that x is strictly greater than y, and y is at least 1 (IC), so subtracting 1 from x will 
result in a number no lower than 1, and the recursive call to f15 in the fourth conditional passes 
body contract checking. In this case, we just keep subtracting 1 from x until it's equal to y.
2. Function contract holds, this function essentially boils down to doing 5^(abs(x - y)), which is guranteed
to be an integer.
3. I'm not totally sure how to write this - after the first iteration, x will always decrease, but it could increase
once - if y is greater than x, the value of x will increase from the first to the second interation, and decrease
consistently after that. So here goes:
(defunc m-f15 (x y)
 :ic (and (posp x) (posp y))
 :oc (natp (m-f15 x y))
 (if (< x y) y x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

16.

(defunc f16 (x y)
  :input-contract (and (listp x) (natp y))
  :output-contract (listp (f16 x y))
  (cond ((equal y 0)  (f16 x (len x)))
        ((endp x)     (list y))
        (t            (f16 (rest x) (- y 1)))))
  
This is not admissible due to termination failure. If y is 0 and x is nil, then (len x) = 0, so
we will never terminate and infinitely recurse with the arguments x=nil and y=0.
        
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

17.

(defunc  f17 (l)
  :input-contract (listp l)
  :output-contract (booleanp (f17 l))
  (cond ((endp l)  l)
        ((in e l)  t)
        (t         (cons (first l)(f17 (rest l))))))

This is not admissible, because we have a free variable e that is not defined, so 
the call to (in e l) blows up.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SECTION 2: DOES IT TERMINATE?
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; For each of the following functions, mention whether the function terminates 
;; or not. If it does, give a measure function for it (here we are not asking 
;; you to prove anything). Features of a valid measure function are described
;; in section 3 below and in the notes.
;; If it does not terminate, give a concrete input on which it fails.
;; Here is a function you can use to help you

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GIVEN
;; abs: integer -> natural
;; (abs i) takes an integer value
;; and returns the absolute value
;; of that number (thus a natural number)
(defunc abs (i)
  :input-contract (integerp i)
  :output-contract (natp (abs i))
  (if (< i 0) (unary-- i)  i))

#|
(defunc f18 (n)
  :input-contract (natp n)
  :output-contract (integerp (f18 n))
  (if (equal n 0)
    14
    (-  (f18 (- n 1)) (* (* n n) n))))

Terminates.
(defunc m-f18 (n)
  :input-contract (natp n)
  :output-contract (natp (m-f18 n))
  n)
  

(defunc  f19 (x)
  :input-contract (integerp x)
  :output-contract (integerp (f19 x))
  (cond ((equal x 0) 1)
        ((> x 0) (* x (f19 (- x 1))))
        (t (* x (f19 (+ x 1))))))

Terminates.
(defunc m-f19 (x)
  :input-contract (integerp x)
  :output-contract (natp (m-f19 x))
  (abs x))

(defunc  f20 (n m)
  :input-contract (and (integerp n)(integerp m))
  :output-contract (integerp (f20 n m))
  (cond ((equal n m)                 1)
        ((< n m)  (f20 (+ n 1)(- m 1)))
        (t             (f20 (- n 1) m))))
       
...........

(defunc  f21 (l i)
  :input-contract (and (listp l)(integerp i))
  :output-contract (listp (f21 l i))
  (if (< i 0) 
    l
    (f21 l (- i (len l)))))

...........

        

(defunc  f22 (l1 l2)
  :input-contract (and (listp l1)(listp l2))
  :output-contract (booleanp (f22 l1 l2))
  (cond ((endp l2)    t)
        ((in (first l2) l1)  (f22 l1 (rest l2)))
        (t    (f22 (cons (first l2) l1) (rest l2)))))

........

|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; PROVING A MEASURE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|

You can prove a function f terminates using a measure function m. 
This requires the following conditions are met:

Condition 1. m has the same arguments and the same input contract as f.
Condition 2. m's output contract is (natp (m ...))
Condition 3. m is admissible.
Condition 4. On every recursive call of f, given the input contract and 
   the conditions that lead to that call, m applied to the arguments in
   the call is less than m applied to the original inputs.

You should do this proof as shown in class (which is also the way we will
expect you to prove termination on exams):

- Write down the propositional logic formalization of Condition 4.
- Simplify the formula.
- Use equational reasoning to conclude the formula is valid.

Unless clearly stated otherwise, you need to follow these steps for EACH
recursive call separately.

Here is an example.

(defunc f (x y)
  :input-contract (and (listp x) (natp y))
  :output-contract (natp (f x y))
  (if (endp x)
    (if (equal y 0) 
      0
      (+ 1 (f x (- y 1))))
    (+ 1 (f (rest x) y))))

The measure is
(defunc m (x y)
  :input-contract (and (listp x) (natp y))
  :output-contract (natp (m x y))
  (+ (len x) y))


For the first recursive call in f, the propositional logic formalization 
for proving Condition 4 is:
(implies (and (listp x) (natp y) (endp x) (not (equal y 0)))
         (< (m x (- y 1)) (m x y)))

This can be rewritten as:
(implies (and (listp x) (natp y) (endp x) (> y 0))
         (< (m x (- y 1)) (m x y)))
         
Proof of Condition 4 for the first recursive call:
Context
C1. (listp x)
C2. (natp y)
C3. (endp x)
C4. (> y 0)

(m x (- y 1))
= { Def m, C3, Def len, Arithmetic }
(- y 1)
< { Arithmetic }
y
= { Def m, C3, Def. len, Arithmetic }
(m x y)

The propositional logic formalization for Proof of Condition 4 for the 
second recursive call:
(implies (and (listp x) (natp y)(not (endp x)))
         (< (m (rest x) y) (m x y)))

Proof:
C1. (listp x)
C2. (natp y)
C3. (not (endp x))

(m (rest x) y)
= { Def m, C3 }
(+ (len (rest x)) y)
< { Arithmetic, Decreasing len axiom }
(+ (len x) y)
= { Def m }
(m x y)

Hence f terminates, and m is a measure function for it.
QED


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

23. Prove f23 terminates:

(defunc f23 (x y c)
  :input-contract (and (natp x) (posp y) (integerp c))
  :output-contract (integerp (f23 x y c))
  (cond ((and (equal x 0) (equal y 1)) c)
        ((> x 0)                       (f23 (- x 1) y (+ c 1)))
        (t                             (f23 5 (- y 1) c))))

For this question, we are providing a measure function:

(defunc m23 (x y c)
  :input-contract (and (natp x) (posp y) (integerp c))
  :output-contract (natp (m23 x y c))
  (+ x (* 6 y)))

For this question, we are also providing the propositional logic formalization 
for Proof of Condition 4.

For the first recursive call, we have:
(implies (and (natp x) (posp y) (integerp c) 
              (or (not (equal x 0)) (not (equal y 1)))
              (> x 0))
         (< (m23 (- x 1) y (+ c 1)) (m23 x y c))
Now prove the above using equational reasoning

..........



For the second recursive call, we have:
(implies (and (natp x) (posp y) (integerp c) 
              (or (not (equal x 0)) (not (equal y 1))) 
              (not (> x 0)))
         (< (m23 5 (- y 1) c) (m23 x y c))
Now prove the above using equational reasoning

.........

|#
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Feedback (5 points)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|

Each week we will ask a couple questions to monitor how the course
is progressing.  This should be the same length as the HW07 survey. 

Please fill out the following form.

https://goo.gl/forms/SvvGaynGyjVEhV3i1

As before, feedback is anonymous and each team member should fill out
the form (only once per person).

After you fill out the form, write your name below in this file, not
on the questionnaire. We have no way of checking if you submitted the
file, but by writing your name below you are claiming that you did,
and we'll take your word for it.  

5 points will be awarded to each team member for filling out the 
questionnaire.

The following team members filled out the feedback survey provided by 
the link above:
---------------------------------------------
<firstname> <LastName>
<firstname> <LastName>

|#