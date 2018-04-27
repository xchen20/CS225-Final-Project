# CS225-Final-Project
<pre>
Exceptions—TAPL Chapter 14:
We will work with simply typed lambda
14.1 is about raising exceptions
14.2 is about handling exceptions
14.3 is about exceptions carrying values

We had done:
1.  Mainly working on chapter 14.1 and 14.2 with some add up from Chapter 9 (simply typed lambda), include defined expression and typing rules as follows.

-- Term (we called it expression as professor did)
       t :: = error            (run-time error)
               try t with t    (trap errors)

-- Step Rules (only show part of the rules)
      error t2   ->  error          (E-AppErr1)
      v1 error  ->  error          (E-AppErr2)
      try v1 with t2 -> v1       (E-TryV)
      try error with t2 -> t2    (E-TryError)
      and   (E-Try)

We combined the five rules show above with the three evaluation rules from the Chapter 9, each is  (E-App1), (E-App2) and (E-AppAbs), they are all list on figure 9-1 in textbook. They are all defined under the term 'application'
which from lambda calculus.

-- Typing Rules (only show part of the rules)
       Γ ⊢ error : T     (T-Error)
       and   (T-Try)

2. Write up a few test cases
3. We are currently still need more time to debug, there are some error in our codes, it cannot compile well currently.

We will do:
1. Continue wokring on Chapter 14.3 semantics implementation as we did in 14.1 and 14.2
2. Complete all the test cases and make sure they are compiling with no error before the deadline of the whole project.

If you would like to see more about the project, please take look at our proposal pdf file which also upload on this repository.
</pre>

