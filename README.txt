computability in lean

notes:

/-
When registering a function as being primrec:
define:
c_f : the code of f
c_f_ev : proof that eval c_f = f
c_f_ev_pr : proof that eval c_f is prim

When registering a function on codes (g):
c_g : the function g from codes to codes
c_g_ev : proof that eval (c_g asd) has the intended behaviour
c_g_pr : proof that g itself is primrec
-/


