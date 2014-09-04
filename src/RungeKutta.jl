module RungeKutta

using DataStructures

export make_rkfe, show_rkfe,
       make_rk3, show_rk3,
       make_rk4a, show_rk4a,
       make_rk4b, show_rk4b
       

##
## Runge-Kutta integration of ODEs
## Based on Haskell code by Uwe Hollerbach <uh@alumni.caltech.edu>
##
## dy
## -- = f(t, y)
## dt
##
## y_{n+1} = y_n + h sum_{i=1}^s b_i k_i
## k_i = f(t_n + c_i h, y_n + h sum_{j=1}^s a_{ij} k_j)
##
## "Butcher Tableau" is
##
## c_1  a_11 a_12 ... a_1s
## c_2  a_21 a_22 ... a_2s
## ...  ...
## c_s  a_s1 a_s2 ... a_ss
##      b_1  b_2  ... b_s
##
## This module implements a method that can do a generic tableau, then
## specializes with different tableaux to let the user pick a specific
## method. Adaptive step-size methods, see below, add a row of d_j
## coefficients and use that to report the error:
##
## e_{n+1} = h sum_{i=1}^s d_i k_i
##
## non-adaptive solvers:
##	rkfe, rk3, rk4a, rk4b
##
## adaptive solvers:
##	rkhe, rkbs, rkf45, rkck, rkdp, rkf78, rkv65
##
## auxiliary non-adaptive solvers (error estimators from the adaptive ones):
##	rkhe_aux, rkbs_aux, rkf45_aux, rkck_aux, rkdp_aux, rkf78_aux, rkv65_aux
##
## use rk4[ab] if you don't need an adaptive solver, rkdp or rkv65 if you do;
## or use what you need if you're an expert.
##
## DO NOT USE rkfe EXCEPT FOR DEMONSTRATIONS OF INSTABILITY!
## (Or if you're an expert.)
##
## Reference: E. Hairer, S. P. Norsett, G. Wanner,
## Solving Ordinary Differential Equations I: Nonstiff Problems
## (second revised edition, 1993).

function rat (n :: Int)
    Rational (n, 1)
end
    
function isempty (lst:: LinkedList{Rational{Int}})
    return isa (lst, Nil)
end

function isempty (lst:: LinkedList{Int})
    return isa (lst, Nil)
end

function isempty (lst:: LinkedList{Float64})
    return isa (lst, Nil)
end

function isempty (lst:: LinkedList{Any})
    return isa (lst, Nil)
end

function mapPartial(f::Base.Callable, l::Cons)
    first = f(l.head)
    l2 = (first == nothing) ? nil() : cons(first, nil(typeof(first)))
    for h in l.tail
        fh = f(h)
        if (!(fh == nothing))
            l2 = cons(fh, l2)
        end
    end
    reverse(l2)
end

function foldl (f,init,v)
    ax = init
    for x in v
        ax = f(x,ax)
    end
    return ax
end

function zip (l1 :: LinkedList, l2 :: LinkedList)
    cons ((head(l1),head(l2)),zip(tail(l1),tail(l2)))
end

function zip (l1 :: Nil, l2 :: Nil)
    nil()
end

function foldl1 (f, v)
    if isa (v, Cons)
        let h = head (v), t = tail (v)
            if isempty (t)
                h
            else
                foldl (f, f(h, head(t)), tail(t))
            end
        end
    else
        throw (DomainError ())
    end
end


function normalize (r)
    n = num(r)
    d = den(r)
    if (n == 0)
        return 0
    elseif (d == 1)
        return r
    else
        c = gcd (n,d)
        if (c == d)
            return div(n,c)
        else
            return (div (n,c)) // (div(d,c))
        end
    end
end


# Stores a vector of rational numbers as a common denominator, then a vector
# of numerators, all stored as doubles: this lets us write the values in
# the source as exact rational numbers, yet we can take advantage of not
# having to do too many conversions and also of not having to multiply
# by 0 or 1 in some cases.

type RCL
    den  :: Float64
    nums ::  Union (LinkedList{Float64}, Nil{Any})
end

function ratToRCL (rs :: Nil{Any})
    return RCL(1.0, nil())
end

function ratToRCL (rs:: Cons{Rational{Int}})
    ds = map (den, rs)
    dp = foldl1 (*, ds)
    ns = map (x -> num (dp * x), rs)
    g  = foldl (gcd, dp, ns)
    return RCL(float64(dp / g), map (x -> float64 (x / g),  ns))
end

function ratToRCLs (x)
    map (ratToRCL, x)
end


function ratToReals (x:: LinkedList{Rational{Int}})
    map (float64, x)
end



##   A helper function to take the difference of two arrays of
##   rationals: we don't want to use (-) or (.-) because that requires
##   the array to be of the same size.  We want implicit zeros at the
##   end, as far as is necessary.
            
        
## fun diffs ([], []) = []
##  | diffs (xs, []) = xs
##  | diffs ([], xs) = map negate xs
##  | diffs (x::xs, y::ys) = (x +/ (negate y)) :: (diffs (xs,ys))

# Helper function to sum a list of K_i, skipping unnecessary
# multiplications

function m_scale (sc_fn)
    (sv) ->
    begin
        (sv[1] == 0.0) ? Nothing() : sc_fn (sv[1],sv[2])
    end
end

function m_sum (sum_fn)
    (x,ax) -> (x == nothing) ? ax : sum_fn (x,ax)
end    

# Helper function to generate a list of K_i 

function k_sum (sc_fn, sum_fn, h)
    f = ((rcl, ks) ->
         begin
             d     = rcl.den
             ns    = rcl.nums
             ns_ks = zip (ns, ks)
             return sc_fn (h / d, foldl1 (m_sum (sum_fn), mapPartial (m_scale (sc_fn), ns_ks)))
         end)
    return f
end


function gen_ks (ksum_fn,sum_fn,der_fn,h,old,cs,ar)
    (tn,yn) = old
    ks1 = nil()
    yn1 = yn
    for (a,c) in zip (ar,cs)
        yn1 = isempty (ks1) ? yn : sum_fn (yn, ksum_fn (a,ks1))
        v   = der_fn (tn + c*h, yn1)
        ks1 = cat(ks1, list(v))
    end
    return ks1
end



## This is the first core routine.
##
## Its arguments are:
##
##   c table (specified internally)
##   a table (specified internally)
##   b table (specified internally)
##
## user-specified arguments:
##
##   scale function to scale a Y state vector ::
##      (real * a -> a)
##
##   sum function to add two Y state vectors ::
##      (a * a -> a)
##
##   derivative function F ::
##      (real * a -> a)
##
##   step size H ::
##      real
##
##   current state (T,Y) ::
##      (real, a)
##
##   and the return value is the new state Y_new


    
function core1 (cl, al, bl)
    f = ((sc_fn, sum_fn, der_fn) ->
         ((h) -> 
          ((tn,yn) ->
           begin
               ksum = k_sum (sc_fn,sum_fn,h)
               ks = gen_ks (ksum, sum_fn, der_fn, h, (tn,yn), cl, al)
               return sum_fn (yn, ksum (bl, ks))
           end)))
    return f
end

function core2 (cl, al, bl, dk)
    f = ((sc_fn, sum_fn, der_fn) ->
         ((h) -> 
          begin
              ksum = k_sum (sc_fn,sum_fn,h)
              ((old) ->
               begin
                   ks   = gen_ks (ksum, sum_fn, der_fn, h, old, cl, al)
                   return (sum_fn (yn, ksum (bl, ks)), ksum (dl, ks))
               end)
          end))
    
    return f
end

function list_show{T}(l::LinkedList{T},show,sep,startstr,endstr)
    if isa(l,Nil)
        if is(T,Any)
            "nil()"
        else
            string ("nil(", T, ")")
        end
    else
        string (startstr,
                head(l),
                sep,
                list_show(tail (l),show,sep,"",""),
                endstr)
    end
end

function def_list_show (show,xs)
    list_show (xs,show,",","[","]")
end
    
function rcl_show (rcl)
    d = rcl.den
    ns = rcl.nums
    string ("<", d, ", ", def_list_show (string,ns), ">")
end

function rk_show1 (title,cs,ar,bs)
    string (title, ":\ncs:\t", def_list_show (string,cs),
            "\nas:\t", list_show (ar,rcl_show,"\n\t","",""),
            "\nbs:\t", rcl_show (bs))
end

function rk_show2 (title,cs,ar,bs,ds) 
    string (title, ":\nds:\t", rcl_show (ds), 
            "\ncs:\t", def_list_show (string,cs),
            "\nbs:\t", rcl_show (bs),
            "\nas:\t", list_show (ar,rcl_show,"\n\t","","")) 
end

##   Some specific explicit methods, taken from
##   "List of Runge-Kutta methods" at Wikipedia

## forward Euler: unconditionally unstable: don't use this! 

cs_fe = ratToReals (list (rat (0)))
as_fe = ratToRCLs (list (list ()))
bs_fe = ratToRCL  (list (rat (1)))

make_rkfe = () -> core1 (cs_fe, as_fe, bs_fe)
show_rkfe = rk_show1 ("Forward Euler", cs_fe, as_fe, bs_fe)

## Kutta's third-order method: 

cs_rk3 = ratToReals (list (rat (0), 1//2, rat (1)))
as_rk3 = ratToRCLs (list (list (), list (1//2), list (rat (-1), rat (2))))
bs_rk3 = ratToRCL  (list (1//6, 2//3, 1//6))
make_rk3 = () -> core1 (cs_rk3, as_rk3, bs_rk3)
show_rk3 = rk_show1 ("Kutta's third-order method", cs_rk3, as_rk3, bs_rk3)

## Classic fourth-order method 

cs_rk4a = ratToReals (list (rat (0), 1//2, 1//2, rat (1)))
as_rk4a = ratToRCLs (list (list (), list (1//2), list (rat (0), 1//2), list (rat (0), rat (0), rat (1))))
bs_rk4a = ratToRCL  (list (1//6, 1//3, 1//3, 1//6))
make_rk4a = () -> core1 (cs_rk4a, as_rk4a, bs_rk4a)
show_rk4a = rk_show1 ("Classic fourth-order method", cs_rk4a, as_rk4a, bs_rk4a)

## Kutta's other fourth-order method... "The first [above] is more
## popular, the second is more precise." (Hairer, Norsett, Wanner)

cs_rk4b = ratToReals (list (rat (0), 1//3, 2//3, rat (1)))
as_rk4b = ratToRCLs (list (list (), list (1//3), list (-1//3, rat (1)), list (rat (1), rat (-1), rat (1))))
bs_rk4b = ratToRCL  (list (1//8, 3//8, 3//8, 1//8))
make_rk4b = () -> core1 (cs_rk4b, as_rk4b, bs_rk4b)
show_rk4b = rk_show1 ("Kutta's other classic fourth-order method", cs_rk4b, as_rk4b, bs_rk4b)

end # module
