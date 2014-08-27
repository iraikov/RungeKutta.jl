using RungeKutta
using Base.Test


## Solves the test problem dy/dt = -t^3 y^3 
##
##   which has the exact solution y = 1/sqrt(C + t^4/2)
##   where C = 1/y_0^2 - t_0^4/2

summer = +
scaler = *

con = -0.4
deriv = (t,y) ->
begin
#    println (string("deriv: t = ", t, " y = ", y, " y' = ", con*y))
    con*y
end
t0 = 0.0
y0 = 1.75
exact = ((t) -> y0*exp(con*(t - t0)))


showst = ((t,y) -> string (y, "\t", (y - exact (t))))

function gen_soln1 (integrator,h,t,st)
    stn = st
    tn = t
    while tn < 5.0
        stn = integrator (tn,stn)
        tn  = tn+h
    end
    stn = integrator (tn,stn)
    tn  = tn+h
    println (showst (tn,stn))
end

function do_case1 (integrator, n)
    h = (n < 0) ? 2^(-n) : 0.5^(n)
    print (string (h, "\t\t"))
    gen_soln1 (integrator (h),h,t0,y0)
end

function solver1 (integrator,stats) 
    println (stats)
    println ("# step yf err")
    for h in { x - 2 for x = 0:14 }
        do_case1 (integrator (scaler,summer,deriv), h)
    end
    println ("# All done!")
    end

solver1 (make_rkfe(), show_rkfe)
solver1 (make_rk3(), show_rk3)
solver1 (make_rk4a(), show_rk4a)
solver1 (make_rk4b(), show_rk4b)
    

