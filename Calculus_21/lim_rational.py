import sys, json, sympy

def sympy_to_lean(expr):
    expr = sympy.nsimplify(expr)
    s = str(expr).replace('**', '^')
    return s

def solve_limit(num_str, den_str, x0_str):

    x = sympy.Symbol('x')
    num = sympy.sympify(num_str.replace('^', '**'))
    den = sympy.sympify(den_str.replace('^', '**'))
    x0 = sympy.sympify(x0_str)
    t = sympy.Symbol('t')
    num_t = sympy.expand(num.subs(x, t + x0))
    den_t = sympy.expand(den.subs(x, t + x0))

    def get_lowest_power(poly_t):
        if poly_t == 0:
            return float('inf')
        poly = sympy.Poly(poly_t, t)
        if poly.is_zero:
            return float('inf')
        return min([monom[0] for monom in poly.monoms()])

    k_num = get_lowest_power(num_t)
    k_den = get_lowest_power(den_t)

    if k_den > k_num:
        num_rem_t = sympy.simplify(num_t / (t**k_num))
        den_rem_t = sympy.simplify(den_t / (t**k_den))
    else:
        num_rem_t = sympy.simplify(num_t / (t**k_den))
        den_rem_t = sympy.simplify(den_t / (t**k_den))

    p_x = num_rem_t.subs(t, x - x0)
    q_x = den_rem_t.subs(t, x - x0)
    is_divergent = bool(k_den > k_num)
    m_val = int(k_den - k_num) if is_divergent else 0
    k_val = int(min(k_num, k_den))

    result = {
        "is_divergent": is_divergent,
        "p": sympy_to_lean(p_x),
        "q": sympy_to_lean(q_x),
        "k": k_val,
        "m": m_val
    }
    print(json.dumps(result))

if __name__ == "__main__":
    solve_limit(sys.argv[1], sys.argv[2], sys.argv[3])
