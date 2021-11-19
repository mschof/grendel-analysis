import random
import sys
sys.setrecursionlimit(10000)

if len(sys.argv) != 7:
    print("Usage: <script> <n> <t> <d> <R_Full> <num_vars> <test_config>")
    print("test_config = 1 .. Grendel 1 (single variable, factorization)")
    print("test_config = 2 .. Grendel 2 (num_vars > 1 variables, Gröbner basis)")
    exit()

n = int(sys.argv[1])
t = int(sys.argv[2])
d = int(sys.argv[3])
R_num = int(sys.argv[4])
num_vars = int(sys.argv[5])
test_config = int(sys.argv[6])

if test_config not in [1, 2]:
    print("No such config found.")
    exit()

only_d_reg = True
gb_print_prot = False

def reset_seed(random_seed):
    set_random_seed(random_seed)
    random.seed(random_seed)

def get_prime(bit_length, d):
    while True:
        p = random_prime((2^bit_length) - 1, false, 2^(bit_length - 1))
        if gcd(p - 1, d) == 1:
            return p

def find_inverse(d, prime):
    counter = 1
    while True:
        if ((counter * int(prime) - (counter - 1)) / d) == ((counter * int(prime) - (counter - 1)) // d):
            return ((counter * prime - (counter - 1)) // d)
        counter += 1

prime = get_prime(n, d)
d_inv = find_inverse(d, prime)
print("Prime:", prime)
print("Params: n=%d, t=%d, d=%d, R=%d, num_vars=%d, test_config=%d"%(n, t, d, R_num, num_vars, test_config))
F = GF(prime)
# variables = ['x_'+str(i+1) for i in range(0, t)]
variables = ['x_'+str(i+1) for i in range(0, num_vars)]
R = PolynomialRing(F, names=variables)
R.inject_variables()
reduction_equations = [var^(prime) - var for var in R.gens()]
reduction_ideal = Ideal(reduction_equations)

MS = MatrixSpace(F, t, t)
VS = VectorSpace(F, t)

def generate_matrix():
    M = MS.random_element()
    if (0 in list(M)) or M.is_invertible() == False:
        M = MS.random_element()
    return M

def legendre_symbol(value):
    return value^((prime-1)/2)

def extract_guesses(permutation_guess, number_single_guesses):
    single_guesses = []
    for i in range(0, number_single_guesses):
        guess_intermediate = (permutation_guess >> i) & 0b1
        guess_converted = (guess_intermediate * 1) + ((guess_intermediate - 1) * 1)
        single_guesses.append(guess_converted)
    return single_guesses

def permutation(state, linear_layer, round_constants):

    reset_seed(0)

    new_state = list(state)

    for i in range(0, R_num):

        # Nonlinear layer with Legendre symbols
        for j in range(0, t):
            # if i > 0:
            #     print("Legendre symbol:", legendre_symbol(new_state[j]))
            new_state[j] = new_state[j]^d * legendre_symbol(new_state[j])

        # Linear layer (matrix multiplication)
        new_state = list(linear_layer * vector(new_state))

        # Round constants
        for j in range(0, t):
            new_state[j] = new_state[j] + round_constants[(i*t) + j]

    return new_state

# Setup
state = [F.random_element() for i in range(0, t)]
linear_layer = generate_matrix()
round_constants = [F.random_element() for i in range(0, R_num * t)]
output_state = permutation(state, linear_layer, round_constants)
print(output_state)

# Guesses (1 or -1, ignore 0 due to low probability)
# 1 or -1, ignore 0 due to low probability
# num_vars guesses for first round, t guesses for other rounds
# -> num_vars + t*(R_num-1) guesses in total
# Use z-bit number with z = (num_vars + t*(R_num-1)) bits, current guess is
# bit at position b: (b*1) + ((b-1)*1) -> if b = 0: guess is -1, if b = 1: guess is 1
# after each permutation: increase counter by 1 (until 2^z - 1)
number_single_guesses = num_vars + t*(R_num-1)
guess_limit = 2^number_single_guesses
success_combinations = []

if test_config == 1:
    print("--- Root-finding attack with a single variable (preimage) ---")
elif test_config == 2:
    print("--- Attack with a multiple variables (preimage) ---")


for permutation_guess in range(0, guess_limit):
    reset_seed(0)
    state = [R.gens()[i] for i in range(0, num_vars)] + [F(0) for i in range(0, t-num_vars)]
    equations = [0] * num_vars
    new_state = list(state)

    single_guesses = extract_guesses(permutation_guess, number_single_guesses)

    # Build equation system for guess covering whole permutation
    # First round (guess for vars, compute for others)
    for j in range(0, num_vars):
        new_state[j] = new_state[j]^d * single_guesses[j]

    for j in range(num_vars, t):
        new_state[j] = new_state[j]^d * legendre_symbol(new_state[j])

    # Linear layer
    new_state = list(linear_layer * vector(new_state))

    # Round constants
    for j in range(0, t):
        new_state[j] = new_state[j] + round_constants[j]

    # Remaining rounds
    for i in range(1, R_num):

        for j in range(0, t):
            new_state[j] = new_state[j]^d * single_guesses[(num_vars + (i-1) * t) + j]

        # Linear layer
        new_state = list(linear_layer * vector(new_state))

        # Round constants
        for j in range(0, t):
            new_state[j] = new_state[j] + round_constants[(i*t) + j]
    

    # Build equations system
    for i in range(0, num_vars):
        equations[i] = new_state[i]

    ###
    ### Root-finding attack with single variable (preimage)
    ###
    if test_config == 1:
        print("--- Start solving ---")
        # Get solutions
        t_ = walltime()
        roots = equations[0].roots()
        print("Solution time: {t_:5.2f}s".format(t_=walltime(t_)))
        #print("Univariate equation degree:", equations[0].degree())
        solutions = [sol[0] for sol in roots]

        # Try if it works
        for sol in solutions:
            new_state = [F(sol)] + [F(0)] * (t - 1)
            output_state = permutation(new_state, linear_layer, round_constants)
            if output_state[0] == F(0):
                success_combinations.append([new_state, single_guesses])

    ###
    ### Attack with multiple variables (preimage)
    ###
    elif test_config == 2:
        if only_d_reg == False:
            print("--- Start solving ---")
            t_ = walltime()
            I = R.ideal(equations)
            gb = I.groebner_basis(algorithm="singular:slimgb")
            solutions = R.ideal(gb).variety()
            print("Solution time: {t_:5.2f}s".format(t_=walltime(t_)))
            #solutions = I.variety()
            if len(solutions) > 0:
                input_state = [solutions[0][R.gens()[i]] for i in range(0, num_vars)] + [F(0) for i in range(0, t-num_vars)]
                #print("input_state:", input_state)
                output_state = permutation(input_state, linear_layer, round_constants)
                #print("output_state:", output_state)
                all_zero = True
                for i in range(0, num_vars):
                    all_zero = all_zero and (output_state[i] == 0)
                if all_zero == True:
                    success_combinations.append([input_state, single_guesses])
        elif only_d_reg == True:
            print("--- GB computations ---")
            check_only_deg_bound = True
            d_reg_bound = 1
            dreg_estimate = 1 + sum([f.degree() for f in equations])
            I = R.ideal(equations)
            H = I.change_ring(R.change_ring(order="degrevlex")).gens()
            while True:
                t_ = walltime()
                gb = H.groebner_basis(deg_bound=d_reg_bound, algorithm="singular:slimgb", prot=gb_print_prot)
                print("GB time: {t_:5.1f}s".format(t_=walltime(t_)))
                #print("Max degree:", max_deg)
                print("deg_bound: {deg_bound}, is GB: {is_gb}".format(deg_bound=d_reg_bound, is_gb=gb.is_groebner()))
                if not gb.is_groebner():
                    print("Degree bound %d too low, output is not a Groebner basis."%d_reg_bound)
                    d_reg_bound += 1
                else:
                    print("Groebner basis found with d_reg bound %d"%d_reg_bound)
                    break
            print("H max degree:", H.maximal_degree())
            print("D_reg estimate:", dreg_estimate)
            gb_lex = Ideal(gb).transformed_basis('fglm') # Change ordering
            univariate = Sequence([f for f in gb_lex if f.is_univariate()])
            #print(univariate)
            univariate[0] = univariate[0].reduce(reduction_ideal)
            print("Univariate degree:", univariate[0].degree())
            Q = PolynomialRing(F, univariate[0].variables()[0])
            sols = [el[0] for el in set(Q(univariate[0]).roots(ring=F))]
            # print("Groebner basis (lex):", gb_lex)
            # print("Univariate:", univariate)
            # print("Solutions:", sols)
            if check_only_deg_bound == True:
                exit()

print("Success combinations:", success_combinations)

for comb in success_combinations:
    input_state = comb[0]
    output_state = permutation(input_state, linear_layer, round_constants)
    print(output_state)
