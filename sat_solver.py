import itertools
import copy
import time

def load_dimacs(filename):
    file = open(filename, 'r')
    C_set = []
    temp = []
    for x in file:
        if x[0].isalpha():
            continue
        l = x.strip("\n")
        f = False
        temp = []
        n = ""
        for y in l:
            if y == ' ':
                temp.append(int(n))
                n = ""
            else:
                n += y
        C_set.append(temp)
    return C_set

def high_var(C_set):
    temp = 0
    for x in C_set:
        for y in x:
            if abs(y)> temp:
                temp = abs(y)
    return temp

def simple_sat_solve(clause_set):
    h = high_var(clause_set)
    lits = [x for x in range(1,h+1)]
    digs = ["".join(seq) for seq in itertools.product("01", repeat=h+1)]

    for x in digs:
        TA = lits.copy()
        for y in range(0,len(TA)):
            if x[y] == "0":
                TA[y] = TA[y] * -1
        b_ok = True
        for clause in clause_set:
            ok = False
            for l in clause:
                if l == TA[abs(l)-1]:
                    ok = True
                    break
            if not ok:
                b_ok = False
                break
            else:
                b_ok = True
        if b_ok:
            return TA
        else:
            continue
    return False

def sat_test(clause_set, partial_assignment):
    if partial_assignment == False:
        return False
    b_ok = True
    for clause in clause_set:
        ok = False
        for l in clause:
            if l == partial_assignment[abs(l)-1]:
                ok = True
                break
        if not ok:
            b_ok = False
            break
        else:
            b_ok = True
    if b_ok:
        return True
    else:
        return False

def f_zero(assignment):
    for x in range(0,len(assignment)):
        if assignment[x] == 0:
            return x
    return -1

def p_ass(clause_set, pa):
    h = high_var(clause_set)
    new = [0 for i in range(0,h)]
    for x in pa:
        new[abs(x)-1] = x
    return new

def branching_sat_solve(clause_set, partial_assignment=[], first=True):
    
    if first == True:
        partial_assignment = p_ass(clause_set, partial_assignment)
        first = False

    loc = f_zero(partial_assignment)
    
    if loc < 0:
        if sat_test(clause_set, partial_assignment):
            return partial_assignment
        else:
            return False
        
    else:
        for val in [loc+1, -1*(loc+1)]:
            partial_assignment[loc] = val
            gug = branching_sat_solve(clause_set, partial_assignment)
            if type(gug) is not bool:
                return gug

        return False

def dpll_unit_propagate(next_set, pa, first = True, strip_set = []):
    
    if first:
        strip_set = [x for x in pa if x != 0]
        first = False
    n_strip_set = []
    clause_set = []  
    
    for stripper in strip_set:
        for clause in next_set:
            for literal in clause:
                if literal == stripper:
                    clause_set.append(clause)
                    break
                elif abs(literal) == abs(stripper):
                    clause.remove(literal)
                    if len(clause) == 1:
                        n_strip_set.append(clause[0])
                        clause_set.append(clause)
            
    for clause in clause_set:
        if clause in next_set:
            next_set.remove(clause)              
    if n_strip_set:
        p_set = strip_set + list(set(n_strip_set) - set(strip_set))
        return dpll_unit_propagate(next_set, pa, first, p_set)
    else:
        for x in strip_set:
            pop = x
            if (pop*-1) in strip_set:
                return [[]], [0]
            else:
                pa[abs(pop)-1] = pop
                next_set.append([pop])
        
        return next_set, pa
        
def normalise(clause_set):
    n_clause_set = []
    for clause in clause_set:
        
        n_clause_set.append(list(set(clause)))

    return n_clause_set
                                          
def pure_literal_elimination(clause_set, pa):
    seen = []
    fin = []
    ret_c_set = []
    c_fin = []
    flag = False
    for x in clause_set:
        for y in x:
            if y not in seen:
                seen.append(y)
    seen = [abs(x) for x in seen]
    dupes = {i:seen.count(i) for i in seen}
    
    for key in dupes.keys():
        if dupes[key] == 1:
            fin.append(key)
    
    for clause in clause_set:
        for l in clause:
            if abs(l) in fin:
                pa[abs(l)-1] = l
                if l not in c_fin:
                    c_fin.append([l])
                flag = True
                continue
        if flag:
            flag = False
            continue
        ret_c_set.append(clause)
    for x in clause_set:
        if len(x) == 1:                
            ret_c_set.append(x)

    for unit in c_fin:
        if unit not in ret_c_set:
            ret_c_set.append(unit)

    return ret_c_set, pa

def dpll_sat_solve(clause_set, partial_assignment = [], first = True):
    if first:
        clause_set = normalise(clause_set)
        for l in partial_assignment:
            clause_set.append([l])
        partial_assignment = p_ass(clause_set, partial_assignment)

        first = False

    clause_set, partial_assignment = dpll_unit_propagate(clause_set, partial_assignment)

    loc = f_zero(partial_assignment)

    for c in clause_set:
        if c == []:
            return False
        
    if loc < 0:
        return partial_assignment


    for val in [loc+1, -1*(loc+1)]:
        p = copy.deepcopy(clause_set)
        p.append([val])
        partial_assignment[loc] = val
        temp_pa = copy.copy(partial_assignment)
        valid_check = dpll_sat_solve(p, temp_pa, first)
        if type(valid_check) is not bool:
            return valid_check
        
    return False

def unit_propagate(next_set, first = True, strip_set = []):
    if first:
        strip_set = [x[0] for x in next_set if len(x) == 1]
        first = False
    n_strip_set = []
    clause_set = []  
    
    for stripper in strip_set:
        for clause in next_set:
            for literal in clause:
                if literal == stripper:
                    clause_set.append(clause)
                    break
                elif abs(literal) == abs(stripper):
                    clause.remove(literal)
                    if len(clause) == 1:
                        n_strip_set.append(clause[0])
                        clause_set.append(clause)
            
    for clause in clause_set:
        if clause in next_set:
            next_set.remove(clause)              
    if n_strip_set:
        p_set = strip_set + list(set(n_strip_set) - set(strip_set))
        return unit_propagate(next_set, first, p_set)
    else:
        return next_set

file = load_dimacs("8queens.txt")
start = time.time()
retval = dpll_sat_solve(file)
print(time.time() - start)
print(retval)
print(sat_test(file, retval))