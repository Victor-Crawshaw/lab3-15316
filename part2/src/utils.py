import pca_logic as pca

# Counter to generate fresh variables
count = 0

def fresh_var(x: pca.Variable) -> pca.Variable:
    global count
    x_prime_id = f"{x.id}'{count}"
    count += 1
    return pca.Variable(x_prime_id)

def eq_term(s: pca.Term, t: pca.Term) -> bool:
    # Both terms must be of the same type (Variable or Constant)
    if type(s) != type(t):
        return False
    
    # Compare IDs for variables or names for constants
    if isinstance(s, pca.Variable):
        return s.id == t.id
    else:  # Constant
        return s.name == t.name

def eq_form(p: pca.Form, q: pca.Form) -> bool:
    # Must be same type of formula
    if type(p) != type(q):
        return False
    
    if isinstance(p, pca.Atom):
        return (eq_term(p.predicate, q.predicate) and 
                len(p.terms) == len(q.terms) and
                all(eq_term(s, t) for s, t in zip(p.terms, q.terms)))
    
    elif isinstance(p, pca.Implies):
        return eq_form(p.premise, q.premise) and eq_form(p.conclusion, q.conclusion)
    
    elif isinstance(p, pca.Says):
        return eq_term(p.agent, q.agent) and eq_form(p.formula, q.formula)
    
    elif isinstance(p, pca.Forall):
        return eq_term(p.variable, q.variable) and eq_form(p.formula, q.formula)
    
    return False

def subst_form(x: pca.Variable, t: pca.Term, p: pca.Form) -> pca.Form:
    def subst_term(term: pca.Term) -> pca.Term:
        if isinstance(term, pca.Variable) and term.id == x.id:
            return t
        return term
    
    if isinstance(p, pca.Atom):
        return pca.Atom(
            predicate=p.predicate, 
            terms=[subst_term(term) for term in p.terms]
        )
    
    elif isinstance(p, pca.Implies):
        return pca.Implies(
            premise=subst_form(x, t, p.premise),
            conclusion=subst_form(x, t, p.conclusion)
        )
    
    elif isinstance(p, pca.Says):
        return pca.Says(
            agent=subst_term(p.agent),
            formula=subst_form(x, t, p.formula)
        )
    
    elif isinstance(p, pca.Forall):
        # Don't substitute if the variable is bound by this quantifier
        if eq_term(p.variable, x):
            return p
        return pca.Forall(
            variable=p.variable,
            formula=subst_form(x, t, p.formula)
        )
    
    return p
