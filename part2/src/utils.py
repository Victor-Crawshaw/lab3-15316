import pca_logic as pca

# Counter to generate fresh variables
count = 0

def fresh_var(x: pca.Variable) -> pca.Variable:
    """
    Generate a fresh variable with a unique name based on the input variable.
    
    Args:
        x (Variable): The base variable to create a fresh version of.
        
    Returns:
        Variable: A new variable with a unique name based on x.
    """
    global count
    x_prime_id = f"{x.id}'{count}"
    count += 1
    return pca.Variable(x_prime_id)

def eq_term(s: pca.Term, t: pca.Term) -> bool:
    """
    Check if two terms are equal.
    
    Args:
        s (Term): First term to compare.
        t (Term): Second term to compare.
        
    Returns:
        bool: True if the terms are equal, False otherwise.
    """
    if type(s) != type(t):
        return False
    
    if isinstance(s, pca.Variable):
        return s.id == t.id
    else:  # Constant
        return s.name == t.name

def eq_form(p: pca.Form, q: pca.Form) -> bool:
    """
    Check if two formulas are equal.
    
    Args:
        p (Form): First formula to compare.
        q (Form): Second formula to compare.
        
    Returns:
        bool: True if the formulas are equal, False otherwise.
    """
    if type(p) != type(q):
        return False
    
    if isinstance(p, pca.Atom):
        if not eq_term(p.predicate, q.predicate):
               return False
        if (p.terms is None and q.terms is not None) or (p.terms is not None and q.terms is None):
            return False
        if p.terms is None and q.terms is None:
            return True
        return (len(p.terms) == len(q.terms) and
                all(eq_term(s, t) for s, t in zip(p.terms, q.terms)))
    
    elif isinstance(p, pca.Implies):
        return eq_form(p.premise, q.premise) and eq_form(p.conclusion, q.conclusion)
    
    elif isinstance(p, pca.Says):
        return eq_term(p.agent, q.agent) and eq_form(p.formula, q.formula)
    
    elif isinstance(p, pca.Forall):
        return eq_term(p.variable, q.variable) and eq_form(p.formula, q.formula)
    
    return False

def subst_form(x: pca.Variable, t: pca.Term, p: pca.Form) -> pca.Form:
    """
    Substitute a term for a variable in a formula.
    
    Args:
        x (Variable): The variable to substitute.
        t (Term): The term to substitute with.
        p (Form): The formula to perform substitution in.
        
    Returns:
        Form: A new formula with all occurrences of x replaced by t.
    """
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
        if eq_term(p.variable, x):
            return p
        return pca.Forall(
            variable=p.variable,
            formula=subst_form(x, t, p.formula)
        )
    
    return p
    