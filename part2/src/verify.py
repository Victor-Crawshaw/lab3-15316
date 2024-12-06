from typing import Optional, Set
import pca_logic as pca
from utils import eq_form, eq_term, subst_form

class VerifyException(Exception):
    """
    Exception raised during verification errors.

    Args:
        message (str): The error message describing the issue.
    """
    def __init__(self, message: str):
        super().__init__(message)
        self.message = message


def check_policy(gamma: pca.Policy):
    """
    Checks if the given policy `gamma` is well-formed.

    Args:
        gamma (Policy): The policy to check.

    Raises:
        VerifyException: If `gamma` is not a well-formed policy.
    """
    seen_vars = set()
    
    for decl in gamma:
        # Check for duplicate variables
        if decl.constant.name in seen_vars:
            raise VerifyException(f"Duplicate variable {decl.constant.name} in policy")
        seen_vars.add(decl.constant.name)
        
        # Check quantification of variables
        bound_vars: Set[str] = set()
        def check_vars(form: pca.Form, bound: Set[str]):
            if isinstance(form, pca.Atom):
                if form.terms is not None:
                    for term in form.terms:
                        if isinstance(term, pca.Variable) and term.id not in bound:
                            raise VerifyException(f"Unbound variable {term.id}")
            elif isinstance(form, pca.Says):
                if isinstance(form.agent, pca.Variable) and form.agent.id not in bound:
                    raise VerifyException(f"Unbound variable {form.agent.id}")
                check_vars(form.formula, bound)
            elif isinstance(form, pca.Implies):
                check_vars(form.premise, bound)
                check_vars(form.conclusion, bound)
            elif isinstance(form, pca.Forall):
                if form.variable.id in bound:
                    raise VerifyException(f"Shadowed variable {form.variable.id}")
                bound.add(form.variable.id)
                check_vars(form.formula, bound)
        
        check_vars(decl.formula, bound_vars)


def verify(gamma: pca.Policy, m: pca.Proof, p: pca.Form):
    """
    Verifies that the judgment `gamma ⊢ m ⇐ p` holds.

    Args:
        gamma (Policy): The policy under which to verify the proof.
        m (Proof): The proof to verify.
        p (Form): The formula to verify.

    Raises:
        VerifyException: If the verification `gamma ⊢ m ⇐ p` fails.
    """
    def synth(gamma: pca.Policy, m: pca.Proof) -> pca.Form:
        """Synthesize the type of a proof (⇒ rules)"""
        if isinstance(m, pca.Pvar):
            # Find declaration in policy
            for decl in gamma:
                if decl.constant.name == m.name:
                    return decl.formula
            raise VerifyException(f"Undefined proof variable {m.name}")
        
        elif isinstance(m, pca.App):
            # →E rule
            p1 = synth(gamma, m.m1)
            if not isinstance(p1, pca.Implies):
                raise VerifyException("Application's first term must synthesize to implication")
            check(gamma, m.m2, p1.premise)
            return p1.conclusion
        
        elif isinstance(m, pca.Inst):
            # ∀E rule
            p1 = synth(gamma, m.m)
            if not isinstance(p1, pca.Forall):
                raise VerifyException("Instance's term must synthesize to universal")
            return subst_form(p1.variable, m.t, p1.formula)
        
        else:
            raise VerifyException(f"Cannot synthesize type for {type(m)}")
    
    def check(gamma: pca.Policy, m: pca.Proof, p: pca.Form):
        """Check if a proof matches a type (⇐ rules)"""

        if isinstance(m, pca.LetWrap) and isinstance(p, pca.Affirms):
            # saysE rule
            p1 = synth(gamma, m.m)
            if not isinstance(p1, pca.Says):
                raise VerifyException("Let wrap's first term must synthesize to says")
            # Add the unwrapped formula to context and check the body
            new_decl = pca.Declaration(constant=pca.Constant(m.v.name), formula=p1.formula)
            check(gamma + [new_decl], m.n, p)

        elif isinstance(m, pca.Let):
            # cut rule
            p1 = synth(gamma, m.m)
            new_decl = pca.Declaration(constant=pca.Constant(m.v.name), formula=p1)
            check(gamma + [new_decl], m.n, p)

        elif isinstance(p, pca.Affirms):
            # aff rule
            check(gamma, m, p.formula)
        
            
        elif isinstance(m, pca.Wrap):
            # saysR rule
            if not isinstance(p, pca.Says):
                raise VerifyException("Wrap must check against says type")
            if not eq_term(p.agent, m.a):
                raise VerifyException(f"Agent mismatch: expected {m.a}, got {p.agent}")
            new_aff = pca.Affirms(agent=p.agent, formula=p.formula)
            check(gamma, m.m, new_aff)
        
        elif isinstance(m, pca.LetWrap):
            raise VerifyException("Let without affirmations")
         
        else:
            # ⇒/⇐ rule
            p1 = synth(gamma, m)
            if not eq_form(p1, p):
                raise VerifyException(f"Type mismatch: expected {p}, got {p1}")
                
    check_policy(gamma)
    check(gamma, m, p)
    