"""Independent high-precision binomial-tail audit of the fixed full-count interval.

Uses a discrete binomial recurrence, not the legacy incomplete-beta evaluator.
Exact candidate integers and an explicit deterministic ending allowance enter
only after quantile enclosure. See docs/jcsa-20261122.md.
"""
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction
from functools import lru_cache
from math import factorial

PRECISION=90
TAIL_GUARD=Decimal('1e-45')
SUM_TOLERANCE=Decimal('1e-48')
# At these <= 10^165 state counts, 90-digit arithmetic error is far below this.
COUNT_GUARD=10**100


@lru_cache(None)
def bernoulli(n):
    a=[]
    for m in range(n+1):
        a.append(Fraction(1,m+1))
        for j in range(m,0,-1):a[j-1]=j*(a[j-1]-a[j])
    return a[0]


@lru_cache(None)
def log_factorial(n):
    with localcontext() as ctx:
        ctx.prec=PRECISION
        if n<512:
            return Decimal(factorial(n)).ln()
        z=Decimal(n+1)
        # Decimal pi with >90 correct digits; only log(2*pi)/2 is required.
        pi=Decimal('3.1415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679')
        value=(z-Decimal('.5'))*z.ln()-z+(2*pi).ln()/2
        for k in range(1,21):
            b=bernoulli(2*k)
            value+=Decimal(b.numerator)/Decimal(b.denominator)/(2*k*(2*k-1)*z**(2*k-1))
        return +value


def tail_enclosure(c,n,p):
    """Pr[Bin(n,p)>=c], enclosed by a truncated sum plus geometric remainder.

    For inversion p<=c/n, successive mass ratios are <1 and decrease. The small
    guard covers high-precision roundoff/Stirling error, not statistical error.
    """
    with localcontext() as ctx:
        ctx.prec=PRECISION
        p=Decimal(p)
        if c==0 or p==1:return Decimal(1),Decimal(1)
        if p==0:return Decimal(0),Decimal(0)
        if not 0<c<=n or not 0<p<=Decimal(c)/n:
            raise ValueError('tail inversion requires 0<c<=n and 0<p<=c/n')
        mass=(log_factorial(n)-log_factorial(c)-log_factorial(n-c)
              +c*p.ln()+(n-c)*(1-p).ln()).exp()
        total=Decimal(0);k=c
        while True:
            total+=mass
            if k==n:
                remainder=Decimal(0);break
            ratio=Decimal(n-k)/(k+1)*p/(1-p)
            if not ratio<1:raise ArithmeticError('binomial masses must decrease above c')
            remainder=mass*ratio/(1-ratio)
            if remainder<SUM_TOLERANCE:break
            mass*=ratio;k+=1
        return max(Decimal(0),total-TAIL_GUARD),min(Decimal(1),total+remainder+TAIL_GUARD)


@lru_cache(None)
def lower_enclosure(c,n,tail=Decimal('.0003375'),bits=68):
    if not isinstance(c,int) or not isinstance(n,int) or not 0<=c<=n or not 1<=n<=10**9:
        raise ValueError('invalid binomial counts')
    with localcontext() as ctx:
        ctx.prec=PRECISION
        tail=Decimal(tail)
        if not 0<tail<Decimal('.5'):raise ValueError('invalid tail probability')
        if c==0:return Decimal(0),Decimal(0)
        if c==n:
            q=(tail.ln()/n).exp()
            return max(Decimal(0),q-TAIL_GUARD),min(Decimal(1),q+TAIL_GUARD)
        lo,hi=Decimal(0),Decimal(c)/n
        for _ in range(bits):
            mid=(lo+hi)/2
            low,high=tail_enclosure(c,n,mid)
            if high<tail:lo=mid
            elif low>tail:hi=mid
            else:break
        return lo,hi


def significant_key(value,digits=3):
    """Round a nonnegative integer half up, using integers only."""
    if not isinstance(value,int) or value<0 or not isinstance(digits,int) or digits<1:raise ValueError('invalid rounding input')
    unit=10**max(0,len(str(value))-digits)
    return ((value+unit//2)//unit)*unit


def significant_text(value,digits=3):
    rounded=significant_key(value,digits)
    if rounded==0:return '0'
    text=str(rounded);head=text[:digits].ljust(digits,'0')
    return head[0]+('.'+head[1:] if digits>1 else '')+'e'+str(len(text)-1)


def bracket(counts,cn,ct,alpha=Decimal('.0027'),ending_allowance=0,tail_allocations=None):
    if not all(isinstance(x,int) and 0<=x<10**166 for x in (cn,ct,ending_allowance)):
        raise ValueError('counts must be nonnegative integers below arithmetic guard scale')
    with localcontext() as ctx:
        ctx.prec=PRECISION
        alpha=Decimal(str(alpha))
        tails={s:alpha/8 for s in ('nonterm','flagsj','term','static_mu')}
        if tail_allocations is not None:
            if set(tail_allocations)!=set(tails):raise ValueError('four tail allocations required')
            tails={s:Decimal(str(v)) for s,v in tail_allocations.items()}
            if any(not 0<v<Decimal('.5') for v in tails.values()) or 2*sum(tails.values())>alpha:
                raise ValueError('invalid or overspent one-look alpha budget')
        from plan.allcp_bracket import K_JCSA_1,N_K
        ml=lower_enclosure(K_JCSA_1,N_K,tails['static_mu'])[0]
        mh=1-lower_enclosure(N_K-K_JCSA_1,N_K,tails['static_mu'])[0]
        terms={};quantiles={}
        for s in ('nonterm','flagsj','term'):
            row=counts[s]
            if set(row)-{'certified','unreachable','unresolved'}:raise ValueError('unknown outcome')
            if any(not isinstance(v,int) or v<0 for v in row.values()):raise ValueError('invalid outcome count')
            n=sum(row.values())
            cl,ch=lower_enclosure(row.get('certified',0),n,tails[s])
            rl,rh=lower_enclosure(row.get('unreachable',0),n,tails[s])
            wl,wh=(Decimal(cn),Decimal(cn)) if s=='nonterm' else ((Decimal(ct),Decimal(ct)) if s=='term' else (cn*ml,cn*mh))
            terms[s]=(wl*cl,wh*(1-rl))
            quantiles[s]=dict(cert_lower=[str(cl),str(ch)],refutation_lower=[str(rl),str(rh)])
        lower=max(Decimal(0),sum(t[0] for t in terms.values())-ending_allowance-COUNT_GUARD)
        upper=sum(t[1] for t in terms.values())+ending_allowance+COUNT_GUARD
        lo=int(lower.to_integral_value(rounding=ROUND_FLOOR))
        hi=int(upper.to_integral_value(rounding=ROUND_CEILING))
        return dict(lower_integer=str(lo),upper_integer=str(hi),
                    interval_scaled_1e164=[str(Decimal(lo)/10**164),str(Decimal(hi)/10**164)],
                    terms_scaled_1e164={s:[str(v/10**164) for v in t] for s,t in terms.items()},
                    cp_quantile_enclosures=quantiles,static_mu_interval=[str(ml),str(mh)],
                    ending_allowance=str(ending_allowance),arithmetic_count_guard=str(COUNT_GUARD),
                    alpha=str(alpha),tail_allocations={s:str(v) for s,v in tails.items()},
                    three_digits=significant_text(lo) if significant_key(lo)==significant_key(hi) else None,
                    precision=PRECISION,quantile_bisections=68,
                    method='independent Decimal discrete binomial tail, geometric remainder and explicit numerical guards')
