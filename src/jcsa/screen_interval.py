"""Simultaneous production-look bounds when N nonmembership is decomposed into two events."""
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, localcontext
from fractions import Fraction

from jcsa.decimal_bracket import COUNT_GUARD, PRECISION, bracket, lower_enclosure, significant_text
from jcsa.ending_allowance import allowance


CHEAP_N = 1_000_000
LATE_CHEAP_N = 4_000_000
FULL_N_LOOKS = (20_000, 40_000, 80_000, 160_000, 320_000)
SCREEN_TAIL = Decimal('.00020')
RESIDUAL_TAIL = Decimal('.00008')
SHARED_TAIL = Decimal('.00025')


def full_interval(screen_n, screen_excluded, full_n, residual_nonmembers, outside_unknown,
                  flag_counts, terminal_counts, cn, ct, *, two_screen_looks=False):
    """Combine disjoint N exclusions and the original F/T/static terms.

    Each value is a count in a fixed sample. A verified E exclusion can never
    be a residual nonmember. Every outside-E unknown can still be one.
    The same screen sample, F sample, T sample and static input are reused
    across the five registered N looks. The return value permits reporting
    each side convention on the same simultaneous coverage event.
    """
    if any(type(x) is not int for x in (screen_n, screen_excluded, full_n, residual_nonmembers, outside_unknown)):
        raise TypeError('screen and residual tallies must be integers')
    if not (0 <= screen_excluded <= screen_n and screen_n > 0 and 0 <= residual_nonmembers <= full_n and
            full_n > 0 and 0 <= outside_unknown <= full_n-residual_nonmembers):
        raise ValueError('impossible screen or residual tally')
    screen_looks = 2 if two_screen_looks else 1
    screen_tail = SCREEN_TAIL/screen_looks
    budget = 2*screen_looks*Fraction(screen_tail) + 2*len(FULL_N_LOOKS)*Fraction(RESIDUAL_TAIL) + 6*Fraction(SHARED_TAIL)
    if budget != Fraction(27,10_000):
        raise ValueError('production alpha allocation differs')
    # Ask bracket for its outward F, T and static products. Its ordinary N
    # term and its final allowance are ignored. The allowance is added below.
    other = bracket(dict(nonterm={'certified':1}, flagsj=flag_counts, term=terminal_counts),
                    cn, ct, tail_allocations=dict(nonterm=RESIDUAL_TAIL, flagsj=SHARED_TAIL,
                                                  term=SHARED_TAIL, static_mu=SHARED_TAIL))
    with localcontext() as ctx:
        ctx.prec = PRECISION
        e_lo = lower_enclosure(screen_excluded,screen_n,screen_tail)[0]
        e_hi = 1-lower_enclosure(screen_n-screen_excluded,screen_n,screen_tail)[0]
        d_lo = lower_enclosure(residual_nonmembers,full_n,RESIDUAL_TAIL)[0]
        d_hi = 1-lower_enclosure(full_n-residual_nonmembers-outside_unknown,full_n,RESIDUAL_TAIL)[0]
        n_lo = max(Decimal(0), 1-e_hi-d_hi)
        n_hi = max(Decimal(0), 1-e_lo-d_lo)
        terms = other['terms_scaled_1e164']
        scale = 10**164
        rest = [sum(Decimal(terms[s][i])*scale for s in ('flagsj','term')) for i in (0,1)]
        # The second guard covers deserialization of the 90-digit F/T products.
        padding = allowance() + 2*COUNT_GUARD
        lo = max(0,int((cn*n_lo+rest[0]-padding).to_integral_value(rounding=ROUND_FLOOR)))
        hi = int((cn*n_hi+rest[1]+padding).to_integral_value(rounding=ROUND_CEILING))
        def rounded(mult):
            left, right = significant_text(lo*mult), significant_text(hi*mult)
            return left if left==right else None
        return dict(lower_integer=str(lo), upper_integer=str(hi), screen_probability=[str(e_lo),str(e_hi)],
                    residual_probability=[str(d_lo),str(d_hi)], n_probability=[str(n_lo),str(n_hi)],
                    interval_scaled_1e164=[str(Decimal(i)/scale) for i in (lo,hi)],
                    black_three_digits=rounded(1), either_three_digits=rounded(2), joint_alpha=str(Decimal(budget.numerator)/budget.denominator),
                    screen_tail=str(screen_tail), screen_looks=screen_looks,
                    static_mu_interval=other['static_mu_interval'], allowance=str(allowance()))
