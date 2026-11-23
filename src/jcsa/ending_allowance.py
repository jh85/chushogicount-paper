"""Exact conservative allowance for the recorded small-material ending discrepancies.

Proof and scope: docs/jcsa-20261122.md. This is an additive error
allowance, not a candidate filter or a newly selected rule convention. Historical
intervals are not modified. All counts here are integers.
"""
SQUARES = 144
SIDE_STOCK = 46
PAWNS_AND_GO_BETWEENS = 14
DEAD_LANCES = 2


def allowance(n_squares=SQUARES, side_stock=SIDE_STOCK,
              pawn_go_between_stock=PAWNS_AND_GO_BETWEENS,
              dead_lance_stock=DEAD_LANCES):
    """Black-to-move bound, including raw flags and both terminal-bit values.

    One side has at most one royal, pawn/go-between-origin pieces (either form,
    anywhere), and dead lances on their fixed file's last square. The other side
    has arbitrary surviving/promoted pieces from its initial labelled stock.
    Occupancy, movement, colour classes and material dependencies are relaxed.
    """
    if min(n_squares,side_stock,pawn_go_between_stock,dead_lance_stock)<0:
        raise ValueError('negative stock or board size')
    royal = 1+n_squares
    labelled_piece = 1+2*n_squares
    fixed_dead_lances = 2**dead_lance_stock
    thin = royal*labelled_piece**pawn_go_between_stock*fixed_dead_lances
    other = labelled_piece**side_stock
    raw_flags = 1+n_squares
    terminal_bits = 2
    thin_side_choices = 2
    return thin_side_choices*thin*other*raw_flags*terminal_bits


if __name__=='__main__':
    import json
    value=allowance()
    print(json.dumps(dict(black_to_move=str(value),either_side=str(2*value),
                         formula='336400 * 289**60',scope='recorded small-material ending discrepancies; see proof'),indent=2))
