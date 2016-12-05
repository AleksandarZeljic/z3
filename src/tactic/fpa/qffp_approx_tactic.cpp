/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qffpa_approx_tactic.cpp

Abstract:

    Approximtaing tactic for QF_FP benchmarks.

Author:

    Christoph (cwinter) 2015-06-13

Notes:

--*/
#include"tactical.h"
#include"simplify_tactic.h"
#include"bit_blaster_tactic.h"
#include"sat_tactic.h"
#include"fpa2bv_approx_tactic.h"
#include"smt_tactic.h"
#include"propagate_values_tactic.h"
#include"probe_arith.h"
#include"qfnra_tactic.h"

#include"qffp_tactic.h"
#include"qffp_approx_tactic.h"

tactic * mk_qffp_approx_tactic(ast_manager & m, params_ref const & p) {
    params_ref simp_p = p;
    simp_p.set_bool("arith_lhs", true);
    simp_p.set_bool("elim_and", true);

    tactic * st = and_then(mk_simplify_tactic(m, simp_p),
                           mk_propagate_values_tactic(m, p),
                           using_params(mk_simplify_tactic(m, p), simp_p),
                           cond(mk_or(mk_produce_proofs_probe(), mk_produce_unsat_cores_probe()),
                                mk_smt_tactic(),
                                cond(mk_is_qffp_probe(),
                                     mk_fpa2bv_approx_tactic(m, p),
                                     mk_qfnra_tactic(m, p))),
                           mk_fail_if_undecided_tactic());
    
    st->updt_params(p);
    return st;
}

tactic * mk_qffpbv_approx_tactic(ast_manager & m, params_ref const & p) {
    return mk_qffp_approx_tactic(m, p);
}
