import Pendencias
#print axioms Pendencias.Runge.runge_majorant_sub
#print axioms Pendencias.interp_remainder_C2On
#print axioms Pendencias.quadratic_dyadic_constant_on
#print axioms Pendencias.Agenda.schedule_nesting
#print axioms Pendencias.Agenda.pErr_eq_min
#print axioms Pendencias.Agenda.arithmetic_floor
#print axioms Pendencias.Agenda.infDist_QH
#print axioms Pendencias.Agenda.height_lower_bound
#print axioms Pendencias.FRM_subset_FRMIcc
#print axioms Pendencias.extF_mem_FRM
#print axioms Pendencias.derivative_control_Icc
#print axioms Pendencias.joint_budget_Icc
#print axioms Pendencias.joint_all_N_Icc
#print axioms Pendencias.height_for_epsilon_Icc
#print axioms Pendencias.entropy_codebook_Icc
#print axioms Pendencias.local_asymptotic_error_on
#print axioms Pendencias.general_dyadic_envelope_on
#print axioms Pendencias.general_dyadic_envelope_liminf_on
#print axioms Pendencias.general_dyadic_envelope_zero_on
#print axioms Pendencias.Agenda.c2_endpoint
#print axioms Pendencias.Agenda.c2_endpoint_bits
-- rodada 2
#print axioms Pendencias.Agenda.dyadic_reduction
#print axioms Pendencias.Agenda.dyadic_reduction_inf
#print axioms Pendencias.Agenda.homogeneity_failure
#print axioms Pendencias.Agenda.homogeneity_failure_inf
#print axioms Pendencias.Agenda.universal_inverse
#print axioms Pendencias.Agenda.inverse_modulus
#print axioms Pendencias.Agenda.inverse_besov
#print axioms Pendencias.Agenda.raw_library_inverse_inf
#print axioms Pendencias.Agenda.raw_library_inverse
#print axioms Pendencias.Agenda.schedule_raw_inverse
#print axioms Pendencias.PenteGemini.tent_continuous
#print axioms Pendencias.PenteGemini.tentTree_WF
#print axioms Pendencias.PenteGemini.combFun_continuous
#print axioms Pendencias.PenteGemini.combFrom_spec
#print axioms Pendencias.PenteGemini.omega2_combFun_lower
#print axioms Pendencias.PenteGemini.not_besovInf_combFun
#print axioms Pendencias.PenteGemini.not_besovQ_combFun
#print axioms Pendencias.PenteGemini.critical_tent_comb
#print axioms Pendencias.Marcada.marked_extends
#print axioms Pendencias.Marcada.canonShape_no_interior
#print axioms Pendencias.Marcada.RedReLU.Hcan_eq_maxHeight
#print axioms Pendencias.Marcada.RedReLU.canon_leaves_free
#print axioms Pendencias.coding_formats_comparison
#print axioms Pendencias.gen_eq_RepCat
#print axioms Pendencias.enumSelect_eq_canon
#print axioms Pendencias.tree_rate_pow
#print axioms Pendencias.tree_rate
#print axioms Pendencias.tree_rationalization
#print axioms Pendencias.DPprog.fixTable_cost
#print axioms Pendencias.DPprog.fixRoot_spec
#print axioms Pendencias.DPprog.varTable_cost
#print axioms Pendencias.DPprog.varRoot_spec
-- teste executável de III.3.25 (|𝓛₂|, catálogo D=0 e D=1 com H=2, seleção)
#eval (Artigo.LH 2).card
#eval (Pendencias.gen 2 0 0 0).card
#eval (Pendencias.gen 2 1 0 0).card
#eval (Pendencias.enumSelect 2 1 0 0 (fun R => -(R.numLeaves : ℚ))).map (fun R => (R.numLeaves, R.maxHeight))
-- rodada 3 (13/11/2026)
#print axioms Pendencias.Jackson.whitney_one
#print axioms Pendencias.Jackson.rational_jackson_height
#print axioms Pendencias.Jackson.rational_jackson_uniform
#print axioms Pendencias.Jackson.direct_besov_height
#print axioms Pendencias.Jackson.uniform_besov_ball
#print axioms Pendencias.Jackson.regularized_jackson
#print axioms Pendencias.Jackson.regularized_jackson_uniform
#print axioms Pendencias.Jackson.complete_besov_reversibility
#print axioms Pendencias.Jackson.architecture_stable_reversibility
#print axioms Pendencias.Jackson.besov_direct_whitney
#print axioms Pendencias.Jackson.besov_direct
#print axioms Pendencias.NosLivres.free_knots

-- Minimalidade combinatoria: auxiliares, sem declarar fechamento de IV.5.2.
#print axioms Pendencias.Marcada.canonShape_least
#print axioms Pendencias.Marcada.canonShape_unique_least
#print axioms Pendencias.Marcada.canonShape_independent_depth
#print axioms Pendencias.Marcada.canonShape_min_leaves

-- Reversibilidade rasa completa: parametros reais e todas as conclusoes de IV.5.2.
#print axioms Pendencias.Marcada.canonShape_leaf_bounds
#print axioms Pendencias.Marcada.RedReLU.canonTree_representation_bounds
#print axioms Pendencias.Marcada.RealReLU.not_differentiableAt_break
#print axioms Pendencias.Marcada.RealReLU.parameters_necessary
#print axioms Pendencias.Marcada.RealReLU.marked_realizable_iff
#print axioms Pendencias.Marcada.RealReLU.canonicalTree_spec
#print axioms Pendencias.Marcada.RealReLU.realizes_refines_canonical
#print axioms Pendencias.Marcada.RealReLU.canonicalTree_unique_least
#print axioms Pendencias.Marcada.RealReLU.original_realizable_iff
#print axioms Pendencias.Marcada.RealReLU.dyadicDepth_spec
#print axioms Pendencias.Marcada.RealReLU.exact_shallow_reversal
#print axioms Pendencias.Marcada.MTree.eq_of_shape_eval
#print axioms Pendencias.Marcada.RealReLU.canonicalTree_unique_least_labeled
