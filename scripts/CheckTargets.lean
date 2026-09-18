import DuistermaatVanDerKallen

/-! Type checks of target propositions and completed general lemmas.
Printing a proposition is not a proof of it. -/

#print DuistermaatVanDerKallen.MinimalNonvanishing
#print DuistermaatVanDerKallen.InfiniteNonvanishing
#print DuistermaatVanDerKallen.RadiusTailObligation
#print DuistermaatVanDerKallen.SpherePathObligation
#check DuistermaatVanDerKallen.finite_of_common_radius
#check DuistermaatVanDerKallen.affineTorus_uniform_gradient
#check DuistermaatVanDerKallen.compact_regular_controlled_region
#check DuistermaatVanDerKallen.scalarLift_right_inverse
#check DuistermaatVanDerKallen.scalarLift_weighted_normSq
#check DuistermaatVanDerKallen.trajectory_radius_bound
#check DuistermaatVanDerKallen.constantTerm_pow_reindex
#check DuistermaatVanDerKallen.minimal_nonvanishing_rank_zero
#check DuistermaatVanDerKallen.restricted_fderiv_norm_sq
#check DuistermaatVanDerKallen.normalizedTangentLift_minimal
#check DuistermaatVanDerKallen.polynomial_restricted_norm
#check DuistermaatVanDerKallen.polynomialVectorField_contDiffAt
#check DuistermaatVanDerKallen.polynomialVectorField_derivative
#check DuistermaatVanDerKallen.polynomialVectorField_embedded_norm
#check DuistermaatVanDerKallen.polynomialVectorField_local_solution
#check DuistermaatVanDerKallen.torusPartial_constraint_eval
#check DuistermaatVanDerKallen.restrictedDifferential_unit_rank_one
#check DuistermaatVanDerKallen.laurentRepresentative_eval
#check DuistermaatVanDerKallen.laurentEval_pow
#check DuistermaatVanDerKallen.laurentEval_hasFDerivAt
#check DuistermaatVanDerKallen.laurent_uniform_gradient
#check DuistermaatVanDerKallen.laurentControlledRegion_isCompact
#check DuistermaatVanDerKallen.laurentControlledRegion_regular
#check DuistermaatVanDerKallen.laurent_integral_curve_base
#check DuistermaatVanDerKallen.laurent_integral_curve_radius_bound
#check DuistermaatVanDerKallen.uniform_ode_time_on_compact
#check DuistermaatVanDerKallen.ode_extend_right_of_compact
#check DuistermaatVanDerKallen.ode_exists_past_of_compact_control
#check DuistermaatVanDerKallen.laurent_complete_segment
#check DuistermaatVanDerKallen.laurent_segment_unique
#check DuistermaatVanDerKallen.laurent_segment_reverse_inverse
#check DuistermaatVanDerKallen.laurent_zero_velocity_curve
#check DuistermaatVanDerKallen.fiberTransportEquiv
#check DuistermaatVanDerKallen.fiberCurves_compact_control
#check DuistermaatVanDerKallen.fiberCurves_lipschitz_initial
#check DuistermaatVanDerKallen.fiberCurves_continuous
#check DuistermaatVanDerKallen.fiberTransportHomeomorph
#check DuistermaatVanDerKallen.fiberSweep_isCompact
#check DuistermaatVanDerKallen.fiberSweep_subset_regular
#check DuistermaatVanDerKallen.fiberTransport_zero
#check DuistermaatVanDerKallen.curveVectorField_apply
#check DuistermaatVanDerKallen.laurentCurveVectorField_contDiffAt
#check DuistermaatVanDerKallen.curvePrimitiveCLM_norm_le
#check DuistermaatVanDerKallen.picardResidual_partial_zero
#check DuistermaatVanDerKallen.exists_smooth_picard_branch
#check DuistermaatVanDerKallen.laurent_exists_smooth_picard_branch
#check DuistermaatVanDerKallen.laurent_picard_equation_solves_ode
#check DuistermaatVanDerKallen.laurent_exists_analytic_picard_neighborhood
#check DuistermaatVanDerKallen.laurent_local_analytic_endpoint
#check DuistermaatVanDerKallen.laurent_family_analytic
#check DuistermaatVanDerKallen.laurent_family_joint_analytic
#check DuistermaatVanDerKallen.laurentSegmentCurve_joint_analytic
#check DuistermaatVanDerKallen.laurentSegmentCurve_eq_fiberCurve
#check DuistermaatVanDerKallen.fiberTransport_has_analytic_extension
#check DuistermaatVanDerKallen.fiberTransportBack_has_analytic_extension
#check DuistermaatVanDerKallen.laurentSegmentCurve_has_analytic_extension
#check DuistermaatVanDerKallen.laurentRealDifferential_surjective
#check DuistermaatVanDerKallen.laurent_regular_product_chart_fixed
#check DuistermaatVanDerKallen.laurentRealDifferential_ker_finrank
#check DuistermaatVanDerKallen.regularLaurentValue_of_not_critical
#check DuistermaatVanDerKallen.regularFiberIsManifold
#check DuistermaatVanDerKallen.regularFiber_val_contMDiff
#check DuistermaatVanDerKallen.fiberTransportDiffeomorph
#check DuistermaatVanDerKallen.complete_segment_transport
#check DuistermaatVanDerKallen.exists_local_gradient_bound
#check DuistermaatVanDerKallen.criticalValues_union_isClosed
#check DuistermaatVanDerKallen.convexTransportDiffeomorph
#check DuistermaatVanDerKallen.convexTransportDiffeomorph_base
#check DuistermaatVanDerKallen.convexTransport_center
#check DuistermaatVanDerKallen.convexTransport_compact_sweep
#check DuistermaatVanDerKallen.laurent_local_trivialization_at
#check DuistermaatVanDerKallen.laurent_exists_driven_picard_neighborhood
#check DuistermaatVanDerKallen.laurent_driven_local_family
#check DuistermaatVanDerKallen.laurent_driven_uniform_time
#check DuistermaatVanDerKallen.laurent_driven_unique_on_open_interval
#check DuistermaatVanDerKallen.laurent_driven_exists_past_of_compact_control
#check DuistermaatVanDerKallen.laurent_driven_curve_radius_bound
#check DuistermaatVanDerKallen.laurent_complete_C1_path
#check DuistermaatVanDerKallen.laurent_driven_local_analytic_endpoint
#check DuistermaatVanDerKallen.laurent_driven_family_analytic_on
#check DuistermaatVanDerKallen.laurent_driven_unit_unique
#check DuistermaatVanDerKallen.LaurentC1Path.ofInterval
#check DuistermaatVanDerKallen.LaurentC1Path.curve_spec
#check DuistermaatVanDerKallen.LaurentC1Path.reverse_curve
#check DuistermaatVanDerKallen.LaurentC1Path.transportDiffeomorph
#check DuistermaatVanDerKallen.LaurentC1Chain.transportDiffeomorph
#check DuistermaatVanDerKallen.laurent_driven_family_joint_continuous_on
#check DuistermaatVanDerKallen.LaurentC1Path.curves_continuous
#check DuistermaatVanDerKallen.LaurentC1Path.sweep_isCompact
#check DuistermaatVanDerKallen.LaurentC1Chain.sweep_isCompact
#check DuistermaatVanDerKallen.LaurentC1Chain.sweep_subset_regular
#check DuistermaatVanDerKallen.LaurentC1Path.localCoordinateHomotopy
#check DuistermaatVanDerKallen.LaurentC1Path.transportHomotopyOfConvex
#check DuistermaatVanDerKallen.laurentFiberHomology
#check DuistermaatVanDerKallen.LaurentC1Path.homologyIso
#check DuistermaatVanDerKallen.LaurentC1Path.homologyMap_eq_of_convex
#check DuistermaatVanDerKallen.LaurentC1Chain.homologyMap_append
#check DuistermaatVanDerKallen.LaurentC1Chain.homologyMap_comp_coordinate
#check DuistermaatVanDerKallen.localFiberCoordinateHomeomorph
#check DuistermaatVanDerKallen.localFiberHomologyIso
#check DuistermaatVanDerKallen.localHomologyTransition_eq_on_overlap
#check DuistermaatVanDerKallen.ConstantTransitionAtlas.stalkEquiv
#check DuistermaatVanDerKallen.ConstantTransitionAtlas.isCoveringMap_etale
#check DuistermaatVanDerKallen.ConstantTransitionModuleAtlas.sheaf
#check DuistermaatVanDerKallen.ConstantTransitionModuleAtlas.stalkLinearEquiv
#check DuistermaatVanDerKallen.ConstantTransitionModuleAtlas.germLinearEquiv
#check DuistermaatVanDerKallen.laurentHomologyModuleSheaf
#check DuistermaatVanDerKallen.laurentHomologyModuleSheaf_forget
#check DuistermaatVanDerKallen.laurentHomologyStalkLinearEquiv
#check DuistermaatVanDerKallen.laurentHomologyGermLinearEquiv
#check DuistermaatVanDerKallen.laurentHomologySheaf_isCoveringMap
#check DuistermaatVanDerKallen.laurentHomologySection_transport
#check DuistermaatVanDerKallen.LaurentC1Path.timeHomologyMap_coordinate_eq
#check DuistermaatVanDerKallen.LaurentC1Path.exists_time_patch
#check DuistermaatVanDerKallen.laurentHomologyModuleSheaf_isCoveringMap
#check DuistermaatVanDerKallen.LaurentC1Path.homologyLift_continuous
#check DuistermaatVanDerKallen.LaurentC1Path.homologyLift_zero
#check DuistermaatVanDerKallen.LaurentC1Path.homologyLift_one
#check DuistermaatVanDerKallen.LaurentC1Path.homologyLift_eq_liftPath
#check DuistermaatVanDerKallen.LaurentC1Path.homologyMap_eq_of_homotopicRel
#check DuistermaatVanDerKallen.LaurentC1Chain.monodromy_homologyMap
#check DuistermaatVanDerKallen.LaurentC1Chain.homologyMap_eq_of_homotopic
#check DuistermaatVanDerKallen.LaurentC1Chain.homologyMap_eq_id_of_nullhomotopic
#check DuistermaatVanDerKallen.coeff_pow_unique_min
#check DuistermaatVanDerKallen.finite_extremePoint_exposed
#check DuistermaatVanDerKallen.extremePoint_pow_mem
#check DuistermaatVanDerKallen.newtonPolytope_pow
#check DuistermaatVanDerKallen.origin_in_newton_powers
#check DuistermaatVanDerKallen.infinite_of_minimal

#check DuistermaatVanDerKallen.facePart_mul
#check DuistermaatVanDerKallen.newtonPolytope_facePart
#check DuistermaatVanDerKallen.constantTerm_facePart_pow
#check DuistermaatVanDerKallen.exists_span_interior_restriction
#check DuistermaatVanDerKallen.latticeRealMap_injective
#check DuistermaatVanDerKallen.exists_interior_lattice_coordinates
#check DuistermaatVanDerKallen.face_reduction
#print DuistermaatVanDerKallen.InteriorMinimalNonvanishing
#check DuistermaatVanDerKallen.minimal_of_interior_minimal
#check DuistermaatVanDerKallen.minimal_iff_interior_minimal

-- Exact manuscript statement, checked independently of its inferred printed type.
example {d : ℕ} (f : DuistermaatVanDerKallen.MultiLaurent d)
    (hf : (0 : Fin d → ℝ) ∈ DuistermaatVanDerKallen.newtonPolytope f) :
    ∃ r ≤ d, ∃ g : DuistermaatVanDerKallen.MultiLaurent r,
      (∀ n : ℕ, DuistermaatVanDerKallen.constantTerm (g ^ n) =
        DuistermaatVanDerKallen.constantTerm (f ^ n)) ∧
      ((r = 0 ∧ ∃ c : ℂ, c ≠ 0 ∧ g = AddMonoidAlgebra.single 0 c) ∨
        (1 ≤ r ∧ (0 : Fin r → ℝ) ∈ interior (DuistermaatVanDerKallen.newtonPolytope g))) :=
  DuistermaatVanDerKallen.face_reduction f hf

#check DuistermaatVanDerKallen.exists_integer_weight_injOn
#check DuistermaatVanDerKallen.exists_all_coordinate_minimum
#check DuistermaatVanDerKallen.realExponentEquiv
#check DuistermaatVanDerKallen.origin_interior_reindex
#check DuistermaatVanDerKallen.coordinate_minimum_neg
#check DuistermaatVanDerKallen.factor_at_coordinate_minimum
#check DuistermaatVanDerKallen.unimodular_vertex_chart
#check DuistermaatVanDerKallen.laurentEval_polynomialLaurentHom
#check DuistermaatVanDerKallen.unimodular_vertex_chart_evaluation
#print DuistermaatVanDerKallen.VertexMinimalNonvanishing
#check DuistermaatVanDerKallen.minimal_of_vertex_minimal
#check DuistermaatVanDerKallen.minimal_iff_vertex_minimal

-- Exact algebraic vertex-chart statement in every positive rank.
example {d : ℕ} (hd : 1 ≤ d) (f : DuistermaatVanDerKallen.MultiLaurent d)
    (hf : (0 : Fin d → ℝ) ∈ interior (DuistermaatVanDerKallen.newtonPolytope f)) :
    ∃ E : (Fin d → ℤ) ≃ₗ[ℤ] (Fin d → ℤ), ∃ m : Fin d → ℤ,
      (∀ i, 0 < m i) ∧ ∃ u : MvPolynomial (Fin d) ℂ, u.coeff 0 ≠ 0 ∧
        AddMonoidAlgebra.mapDomainRingEquiv ℂ E.toAddEquiv f =
          AddMonoidAlgebra.single (-m) 1 * DuistermaatVanDerKallen.polynomialLaurentHom u ∧
        (∀ n : ℕ, DuistermaatVanDerKallen.constantTerm
          ((AddMonoidAlgebra.mapDomainRingEquiv ℂ E.toAddEquiv f) ^ n) =
            DuistermaatVanDerKallen.constantTerm (f ^ n)) :=
  DuistermaatVanDerKallen.unimodular_vertex_chart hd f hf

#check DuistermaatVanDerKallen.exists_polynomial_derivative_polydisc
#check DuistermaatVanDerKallen.mvPolynomial_hasDerivAt_update
#check DuistermaatVanDerKallen.residueFiberPolynomial_logderiv
#check DuistermaatVanDerKallen.residueFiberPolynomial_deriv_ne_zero
#check DuistermaatVanDerKallen.exists_residue_regular_polydisc
#check DuistermaatVanDerKallen.coeff_pow_norm_le
#check DuistermaatVanDerKallen.summable_constantTerm_series
#check DuistermaatVanDerKallen.generatingFunction_eq_inv_of_vanishing
#check DuistermaatVanDerKallen.integral_torusCharacter
#check DuistermaatVanDerKallen.integral_torusLaurent_eq_constantTerm
#check DuistermaatVanDerKallen.integral_torusLaurent_pow
#check DuistermaatVanDerKallen.generatingFunction_eq_torusCauchy
#check DuistermaatVanDerKallen.isFiniteFourierSum_iff_coefficients
#check DuistermaatVanDerKallen.torus_mathieu_of_minimal

-- The Cauchy-transform formula is a scalar Haar integral, not yet a residue period.
example {d : ℕ} (f : DuistermaatVanDerKallen.MultiLaurent d) (r : Fin d → ℝ)
    (hr : ∀ i, r i ≠ 0) {s : ℂ}
    (hs : DuistermaatVanDerKallen.weightedCoefficientMass f r < ‖s‖) :
    DuistermaatVanDerKallen.constantTermGeneratingFunction f s =
      MeasureTheory.integral (DuistermaatVanDerKallen.phaseTorusMeasure d)
        (fun x => 1 / (s - DuistermaatVanDerKallen.laurentEval f
          (DuistermaatVanDerKallen.torusPoint r x))) :=
  DuistermaatVanDerKallen.generatingFunction_eq_torusCauchy f r hr hs

#check DuistermaatVanDerKallen.unimodular_vertex_chart_nat
#check DuistermaatVanDerKallen.residueFiberPolynomial_zero_iff
#check DuistermaatVanDerKallen.exists_residue_boundary_bound
#check DuistermaatVanDerKallen.exists_residue_interior_regular_roots
#check DuistermaatVanDerKallen.isCompact_residue_root_locus
#check DuistermaatVanDerKallen.isCoveringMap_compactRootProjection
#check DuistermaatVanDerKallen.exists_residue_covering
#check DuistermaatVanDerKallen.finite_residueRootProjection_fiber
#check DuistermaatVanDerKallen.residueRootSpace_laurent_fiber
#check DuistermaatVanDerKallen.residueRootPoint_injective
#check DuistermaatVanDerKallen.isCompact_range_residueRootPoint
#check DuistermaatVanDerKallen.exists_residue_covering_with_branches

-- This is the full compact-covering component, with no unproved regularity
-- premise. The exact positive sheet count is checked separately below.
example {d : ℕ} (m : Fin (d + 1) →₀ ℕ) (hm : ∀ i, 0 < m i)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (hu : u.coeff 0 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ B : ℝ, ∀ s : ℂ, B < ‖s‖ →
      IsCoveringMap (DuistermaatVanDerKallen.residueRootProjection m u ε s) ∧
      ∀ b : DuistermaatVanDerKallen.residueCircleBase d ε,
        (DuistermaatVanDerKallen.residueRootProjection m u ε s ⁻¹' {b}).Finite := by
  obtain ⟨ε, hε, B, hB⟩ := DuistermaatVanDerKallen.exists_residue_covering m hm u hu
  exact ⟨ε, hε, B, fun s hs => ⟨(hB s hs).1, fun b =>
    DuistermaatVanDerKallen.finite_residueRootProjection_fiber m u ε s (hB s hs).1 b⟩⟩

#check DuistermaatVanDerKallen.nonempty_residueDiscData
#check DuistermaatVanDerKallen.residueDeformationEquation_logderiv
#check DuistermaatVanDerKallen.ResidueDiscData.deformation_regular_root
#check DuistermaatVanDerKallen.ResidueDiscData.isCoveringMap_deformationProjection
#check DuistermaatVanDerKallen.complex_monomial_root_card_in_disc
#check DuistermaatVanDerKallen.covering_fiber_card_eq_along_path
#check DuistermaatVanDerKallen.ResidueDiscData.residueRootProjection_card
#check DuistermaatVanDerKallen.ResidueDiscData.residueRootSpace_nonempty
#check DuistermaatVanDerKallen.ResidueDiscData.residueRoot_local_branch
#check DuistermaatVanDerKallen.exists_residue_covering_degree

-- The actual covering has the precise positive sheet count; no root-count,
-- boundary-exclusion, or regularity premise is left to be supplied.
example {d : ℕ} (m : Fin (d + 1) →₀ ℕ) (hm : ∀ i, 0 < m i)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (hu : u.coeff 0 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ B : ℝ, ∀ s : ℂ, B < ‖s‖ →
      IsCoveringMap (DuistermaatVanDerKallen.residueRootProjection m u ε s) ∧
      Function.Surjective (DuistermaatVanDerKallen.residueRootProjection m u ε s) ∧
      ∀ b : DuistermaatVanDerKallen.residueCircleBase d ε,
        Nat.card (DuistermaatVanDerKallen.residueRootProjection m u ε s ⁻¹' {b}) = m 0 :=
  DuistermaatVanDerKallen.exists_residue_covering_degree m hm u hu

#check DuistermaatVanDerKallen.complexCoordinatesHomeomorph
#check DuistermaatVanDerKallen.IsSemialgebraic.polynomial_preimage
#check DuistermaatVanDerKallen.IsComplexSemialgebraic.polynomial_preimage
#check DuistermaatVanDerKallen.range_residueRootPoint_eq
#check DuistermaatVanDerKallen.isComplexSemialgebraic_residueFamily

-- Compactness and semialgebraicity concern the actual coordinate image,
-- while covering and degree concern its actual projection to the circle base.
example {d : ℕ} (m : Fin (d + 1) →₀ ℕ) (hm : ∀ i, 0 < m i)
    (u : MvPolynomial (Fin (d + 1)) ℂ) (hu : u.coeff 0 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ B : ℝ, ∀ s : ℂ, B < ‖s‖ →
      IsCompact (Set.range (DuistermaatVanDerKallen.residueRootPoint m u ε s)) ∧
      DuistermaatVanDerKallen.IsComplexSemialgebraic
        (Set.range (DuistermaatVanDerKallen.residueRootPoint m u ε s)) ∧
      IsCoveringMap (DuistermaatVanDerKallen.residueRootProjection m u ε s) ∧
      Function.Surjective (DuistermaatVanDerKallen.residueRootProjection m u ε s) ∧
      ∀ b : DuistermaatVanDerKallen.residueCircleBase d ε,
        Nat.card (DuistermaatVanDerKallen.residueRootProjection m u ε s ⁻¹' {b}) = m 0 :=
  DuistermaatVanDerKallen.exists_compact_semialgebraic_residue_covering m hm u hu

#print DuistermaatVanDerKallen.SemialgebraicProjectionObligation
#check DuistermaatVanDerKallen.IsSemialgebraic.eventuallyConstant_polynomial_curve
#check DuistermaatVanDerKallen.IsSemialgebraic.contains_tail_of_unbounded
#check DuistermaatVanDerKallen.isSemialgebraic_smallGradientTotalFamily
#check DuistermaatVanDerKallen.isComplexSemialgebraic_smallGradientSphere
#check DuistermaatVanDerKallen.isSemialgebraic_radiusIncidence
#check DuistermaatVanDerKallen.radiusApproximationSet_iff_projection

-- Exact original tail obligation, conditional solely on the unproved
-- coordinate-projection standard input. This is not a proof of that input.
example (hproj : DuistermaatVanDerKallen.SemialgebraicProjectionObligation) :
    DuistermaatVanDerKallen.RadiusTailObligation :=
  DuistermaatVanDerKallen.radiusTail_of_semialgebraic_projection hproj

-- The same single set includes both varying parameters, not a separate
-- semialgebraicity claim with constants depending on a fixed radius/threshold.
example {d : ℕ} (g : Fin d → DuistermaatVanDerKallen.AmbientPolynomial d) :
    DuistermaatVanDerKallen.IsSemialgebraic
      (DuistermaatVanDerKallen.RadiusFamilyIndex d)
      {q | 1 < q (.inl 0) ∧ 0 < q (.inl 1) ∧
        DuistermaatVanDerKallen.radiusFamilyPoint q ∈
          DuistermaatVanDerKallen.smallGradientSphere g (q (.inl 0)) (q (.inl 1))} :=
  DuistermaatVanDerKallen.isSemialgebraic_smallGradientTotalFamily g

#print DuistermaatVanDerKallen.SphereC1ChainObligation
#check DuistermaatVanDerKallen.curve_derivative_mem_torusTangentSpace
#check DuistermaatVanDerKallen.smallGradient_curve_image_integral_bound
#check DuistermaatVanDerKallen.C1ArcChain.smallGradient_image_dist_le
#check DuistermaatVanDerKallen.radiusApproximationSet_unbounded_of_asymptotic
#check DuistermaatVanDerKallen.normalize_mem_smallGradientSphere

-- Actual Laurent evaluation, proper ambient radius, and restricted differential.
-- The two geometric premises are still unproved; this checks conditional coverage.
example (hproj : DuistermaatVanDerKallen.SemialgebraicProjectionObligation)
    (hpaths : DuistermaatVanDerKallen.SphereC1ChainObligation)
    {d : ℕ} (f : DuistermaatVanDerKallen.MultiLaurent d) :
    (DuistermaatVanDerKallen.asymptoticCriticalValues
      (DuistermaatVanDerKallen.laurentOnAffineTorus f) (fun x => ‖x.val‖)
      (DuistermaatVanDerKallen.laurentDifferentialNorm f)).Finite :=
  DuistermaatVanDerKallen.laurent_finite_asymptotic_of_projection_and_paths hproj hpaths f

#check DuistermaatVanDerKallen.ambientDifferentialNorm_eq_zero_iff
#check DuistermaatVanDerKallen.isComplexSemialgebraic_criticalTorusLocus
#check DuistermaatVanDerKallen.C1ArcChain.critical_image_eq
#check DuistermaatVanDerKallen.dummyExtension_eval
#check DuistermaatVanDerKallen.dummyExtension_critical
#check DuistermaatVanDerKallen.ordinaryCriticalValues_subset_dummy_asymptotic

-- Both critical-value sets use the original Laurent evaluation and proper
-- induced radius, and only the same two still-unproved geometric premises.
example (hproj : DuistermaatVanDerKallen.SemialgebraicProjectionObligation)
    (hpaths : DuistermaatVanDerKallen.SphereC1ChainObligation)
    {d : ℕ} (f : DuistermaatVanDerKallen.MultiLaurent d) :
    (DuistermaatVanDerKallen.ordinaryCriticalValues
        (DuistermaatVanDerKallen.laurentOnAffineTorus f)
        (DuistermaatVanDerKallen.laurentDifferentialNorm f) ∪
      DuistermaatVanDerKallen.asymptoticCriticalValues
        (DuistermaatVanDerKallen.laurentOnAffineTorus f) (fun x => ‖x.val‖)
        (DuistermaatVanDerKallen.laurentDifferentialNorm f)).Finite :=
  DuistermaatVanDerKallen.laurent_finite_critical_union_of_projection_and_paths hproj hpaths f

example (hproj : DuistermaatVanDerKallen.SemialgebraicProjectionObligation)
    (hpaths : DuistermaatVanDerKallen.SphereC1ChainObligation)
    {d : ℕ} (f : DuistermaatVanDerKallen.MultiLaurent d) :
    ((DuistermaatVanDerKallen.laurentGoodValues f : Set ℂ)ᶜ).Finite :=
  DuistermaatVanDerKallen.laurentGoodValues_finite_compl_of_projection_and_paths hproj hpaths f

#check DuistermaatVanDerKallen.torusPartial_eval_eq_of_eqOn
#check DuistermaatVanDerKallen.ambientDifferentialNorm_eq_of_eqOn
#check DuistermaatVanDerKallen.infinityExample_line_partials
#check DuistermaatVanDerKallen.infinityExample_inverse_norm
#check DuistermaatVanDerKallen.infinityExample_inverse_gradient

-- Unconditional regression using the exact Laurent definitions of the targets.
example (c : ℂ) :
    (0 : Fin 2 → ℝ) ∈ interior (DuistermaatVanDerKallen.newtonPolytope
      (DuistermaatVanDerKallen.infinityExampleLaurent c)) ∧
    c ∈ DuistermaatVanDerKallen.asymptoticCriticalValues
      (DuistermaatVanDerKallen.laurentOnAffineTorus
        (DuistermaatVanDerKallen.infinityExampleLaurent c)) (fun x => ‖x.val‖)
      (DuistermaatVanDerKallen.laurentDifferentialNorm
        (DuistermaatVanDerKallen.infinityExampleLaurent c)) ∧
    c ∉ DuistermaatVanDerKallen.ordinaryCriticalValues
      (DuistermaatVanDerKallen.laurentOnAffineTorus
        (DuistermaatVanDerKallen.infinityExampleLaurent c))
      (DuistermaatVanDerKallen.laurentDifferentialNorm
        (DuistermaatVanDerKallen.infinityExampleLaurent c)) :=
  DuistermaatVanDerKallen.infinityExample_regression c
