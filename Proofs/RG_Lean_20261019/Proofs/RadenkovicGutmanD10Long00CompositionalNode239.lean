/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode236
import Proofs.RadenkovicGutmanD10Long00CompositionalNode238
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e239 : NestedArithmetic.Expr 3 := .plus e236 e238
noncomputable def p239 : NestedHorner.Poly 3 := [[[-100],[0],[0]],[[0,0],[0,0],[0]],[[-3300,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-50100,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-464000,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2931000,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-13375700,-100,0],[-100,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-45570700,-2400,0],[-2400,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-118136800,-25700,0],[-25700,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-235377000,-162000,0],[-162000,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-361613400,-667900,0],[-667900,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-427293900,-1893000,0],[-1893000,-100,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-385111600,-3774800,0],[-3774800,-1400,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-260777400,-5331600,0],[-5331600,-8100,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-129512900,-5301700,0],[-5301700,-25000,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-45424500,-3643200,0],[-3643200,-44400,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-10573200,-1671500,0],[-1671500,-45800,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1455300,-482400,0],[-482400,-26500,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-89100,-78300,0],[-78300,-7800,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-5400,0],[-5400,-900,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step239 : p239=NestedHorner.add p236 p238 := by decide +kernel
#print axioms step239
theorem h239 : NestedArithmetic.compile e239=p239 := StagedExprCompile.compile_plus e239 e236 e238 p236 p238 p239 rfl h236 h238 step239
#print axioms h239
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
