/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode079
import Proofs.RadenkovicGutmanD10Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-5400,0],[-5400,-900,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-89100,-78300,0],[-78300,-7800,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1455300,-482400,0],[-482400,-26500,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-10573200,-1671500,0],[-1671500,-45800,0],[0,0]],[[0,0,0],[0,0],[0]],[[-45424500,-3643200,0],[-3643200,-44400],[0]],[[0,0,0],[0,0],[0]],[[-129512900,-5301700,0],[-5301700,-25000],[0]],[[0,0,0],[0,0],[0]],[[-260777400,-5331600,0],[-5331600,-8100],[0]],[[0,0,0],[0,0],[0]],[[-385111600,-3774800,0],[-3774800,-1400],[0]],[[0,0,0],[0,0],[0]],[[-427293900,-1893000,0],[-1893000,-100],[0]],[[0,0],[0]],[[-361613400,-667900],[-667900]],[[0,0],[0]],[[-235377000,-162000],[-162000]],[[0,0],[0]],[[-118136800,-25700],[-25700]],[[0,0],[0]],[[-45570700,-2400],[-2400]],[[0,0],[0]],[[-13375700,-100],[-100]],[[0]],[[-2931000]],[[0]],[[-464000]],[[0]],[[-50100]],[[0]],[[-3300]],[[0]],[[-100]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
