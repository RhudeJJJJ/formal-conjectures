/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode078
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e082 : NestedArithmetic.Expr 3 := .scaled (-1) e078
noncomputable def p082 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,-25]],[[0,0],[0,0,0],[0,0]],[[0,0,-225],[0,-450,-450],[-225,-450]],[[0,0,0],[0,0,0],[0,0]],[[2025,-7425,-3975],[-7425,-12000,-1200],[-3975,-1200]],[[0,0,0],[0,0,0],[0,0]],[[-25650,-119475,-17425],[-119475,-56450,-1100],[-17425,-1100]],[[0,0,0],[0,0,0],[0,0]],[[-722925,-688275,-35750],[-688275,-120100,-400],[-35750,-400]],[[0,0,0],[0,0,0],[0,0]],[[-5571150,-2118650,-41100],[-2118650,-142200,-50],[-41100,-50]],[[0,0,0],[0,0],[0]],[[-23180975,-4057075,-28400],[-4057075,-101100],[-28400]],[[0,0,0],[0,0],[0]],[[-62157500,-5208175,-12025],[-5208175,-44050],[-12025]],[[0,0,0],[0,0],[0]],[[-116642250,-4664500,-3050],[-4664500,-11500],[-3050]],[[0,0,0],[0,0],[0]],[[-160435450,-2973275,-425],[-2973275,-1650],[-425]],[[0,0,0],[0,0],[0]],[[-166304250,-1356425,-25],[-1356425,-100],[-25]],[[0,0],[0]],[[-132096500,-439400],[-439400]],[[0,0],[0]],[[-81113250,-98625],[-98625]],[[0,0],[0]],[[-38598450,-14575],[-14575]],[[0,0],[0]],[[-14182475,-1275],[-1275]],[[0,0],[0]],[[-3981900,-50],[-50]],[[0]],[[-837750]],[[0]],[[-127750]],[[0]],[[-13325]],[[0]],[[-850]],[[0]],[[-25]]]
theorem step082 : p082=NestedHorner.scale (-1) p078 := by decide +kernel
#print axioms step082
theorem h082 : NestedArithmetic.compile e082=p082 := StagedExprCompile.compile_scaled (-1) e082 e078 p078 p082 rfl h078 step082
#print axioms h082
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
