/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode071
import Proofs.RadenkovicGutmanD2Long00CompositionalNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e071 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-144,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1296,-2160,0],[-2160,-1428,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-48708,-27540,0],[-27540,-5800,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-578340,-152136,0],[-152136,-12628,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3591840,-481580,0],[-481580,-16264,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-13927636,-975208,0],[-975208,-12880,0],[0,0]],[[0,0,0],[0,0],[0]],[[-36825148,-1336956,0],[-1336956,-6296],[0]],[[0,0,0],[0,0],[0]],[[-69898040,-1280592,0],[-1280592,-1844],[0]],[[0,0,0],[0,0],[0]],[[-98388320,-870952,0],[-870952,-296],[0]],[[0,0,0],[0,0],[0]],[[-104882956,-422336,0],[-422336,-20],[0]],[[0,0,0],[0,0],[0]],[[-85793848,-144828,0],[-144828,0],[0]],[[0,0],[0]],[[-54231160,-34280],[-34280]],[[0,0],[0]],[[-26532400,-5324],[-5324]],[[0,0],[0]],[[-10007276,-488],[-488]],[[0,0],[0]],[[-2879308,-20],[-20]],[[0,0],[0]],[[-619800,0],[0]],[[0]],[[-96560]],[[0]],[[-10276]],[[0]],[[-668]],[[0]],[[-20]],[[0]],[[0]]]
theorem step083 : p083=NestedHorner.add p071 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e071 e082 p071 p082 p083 rfl h071 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
