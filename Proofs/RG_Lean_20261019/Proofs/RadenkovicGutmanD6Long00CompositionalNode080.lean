/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode035
import Proofs.RadenkovicGutmanD6Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-108],[0,-108]],[[0,0,0],[0,0,0],[0,0]],[[0,-972,-972],[-972,-3888,-468],[-972,-468]],[[0,0,0],[0,0,0],[0,0]],[[-17496,-38880,-6804],[-38880,-27216,-576],[-6804,-576]],[[0,0,0],[0,0,0],[0,0]],[[-431568,-324000,-18792],[-324000,-75168,-252],[-18792,-252]],[[0,0,0],[0,0,0],[0,0]],[[-3856896,-1282104,-27252],[-1282104,-109008,-36],[-27252,-36]],[[0,0,0],[0,0],[0]],[[-18731088,-2996136,-22896],[-2996136,-91584],[-22896]],[[0,0,0],[0,0],[0]],[[-57929688,-4555008,-11484],[-4555008,-45936],[-11484]],[[0,0,0],[0,0],[0]],[[-123801984,-4735080,-3384],[-4735080,-13536],[-3384]],[[0,0,0],[0,0],[0]],[[-191752416,-3451572,-540],[-3451572,-2160],[-540]],[[0,0,0],[0,0],[0]],[[-221659704,-1779732,-36],[-1779732,-144],[-36]],[[0,0],[0]],[[-194703624,-645444],[-645444]],[[0,0],[0]],[[-131256504,-160920],[-160920]],[[0,0],[0]],[[-68140800,-26244],[-26244]],[[0,0],[0]],[[-27165312,-2520],[-2520]],[[0,0],[0]],[[-8235720,-108],[-108]],[[0]],[[-1863216]],[[0]],[[-304416]],[[0]],[[-33912]],[[0]],[[-2304]],[[0]],[[-72]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
