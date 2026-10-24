/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode034
import Proofs.RadenkovicGutmanD2Long00CompositionalNode051
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .times e034 e051
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-12],[0,-12]],[[0,0,0],[0,0,0],[0,0]],[[0,-108,-108],[-108,-432,-52],[-108,-52]],[[0,0,0],[0,0,0],[0,0]],[[-1944,-4320,-756],[-4320,-3024,-64],[-756,-64]],[[0,0,0],[0,0,0],[0,0]],[[-47952,-36000,-2088],[-36000,-8352,-28],[-2088,-28]],[[0,0,0],[0,0,0],[0,0]],[[-428544,-142456,-3028],[-142456,-12112,-4],[-3028,-4]],[[0,0,0],[0,0],[0]],[[-2081232,-332904,-2544],[-332904,-10176],[-2544]],[[0,0,0],[0,0],[0]],[[-6436632,-506112,-1276],[-506112,-5104],[-1276]],[[0,0,0],[0,0],[0]],[[-13755776,-526120,-376],[-526120,-1504],[-376]],[[0,0,0],[0,0],[0]],[[-21305824,-383508,-60],[-383508,-240],[-60]],[[0,0,0],[0,0],[0]],[[-24628856,-197748,-4],[-197748,-16],[-4]],[[0,0],[0]],[[-21633736,-71716],[-71716]],[[0,0],[0]],[[-14584056,-17880],[-17880]],[[0,0],[0]],[[-7571200,-2916],[-2916]],[[0,0],[0]],[[-3018368,-280],[-280]],[[0,0],[0]],[[-915080,-12],[-12]],[[0]],[[-207024]],[[0]],[[-33824]],[[0]],[[-3768]],[[0]],[[-256]],[[0]],[[-8]]]
theorem step078 : p078=NestedArithmetic.mul p034 p051 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_times e078 e034 e051 p034 p051 p078 rfl h034 h051 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
