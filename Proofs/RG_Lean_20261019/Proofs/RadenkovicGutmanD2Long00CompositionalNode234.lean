/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode214
import Proofs.RadenkovicGutmanD2Long00CompositionalNode211
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e234 : NestedArithmetic.Expr 3 := .times e214 e211
noncomputable def p234 : NestedHorner.Poly 3 := [[[-8],[0],[0]],[[0,0],[0,0],[0]],[[-256,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3768,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-33824,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-207024,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-915080,-12,0],[-12,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3018368,-280,0],[-280,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7571200,-2916,0],[-2916,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-14584056,-17880,0],[-17880,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-21633736,-71716,0],[-71716,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-24628856,-197748,-4],[-197748,-16,0],[-4,0]],[[0,0,0],[0,0,0],[0,0]],[[-21305824,-383508,-60],[-383508,-240,0],[-60,0]],[[0,0,0],[0,0,0],[0,0]],[[-13755776,-526120,-376],[-526120,-1504,0],[-376,0]],[[0,0,0],[0,0,0],[0,0]],[[-6436632,-506112,-1276],[-506112,-5104,0],[-1276,0]],[[0,0,0],[0,0,0],[0,0]],[[-2081232,-332904,-2544],[-332904,-10176,0],[-2544,0]],[[0,0,0],[0,0,0],[0,0]],[[-428544,-142456,-3028],[-142456,-12112,-4],[-3028,-4]],[[0,0,0],[0,0,0],[0,0]],[[-47952,-36000,-2088],[-36000,-8352,-28],[-2088,-28]],[[0,0,0],[0,0,0],[0,0]],[[-1944,-4320,-756],[-4320,-3024,-64],[-756,-64]],[[0,0,0],[0,0,0],[0,0]],[[0,-108,-108],[-108,-432,-52],[-108,-52]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,-12],[0,-12]]]
theorem step234 : p234=NestedArithmetic.mul p214 p211 := by decide +kernel
#print axioms step234
theorem h234 : NestedArithmetic.compile e234=p234 := StagedExprCompile.compile_times e234 e214 e211 p214 p211 p234 rfl h214 h211 step234
#print axioms h234
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
