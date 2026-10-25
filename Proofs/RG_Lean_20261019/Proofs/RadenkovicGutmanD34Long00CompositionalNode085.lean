/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode073
import Proofs.RadenkovicGutmanD34Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-2448,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-22032,-271728,0],[-271728,-63444,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4705668,-3875796,0],[-3875796,-438056,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-73166436,-23580360,0],[-23580360,-1367956,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-521206944,-80930540,0],[-80930540,-2269704,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2213644052,-175130600,0],[-175130600,-2151248,0],[0,0]],[[0,0,0],[0,0],[0]],[[-6262428924,-253458236,0],[-253458236,-1195032],[0]],[[0,0,0],[0,0],[0]],[[-12537299128,-253801296,0],[-253801296,-383860],[0]],[[0,0,0],[0,0],[0]],[[-18432658272,-179085480,0],[-179085480,-65960],[0]],[[0,0,0],[0,0],[0]],[[-20378840780,-89563072,0],[-89563072,-4692],[0]],[[0,0,0],[0,0],[0]],[[-17195910584,-31529084,0],[-31529084,0],[0]],[[0,0],[0]],[[-11165536760,-7633000],[-7633000]],[[0,0],[0]],[[-5592364336,-1208972],[-1208972]],[[0,0],[0]],[[-2153360556,-112744],[-112744]],[[0,0],[0]],[[-631058700,-4692],[-4692]],[[0,0],[0]],[[-138093720,0],[0]],[[0]],[[-21834800]],[[0]],[[-2355044]],[[0]],[[-154972]],[[0]],[[-4692]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
