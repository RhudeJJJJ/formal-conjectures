/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode035
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .pow e035 2
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,441],[0,882],[441]],[[0,0,0],[0,0],[0]],[[0,15876,3822],[15876,7644],[3822]],[[0,0,0],[0,0],[0]],[[142884,179928,12985],[179928,25970],[12985]],[[0,0,0],[0,0],[0]],[[2000376,873180,22442],[873180,44884],[22442]],[[0,0,0],[0,0],[0]],[[12526164,2404920,21756],[2404920,43512],[21756]],[[0,0,0],[0,0],[0]],[[46686024,4204396,12250],[4204396,24500],[12250]],[[0,0,0],[0,0],[0]],[[116222904,4935280,3969],[4935280,7938],[3969]],[[0,0,0],[0,0],[0]],[[205396632,4003496,686],[4003496,1372],[686]],[[0,0,0],[0,0],[0]],[[267087436,2269680,49],[2269680,98],[49]],[[0,0],[0]],[[261127272,895916],[895916]],[[0,0],[0]],[[194299112,241080],[241080]],[[0,0],[0]],[[110567912,42140],[42140]],[[0,0],[0]],[[48036268,4312],[4312]],[[0,0],[0]],[[15790936,196],[196]],[[0]],[[3856888]],[[0]],[[677768]],[[0]],[[80948]],[[0]],[[5880]],[[0]],[[196]]]
theorem step114 : p114=NestedArithmetic.power p035 2 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_pow 2 e114 e035 p035 p114 rfl h035 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
