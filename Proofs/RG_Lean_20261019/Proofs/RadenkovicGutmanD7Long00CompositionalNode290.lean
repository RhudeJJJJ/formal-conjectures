/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode289
import Proofs.RadenkovicGutmanD7Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[196,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[5880,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[80948,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[677768,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[3856888,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[15790936,196,0],[196,0],[0]],[[0,0,0],[0,0],[0]],[[48036268,4312,0],[4312,0],[0]],[[0,0,0],[0,0],[0]],[[110567912,42140,0],[42140,0],[0]],[[0,0,0],[0,0],[0]],[[194299112,241080,0],[241080,0],[0]],[[0,0,0],[0,0],[0]],[[261127272,895916,0],[895916,0],[0]],[[0,0,0],[0,0],[0]],[[267087436,2269680,49],[2269680,98],[49]],[[0,0,0],[0,0],[0]],[[205396632,4003496,686],[4003496,1372],[686]],[[0,0,0],[0,0],[0]],[[116222904,4935280,3969],[4935280,7938],[3969]],[[0,0,0],[0,0],[0]],[[46686024,4204396,12250],[4204396,24500],[12250]],[[0,0,0],[0,0],[0]],[[12526164,2404920,21756],[2404920,43512],[21756]],[[0,0,0],[0,0],[0]],[[2000376,873180,22442],[873180,44884],[22442]],[[0,0,0],[0,0],[0]],[[142884,179928,12985],[179928,25970],[12985]],[[0,0,0],[0,0],[0]],[[0,15876,3822],[15876,7644],[3822]],[[0,0,0],[0,0],[0]],[[0,0,441],[0,882],[441]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
