/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode035
import Proofs.RadenkovicGutmanD3Long00StagedUNode039
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e040 : NestedArithmetic.Expr 3 := .times e035 e039
noncomputable def p040 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-2]],[[0,0],[0]],[[90,-18],[-18]],[[0,0],[0]],[[618,-48],[-48]],[[0,0],[0]],[[1786,-44],[-44]],[[0,0],[0]],[[2636,-16],[-16]],[[0,0],[0]],[[2040,-2],[-2]],[[0]],[[728]],[[0]],[[10]],[[0]],[[-76]],[[0]],[[-22]],[[0]],[[-2]]]
theorem step040 : p040=NestedArithmetic.mul p035 p039 := by decide +kernel
#print axioms step040
theorem h040 : NestedArithmetic.compile e040=p040 := StagedExprCompile.compile_times e040 e035 e039 p035 p039 p040 rfl h035 h039 step040
#print axioms h040
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
