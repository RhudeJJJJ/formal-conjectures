/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode108
import Proofs.RadenkovicGutmanD3Long00StagedUNode109
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e110 : NestedArithmetic.Expr 3 := .plus e108 e109
noncomputable def p110 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,9]],[[0,0],[0,0,0],[0,0,0]],[[0,0,81],[0,0,234],[81,234,16]],[[0,0,0],[0,0,0],[0,0,0]],[[729,2106,2403],[2106,5796,1104],[2403,1104,4]],[[0,0,0],[0,0,0],[0,0]],[[44550,64638,15561],[64638,44040,1932],[15561,1932]],[[0,0,0],[0,0,0],[0,0]],[[839511,546534,46710],[546534,141296,1592],[46710,1592]],[[0,0,0],[0,0,0],[0,0]],[[7218450,2330880,79260],[2330880,251880,642],[79260,642]],[[0,0,0],[0,0,0],[0,0]],[[36070905,6062430,82728],[6062430,275848,120],[82728,120]],[[0,0,0],[0,0,0],[0,0]],[[118374772,10511054,55225],[10511054,193536,8],[55225,8]],[[0,0,0],[0,0],[0]],[[273462866,12750364,23870],[12750364,87904],[23870]],[[0,0,0],[0,0],[0]],[[464196962,11120064,6601],[11120064,25448],[6601]],[[0,0,0],[0,0],[0]],[[595299680,7070502,1117],[7070502,4468],[1117]],[[0,0,0],[0,0],[0]],[[587351336,3289794,104],[3289794,424],[104]],[[0,0,0],[0,0],[0]],[[450984528,1113406,4],[1113406,16],[4]],[[0,0],[0]],[[271149102,269336],[269336]],[[0,0],[0]],[[127849701,45010],[45010]],[[0,0],[0]],[[47127996,4882],[4882]],[[0,0],[0]],[[13467946,304],[304]],[[0,0],[0]],[[2939094,8],[8]],[[0]],[[477901]],[[0]],[[55650]],[[0]],[[4341]],[[0]],[[200]],[[0]],[[4]]]
theorem step110 : p110=NestedHorner.add p108 p109 := by decide +kernel
#print axioms step110
theorem h110 : NestedArithmetic.compile e110=p110 := StagedExprCompile.compile_plus e110 e108 e109 p108 p109 p110 rfl h108 h109 step110
#print axioms h110
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
