/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode289
import Proofs.RadenkovicGutmanD29Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e290 : NestedArithmetic.Expr 3 := .times e289 e003
noncomputable def p290 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[3364,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[100920,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1389332,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[11632712,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[66196792,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[271024024,3364,0],[3364,0],[0]],[[0,0,0],[0,0],[0]],[[824459212,74008,0],[74008,0],[0]],[[0,0,0],[0,0],[0]],[[1897706408,723260,0],[723260,0],[0]],[[0,0,0],[0,0],[0]],[[3334807208,4137720,0],[4137720,0],[0]],[[0,0,0],[0,0],[0]],[[4481796648,15376844,0],[15376844,0],[0]],[[0,0,0],[0,0],[0]],[[4584092524,38955120,841],[38955120,1682],[841]],[[0,0,0],[0,0],[0]],[[3525276888,68713064,11774],[68713064,23548],[11774]],[[0,0,0],[0,0],[0]],[[1994764536,84705520,68121],[84705520,136242],[68121]],[[0,0,0],[0,0],[0]],[[801284616,72161164,210250],[72161164,420500],[210250]],[[0,0,0],[0,0],[0]],[[214989876,41276280,373404],[41276280,746808],[373404]],[[0,0,0],[0,0],[0]],[[34332984,14986620,385178],[14986620,770356],[385178]],[[0,0,0],[0,0],[0]],[[2452356,3088152,222865],[3088152,445730],[222865]],[[0,0,0],[0,0],[0]],[[0,272484,65598],[272484,131196],[65598]],[[0,0,0],[0,0],[0]],[[0,0,7569],[0,15138],[7569]]]
theorem step290 : p290=NestedArithmetic.mul p289 p003 := by decide +kernel
#print axioms step290
theorem h290 : NestedArithmetic.compile e290=p290 := StagedExprCompile.compile_times e290 e289 e003 p289 p003 p290 rfl h289 h003 step290
#print axioms h290
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
