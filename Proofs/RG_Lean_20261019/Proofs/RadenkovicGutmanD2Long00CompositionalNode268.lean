/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode267
import Proofs.RadenkovicGutmanD2Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e268 : NestedArithmetic.Expr 3 := .times e267 e003
noncomputable def p268 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,0],[0,0],[0,0]],[[-24,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-728,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-10120,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-85440,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-489504,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2014320,-28,0],[-28,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6146984,-604,0],[-604,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-14162920,-5780,0],[-5780,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-24851584,-32328,0],[-32328,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-33257080,-117236,0],[-117236,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-33766680,-289212,-4],[-289212,-8,0],[-4,0]],[[0,0,0],[0,0,0],[0,0]],[[-25690832,-495632,-56],[-495632,-112,0],[-56,0]],[[0,0,0],[0,0,0],[0,0]],[[-14332544,-592276,-324],[-592276,-648,0],[-324,0]],[[0,0,0],[0,0,0],[0,0]],[[-5657280,-488188,-1000],[-488188,-2000,0],[-1000,0]],[[0,0,0],[0,0,0],[0,0]],[[-1487160,-269880,-1776],[-269880,-3552,0],[-1776,0]],[[0,0,0],[0,0,0],[0,0]],[[-232200,-94716,-1832],[-94716,-3664,0],[-1832,0]],[[0,0,0],[0,0,0],[0,0]],[[-16200,-18900,-1060],[-18900,-2120,0],[-1060,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-1620,-312],[-1620,-624,0],[-312,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,-36],[0,-72,0],[-36,0]]]
theorem step268 : p268=NestedArithmetic.mul p267 p003 := by decide +kernel
#print axioms step268
theorem h268 : NestedArithmetic.compile e268=p268 := StagedExprCompile.compile_times e268 e267 e003 p267 p003 p268 rfl h267 h003 step268
#print axioms h268
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
