/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,7569],[0,15138],[7569]],[[0,0,0],[0,0],[0]],[[0,249777,65598],[249777,131196],[65598]],[[0,0,0],[0,0],[0]],[[2043630,2792961,222865],[2792961,445730],[222865]],[[0,0,0],[0,0],[0]],[[27929610,13344147,385178],[13344147,770356],[385178]],[[0,0,0],[0,0],[0]],[[170257086,36120950,373404],[36120950,746808],[373404]],[[0,0,0],[0,0],[0]],[[616298256,62001043,210250],[62001043,420500],[210250]],[[0,0,0],[0,0],[0]],[[1487389236,71432017,68121],[71432017,136242],[68121]],[[0,0,0],[0,0],[0]],[[2544963556,56881876,11774],[56881876,23548],[11774]],[[0,0,0],[0,0],[0]],[[3201187446,31671219,841],[31671219,1682],[841]],[[0,0],[0]],[[3025882678,12286169],[12286169]],[[0,0],[0]],[[2176279248,3251306],[3251306]],[[0,0],[0]],[[1197060898,559265],[559265]],[[0,0],[0]],[[502764938,56347],[56347]],[[0,0],[0]],[[159813548,2523],[2523]],[[0]],[[37754172]],[[0]],[[6418512]],[[0]],[[741762]],[[0]],[[52142]],[[0]],[[1682]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
