/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode089
import Proofs.RadenkovicGutmanD44Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,11616],[0,11616,-3696]],[[0,0,0],[0,0,0],[0,0]],[[0,0,139392],[0,470448,-15928],[139392,-15928]],[[0,0,0],[0,0,0],[0,0]],[[456192,3818232,736824],[3818232,2192256,-114312],[736824,-114312]],[[0,0,0],[0,0,0],[0,0]],[[32883840,33073920,1467224],[33073920,3303696,-134112],[1467224,-134112]],[[0,0,0],[0,0,0],[0,0]],[[355644432,124656048,1157904],[124656048,198176,-54648],[1157904,-54648]],[[0,0,0],[0,0,0],[0,0]],[[1853114736,266677136,-186824],[266677136,-5045216,-7304],[-186824,-7304]],[[0,0,0],[0,0],[0]],[[5887953280,352737088,-1015520],[352737088,-6482080],[-1015520]],[[0,0,0],[0,0],[0]],[[12603916336,290025472,-772728],[290025472,-3874992],[-772728]],[[0,0,0],[0,0],[0]],[[19128159776,131999824,-278608],[131999824,-1249952],[-278608]],[[0,0,0],[0,0],[0]],[[21125154512,8643096,-50072],[8643096,-209968],[-50072]],[[0,0,0],[0,0],[0]],[[17125381680,-29131960,-3608],[-29131960,-14432],[-3608]],[[0,0],[0]],[[10091188624,-19953736],[-19953736]],[[0,0],[0]],[[4142984208,-6829504],[-6829504]],[[0,0],[0]],[[1023989648,-1358984],[-1358984]],[[0,0],[0]],[[34642784,-149952],[-149952]],[[0,0],[0]],[[-85154608,-7128],[-7128]],[[0]],[[-37780864]],[[0]],[[-8789968]],[[0]],[[-1233936]],[[0]],[[-99088]],[[0]],[[-3520]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
