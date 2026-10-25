/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode035
import Proofs.RadenkovicGutmanD32Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e076 : NestedArithmetic.Expr 3 := .times e035 e074
noncomputable def p076 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,-9216],[0,-18432],[-9216]],[[0,0,0],[0,0],[0]],[[0,-304128,-79872],[-304128,-159744],[-79872]],[[0,0,0],[0,0],[0]],[[-2488320,-3400704,-271360],[-3400704,-542720],[-271360]],[[0,0,0],[0,0],[0]],[[-34007040,-16247808,-468992],[-16247808,-937984],[-468992]],[[0,0,0],[0,0],[0]],[[-207304704,-43980800,-454656],[-43980800,-909312],[-454656]],[[0,0,0],[0,0],[0]],[[-750403584,-75492352,-256000],[-75492352,-512000],[-256000]],[[0,0,0],[0,0],[0]],[[-1811042304,-86975488,-82944],[-86975488,-165888],[-82944]],[[0,0,0],[0,0],[0]],[[-3098742784,-69259264,-14336],[-69259264,-28672],[-14336]],[[0,0,0],[0,0],[0]],[[-3897759744,-38562816,-1024],[-38562816,-2048],[-1024]],[[0,0],[0]],[[-3684308992,-14959616],[-14959616]],[[0,0],[0]],[[-2649833472,-3958784],[-3958784]],[[0,0],[0]],[[-1457539072,-680960],[-680960]],[[0,0],[0]],[[-612165632,-68608],[-68608]],[[0,0],[0]],[[-194588672,-3072],[-3072]],[[0]],[[-45969408]],[[0]],[[-7815168]],[[0]],[[-903168]],[[0]],[[-63488]],[[0]],[[-2048]]]
theorem step076 : p076=NestedArithmetic.mul p035 p074 := by decide +kernel
#print axioms step076
theorem h076 : NestedArithmetic.compile e076=p076 := StagedExprCompile.compile_times e076 e035 e074 p035 p074 p076 rfl h035 h074 step076
#print axioms h076
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
