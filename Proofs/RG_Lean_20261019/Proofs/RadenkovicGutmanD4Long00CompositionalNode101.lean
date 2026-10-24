/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode099
import Proofs.RadenkovicGutmanD4Long00CompositionalNode100
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .plus e099 e100
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,16]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-144],[0,-288,432],[-144,432,8]],[[0,0,0],[0,0,0],[0,0]],[[-1296,-5184,1344],[-5184,7872,1536],[1344,1536]],[[0,0,0],[0,0,0],[0,0]],[[-64584,-432,12392],[-432,58048,1856],[12392,1856]],[[0,0,0],[0,0,0],[0,0]],[[-433296,251424,36736],[251424,161600,944],[36736,944]],[[0,0,0],[0,0,0],[0,0]],[[-514056,1392000,56208],[1392000,239040,208],[56208,208]],[[0,0,0],[0,0,0],[0,0]],[[5619632,3793424,50304],[3793424,209216,16],[50304,16]],[[0,0,0],[0,0],[0]],[[32948056,6386960,27504],[6386960,112608],[27504]],[[0,0,0],[0,0],[0]],[[94280800,7221136,9216],[7221136,37312],[9216]],[[0,0,0],[0,0],[0]],[[175495952,5697152,1824],[5697152,7328],[1824]],[[0,0,0],[0,0],[0]],[[232273440,3188576,192],[3188576,768],[192]],[[0,0,0],[0,0],[0]],[[227770304,1267824,8],[1267824,32],[8]],[[0,0],[0]],[[169064480,353600],[353600]],[[0,0],[0]],[[95973600,67072],[67072]],[[0,0],[0]],[[41768432,8144],[8144]],[[0,0],[0]],[[13871256,560],[560]],[[0,0],[0]],[[3471648,16],[16]],[[0]],[[640080]],[[0]],[[83664]],[[0]],[[7256]],[[0]],[[368]],[[0]],[[8]]]
theorem step101 : p101=NestedHorner.add p099 p100 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_plus e101 e099 e100 p099 p100 p101 rfl h099 h100 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
