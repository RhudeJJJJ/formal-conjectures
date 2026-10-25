/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode092
import Proofs.RadenkovicGutmanD8Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-576,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5184,-5184,0],[-5184,-4848,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-135216,-57456,0],[-57456,-15712,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1313712,-270432,0],[-270432,-25072,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6926592,-714000,0],[-714000,-21088,0],[0,0]],[[0,0,0],[0,0],[0]],[[-23007088,-1176544,0],[-1176544,-8896],[0]],[[0,0,0],[0,0],[0]],[[-52000848,-1268304,0],[-1268304,-1184],[0]],[[0,0,0],[0,0],[0]],[[-83591328,-904384,0],[-904384,400],[0]],[[0,0,0],[0,0],[0]],[[-98010368,-414304,0],[-414304,160],[0]],[[0,0,0],[0,0],[0]],[[-84790672,-107264,0],[-107264,16],[0]],[[0,0],[0]],[[-54029216,-5584],[-5584]],[[0,0],[0]],[[-24840352,5920],[5920]],[[0,0],[0]],[[-7741120,2032],[2032]],[[0,0],[0]],[[-1298064,288],[288]],[[0,0],[0]],[[83696,16],[16]],[[0]],[[114912]],[[0]],[[32832]],[[0]],[[5072]],[[0]],[[432]],[[0]],[[16]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
