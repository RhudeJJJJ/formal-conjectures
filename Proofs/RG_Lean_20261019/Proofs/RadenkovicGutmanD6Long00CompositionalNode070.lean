/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode067
import Proofs.RadenkovicGutmanD6Long00CompositionalNode069
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e070 : NestedArithmetic.Expr 3 := .plus e067 e069
noncomputable def p070 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,36]],[[0,0],[0,0,0],[0,0,0]],[[0,0,324],[0,648,792],[324,792,88]],[[0,0,0],[0,0,0],[0,0,0]],[[-2916,11988,8316],[11988,24480,4080],[8316,4080,4]],[[0,0,0],[0,0,0],[0,0]],[[47952,262764,53820],[262764,168600,7272],[53820,7272]],[[0,0,0],[0,0,0],[0,0]],[[1728000,2021436,162108],[2021436,520928,5744],[162108,5744]],[[0,0,0],[0,0,0],[0,0]],[[16757280,8209632,273792],[8209632,897744,2040],[273792,2040]],[[0,0,0],[0,0,0],[0,0]],[[86827656,20599452,281184],[20599452,943120,288],[281184,288]],[[0,0,0],[0,0,0],[0,0]],[[287798632,34575356,181924],[34575356,626760,8],[181924,8]],[[0,0,0],[0,0],[0]],[[664474868,40592416,74624],[40592416,264976],[74624]],[[0,0,0],[0,0],[0]],[[1121985656,34187124,18964],[34187124,69560],[18964]],[[0,0,0],[0,0],[0]],[[1428062240,20910996,2788],[20910996,10576],[2788]],[[0,0,0],[0,0],[0]],[[1396626992,9306288,200],[9306288,784],[200]],[[0,0,0],[0,0],[0]],[[1061783064,2987092,4],[2987092,16],[4]],[[0,0],[0]],[[631173816,676340],[676340]],[[0,0],[0]],[[293604492,103516],[103516]],[[0,0],[0]],[[106419816,9880],[9880]],[[0,0],[0]],[[29754148,496],[496]],[[0,0],[0]],[[6304584,8],[8]],[[0]],[[983596]],[[0]],[[107760]],[[0]],[[7632]],[[0]],[[296]],[[0]],[[4]]]
theorem step070 : p070=NestedHorner.add p067 p069 := by decide +kernel
#print axioms step070
theorem h070 : NestedArithmetic.compile e070=p070 := StagedExprCompile.compile_plus e070 e067 e069 p067 p069 p070 rfl h067 h069 step070
#print axioms h070
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
