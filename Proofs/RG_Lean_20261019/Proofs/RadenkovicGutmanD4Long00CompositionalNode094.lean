/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode092
import Proofs.RadenkovicGutmanD4Long00CompositionalNode093
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .plus e092 e093
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,16]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-144],[0,-288,432],[-144,432,8]],[[0,0,0],[0,0,0],[0,0]],[[-1296,-5184,1344],[-5184,7584,1536],[1344,1536]],[[0,0,0],[0,0,0],[0,0]],[[-67176,-3024,12392],[-3024,55552,1856],[12392,1856]],[[0,0,0],[0,0,0],[0,0]],[[-501552,222048,36736],[222048,153120,944],[36736,944]],[[0,0,0],[0,0,0],[0,0]],[[-1187976,1249440,56208],[1249440,224384,208],[56208,208]],[[0,0,0],[0,0,0],[0,0]],[[1987856,3400784,50304],[3400784,195008,16],[50304,16]],[[0,0,0],[0,0],[0]],[[20536568,5700528,27504],[5700528,104608],[27504]],[[0,0,0],[0,0],[0]],[[65177504,6415376,9216],[6415376,34720],[9216]],[[0,0,0],[0,0],[0]],[[126424464,5043520,1824],[5043520,6880],[1824]],[[0,0,0],[0,0],[0]],[[171000384,2818016,192],[2818016,736],[192]],[[0,0,0],[0,0],[0]],[[170056704,1121552,8],[1121552,32],[8]],[[0,0],[0]],[[127621472,314240],[314240]],[[0,0],[0]],[[73192672,60192],[60192]],[[0,0],[0]],[[32202640,7440],[7440]],[[0,0],[0]],[[10830776,528],[528]],[[0,0],[0]],[[2753376,16],[16]],[[0]],[[517968]],[[0]],[[69552]],[[0]],[[6264]],[[0]],[[336]],[[0]],[[8]]]
theorem step094 : p094=NestedHorner.add p092 p093 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_plus e094 e092 e093 p092 p093 p094 rfl h092 h093 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
