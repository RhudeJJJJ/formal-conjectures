/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode113
import Proofs.RadenkovicGutmanD8Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,64]],[[0,0],[0,0,0],[0,0]],[[0,0,576],[0,0,1152],[576,1152]],[[0,0,0],[0,0,0],[0,0]],[[5184,10368,10176],[10368,20736,3072],[10176,3072]],[[0,0,0],[0,0,0],[0,0]],[[183168,210816,44608],[210816,110592,2816],[44608,2816]],[[0,0,0],[0,0,0],[0,0]],[[2420928,1316736,91520],[1316736,248832,1024],[91520,1024]],[[0,0,0],[0,0,0],[0,0]],[[15832704,4245504,105216],[4245504,307200,128],[105216,128]],[[0,0,0],[0,0],[0]],[[62089024,8413568,72704],[8413568,226816],[72704]],[[0,0,0],[0,0],[0]],[[162346240,11120000,30784],[11120000,102400],[30784]],[[0,0,0],[0,0],[0]],[[301218688,10226944,7808],[10226944,27648],[7808]],[[0,0,0],[0,0],[0]],[[412196992,6683648,1088],[6683648,4096],[1088]],[[0,0,0],[0,0],[0]],[[426323968,3122560,64],[3122560,256],[64]],[[0,0],[0]],[[338324480,1034880],[1034880]],[[0,0],[0]],[[207677440,237440],[237440]],[[0,0],[0]],[[98814848,35840],[35840]],[[0,0],[0]],[[36307264,3200],[3200]],[[0,0],[0]],[[10193664,128],[128]],[[0]],[[2144640]],[[0]],[[327040]],[[0]],[[34112]],[[0]],[[2176]],[[0]],[[64]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
