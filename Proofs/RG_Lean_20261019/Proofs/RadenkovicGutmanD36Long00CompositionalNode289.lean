/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode217
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e289 : NestedArithmetic.Expr 3 := .pow e217 2
noncomputable def p289 : NestedHorner.Poly 3 := [[[5184],[0],[0]],[[0,0],[0,0],[0]],[[155520,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[2140992,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[17926272,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[102010752,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[417654144,5184,0],[5184,0],[0]],[[0,0,0],[0,0],[0]],[[1270510272,114048,0],[114048,0],[0]],[[0,0,0],[0,0],[0]],[[2924408448,1114560,0],[1114560,0],[0]],[[0,0,0],[0,0],[0]],[[5139013248,6376320,0],[6376320,0],[0]],[[0,0,0],[0,0],[0]],[[6906549888,23696064,0],[23696064,0],[0]],[[0,0,0],[0,0],[0]],[[7064190144,60030720,1296],[60030720,2592],[1296]],[[0,0,0],[0,0],[0]],[[5432531328,105888384,18144],[105888384,36288],[18144]],[[0,0,0],[0,0],[0]],[[3073977216,130533120,104976],[130533120,209952],[104976]],[[0,0,0],[0,0],[0]],[[1234797696,111201984,324000],[111201984,648000],[324000]],[[0,0,0],[0,0],[0]],[[331304256,63607680,575424],[63607680,1150848],[575424]],[[0,0,0],[0,0],[0]],[[52907904,23094720,593568],[23094720,1187136],[593568]],[[0,0,0],[0,0],[0]],[[3779136,4758912,343440],[4758912,686880],[343440]],[[0,0,0],[0,0],[0]],[[0,419904,101088],[419904,202176],[101088]],[[0,0,0],[0,0],[0]],[[0,0,11664],[0,23328],[11664]]]
theorem step289 : p289=NestedArithmetic.power p217 2 := by decide +kernel
#print axioms step289
theorem h289 : NestedArithmetic.compile e289=p289 := StagedExprCompile.compile_pow 2 e289 e217 p217 p289 rfl h217 step289
#print axioms h289
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
