/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode051
import Proofs.RadenkovicGutmanD8Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e101 : NestedArithmetic.Expr 3 := .times e051 e053
noncomputable def p101 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,64]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,1536],[0,1536,16]],[[0,0,0],[0,0,0],[0,0]],[[-5184,3456,8640],[3456,34848,5024],[8640,5024]],[[0,0,0],[0,0,0],[0,0]],[[-26352,234144,53136],[234144,215040,5632],[53136,5632]],[[0,0,0],[0,0,0],[0,0]],[[1305504,1951200,135936],[1951200,552224,2624],[135936,2624]],[[0,0,0],[0,0,0],[0,0]],[[15624240,7562720,189248],[7562720,771648,512],[189248,512]],[[0,0,0],[0,0,0],[0,0]],[[83000672,17382144,157312],[17382144,643456,32],[157312,32]],[[0,0,0],[0,0],[0]],[[267427536,26195936,80608],[26195936,330432],[80608]],[[0,0,0],[0,0],[0]],[[585704128,27228256,25344],[27228256,103968],[25344]],[[0,0,0],[0,0],[0]],[[924195808,20030400,4672],[20030400,19136],[4672]],[[0,0,0],[0,0],[0]],[[1086642208,10536320,448],[10536320,1824],[448]],[[0,0,0],[0,0],[0]],[[971412992,3952992,16],[3952992,64],[16]],[[0,0],[0]],[[667824640,1040800],[1040800]],[[0,0],[0]],[[354749440,185696],[185696]],[[0,0],[0]],[[145436832,20992],[20992]],[[0,0],[0]],[[45679952,1312],[1312]],[[0,0],[0]],[[10829376,32],[32]],[[0]],[[1889120]],[[0]],[[232480]],[[0]],[[18768]],[[0]],[[864]],[[0]],[[16]]]
theorem step101 : p101=NestedArithmetic.mul p051 p053 := by decide +kernel
#print axioms step101
theorem h101 : NestedArithmetic.compile e101=p101 := StagedExprCompile.compile_times e101 e051 e053 p051 p053 p101 rfl h051 h053 step101
#print axioms h101
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
