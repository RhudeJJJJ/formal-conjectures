/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode032
import Proofs.RadenkovicGutmanD4Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e074 : NestedArithmetic.Expr 3 := .times e032 e052
noncomputable def p074 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,16]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,288],[0,288]],[[0,0,0],[0,0,0],[0,0]],[[-1296,0,1296],[0,5184,768],[1296,768]],[[0,0,0],[0,0,0],[0,0]],[[-22464,23328,6912],[23328,27648,704],[6912,704]],[[0,0,0],[0,0,0],[0,0]],[[-68688,186624,15552],[186624,62208,256],[15552,256]],[[0,0,0],[0,0,0],[0,0]],[[326400,668736,19200],[668736,76800,32],[19200,32]],[[0,0,0],[0,0],[0]],[[3110768,1416960,14176],[1416960,56704],[14176]],[[0,0,0],[0,0],[0]],[[11483264,1974240,6400],[1974240,25600],[6400]],[[0,0,0],[0,0],[0]],[[26233184,1903104,1728],[1903104,6912],[1728]],[[0,0,0],[0,0],[0]],[[41776192,1300352,256],[1300352,1024],[256]],[[0,0,0],[0,0],[0]],[[48867392,634368,16],[634368,64],[16]],[[0,0],[0]],[[43138112,219360],[219360]],[[0,0],[0]],[[29138432,52480],[52480]],[[0,0],[0]],[[15137920,8256],[8256]],[[0,0],[0]],[[6036336,768],[768]],[[0,0],[0]],[[1830144,32],[32]],[[0]],[[414048]],[[0]],[[67648]],[[0]],[[7536]],[[0]],[[512]],[[0]],[[16]]]
theorem step074 : p074=NestedArithmetic.mul p032 p052 := by decide +kernel
#print axioms step074
theorem h074 : NestedArithmetic.compile e074=p074 := StagedExprCompile.compile_times e074 e032 e052 p032 p052 p074 rfl h032 h052 step074
#print axioms h074
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
