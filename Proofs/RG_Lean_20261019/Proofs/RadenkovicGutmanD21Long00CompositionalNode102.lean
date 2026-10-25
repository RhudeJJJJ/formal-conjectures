/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode100
import Proofs.RadenkovicGutmanD21Long00CompositionalNode101
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e102 : NestedArithmetic.Expr 3 := .plus e100 e101
noncomputable def p102 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,441]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-3969],[0,-7938,12978],[-3969,12978,42]],[[0,0,0],[0,0,0],[0,0]],[[-35721,-133245,46683],[-133245,249102,43764],[46683,43764]],[[0,0,0],[0,0,0],[0,0]],[[-1649970,315819,394569],[315819,1756314,48300],[394569,48300]],[[0,0,0],[0,0,0],[0,0]],[[-8935353,9227169,1121778],[9227169,4701858,20664],[1121778,20664]],[[0,0,0],[0,0,0],[0,0]],[[9808344,45818304,1645980],[45818304,6648516,3234],[1645980,3234]],[[0,0,0],[0,0,0],[0,0]],[[255965661,118046565,1399356],[118046565,5500908,84],[1399356,84]],[[0,0,0],[0,0],[0]],[[1170964368,190087107,713811],[190087107,2748186],[713811]],[[0,0,0],[0,0],[0]],[[3048840102,205985136,216174],[205985136,819210],[216174]],[[0,0,0],[0,0],[0]],[[5351080434,155440173,36351],[155440173,136290],[36351]],[[0,0,0],[0,0],[0]],[[6766941384,82758963,2793],[82758963,10458],[2793]],[[0,0,0],[0,0],[0]],[[6375818400,31004190,42],[31004190,168],[42]],[[0,0],[0]],[[4555510050,8016435],[8016435]],[[0,0],[0]],[[2487626862,1369935],[1369935]],[[0,0],[0]],[[1038312597,141645],[141645]],[[0,0],[0]],[[328813800,7224],[7224]],[[0,0],[0]],[[77720202,84],[84]],[[0]],[[13317150]],[[0]],[[1572711]],[[0]],[[116634]],[[0]],[[4431]],[[0]],[[42]]]
theorem step102 : p102=NestedHorner.add p100 p101 := by decide +kernel
#print axioms step102
theorem h102 : NestedArithmetic.compile e102=p102 := StagedExprCompile.compile_plus e102 e100 e101 p100 p101 p102 rfl h100 h101 step102
#print axioms h102
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
