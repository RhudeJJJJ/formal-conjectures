/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode093
import Proofs.RadenkovicGutmanD21Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,441]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-3969],[0,-7938,12978],[-3969,12978,42]],[[0,0,0],[0,0,0],[0,0]],[[-35721,-133245,46683],[-133245,247590,43764],[46683,43764]],[[0,0,0],[0,0,0],[0,0]],[[-1663578,302211,394569],[302211,1743210,48300],[394569,48300]],[[0,0,0],[0,0,0],[0,0]],[[-9293697,9072945,1121778],[9072945,4657338,20664],[1121778,20664]],[[0,0,0],[0,0,0],[0,0]],[[6270264,45069864,1645980],[45069864,6571572,3234],[1645980,3234]],[[0,0,0],[0,0,0],[0,0]],[[236898837,115985205,1399356],[115985205,5426316,84],[1399356,84]],[[0,0,0],[0,0],[0]],[[1105804056,186483339,713811],[186483339,2706186],[713811]],[[0,0,0],[0,0],[0]],[[2896047798,201754896,216174],[201754896,805602],[216174]],[[0,0,0],[0,0],[0]],[[5093455122,152008605,36351],[152008605,133938],[36351]],[[0,0,0],[0,0],[0]],[[6445257840,80813523,2793],[80813523,10290],[2793]],[[0,0,0],[0,0],[0]],[[6072822000,30236262,42],[30236262,168],[42]],[[0,0],[0]],[[4337934258,7809795],[7809795]],[[0,0],[0]],[[2368026990,1333815],[1333815]],[[0,0],[0]],[[988092189,137949],[137949]],[[0,0],[0]],[[312851280,7056],[7056]],[[0,0],[0]],[[73949274,84],[84]],[[0]],[[12676062]],[[0]],[[1498623]],[[0]],[[111426]],[[0]],[[4263]],[[0]],[[42]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
