/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode093
import Proofs.RadenkovicGutmanD14Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,196]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-1764],[0,-3528,5712],[-1764,5712,28]],[[0,0,0],[0,0,0],[0,0]],[[-15876,-59724,20244],[-59724,108024,19376],[20244,19376]],[[0,0,0],[0,0,0],[0,0]],[[-749196,114156,172592],[114156,763672,21616],[172592,21616]],[[0,0,0],[0,0,0],[0,0]],[[-4367412,3878028,492856],[3878028,2047080,9464],[492856,9464]],[[0,0,0],[0,0,0],[0,0]],[[746844,19475120,726488],[19475120,2900464,1568],[726488,1568]],[[0,0,0],[0,0,0],[0,0]],[[95766356,50385524,621264],[50385524,2409008,56],[621264,56]],[[0,0,0],[0,0],[0]],[[463245468,81346188,319564],[81346188,1212008],[319564]],[[0,0,0],[0,0],[0]],[[1229637304,88365256,98056],[88365256,365960],[98056]],[[0,0,0],[0,0],[0]],[[2179633344,66879820,16884],[66879820,62440],[16884]],[[0,0,0],[0,0],[0]],[[2773993824,35752836,1372],[35752836,5096],[1372]],[[0,0,0],[0,0],[0]],[[2626580544,13473712,28],[13473712,112],[28]],[[0,0],[0]],[[1885075752,3515540],[3515540]],[[0,0],[0]],[[1034121592,609812],[609812]],[[0,0],[0]],[[433896820,64820],[64820]],[[0,0],[0]],[[138295836,3528],[3528]],[[0,0],[0]],[[32967816,56],[56]],[[0]],[[5717488]],[[0]],[[687932]],[[0]],[[52724]],[[0]],[[2156]],[[0]],[[28]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
