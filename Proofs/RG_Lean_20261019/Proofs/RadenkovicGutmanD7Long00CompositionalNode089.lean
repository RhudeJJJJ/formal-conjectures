/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode033
import Proofs.RadenkovicGutmanD7Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,147],[0,147,-70]],[[0,0,0],[0,0,0],[0,0]],[[0,-1323,1323],[-1323,4851,-623],[1323,-623]],[[0,0,0],[0,0,0],[0,0]],[[-14175,14553,3591],[14553,10542,-2576],[3591,-2576]],[[0,0,0],[0,0,0],[0,0]],[[-27405,102564,-4662],[102564,-31633,-2737],[-4662,-2737]],[[0,0,0],[0,0,0],[0,0]],[[369306,109571,-30947],[109571,-146230,-1071],[-30947,-1071]],[[0,0,0],[0,0,0],[0,0]],[[1809087,-632814,-52836],[-632814,-233100,-140],[-52836,-140]],[[0,0,0],[0,0],[0]],[[1777811,-2597161,-46389],[-2597161,-197806],[-46389]],[[0,0,0],[0,0],[0]],[[-9511950,-4804814,-23394],[-4804814,-97545],[-23394]],[[0,0,0],[0,0],[0]],[[-42478520,-5477759,-6825],[-5477759,-27986],[-6825]],[[0,0,0],[0,0],[0]],[[-90441365,-4194197,-1071],[-4194197,-4333],[-1071]],[[0,0,0],[0,0],[0]],[[-125972140,-2224110,-70],[-2224110,-280],[-70]],[[0,0],[0]],[[-125409284,-820050],[-820050]],[[0,0],[0]],[[-92620472,-206472],[-206472]],[[0,0],[0]],[[-51583035,-33866],[-33866]],[[0,0],[0]],[[-21753333,-3262],[-3262]],[[0,0],[0]],[[-6907026,-140],[-140]],[[0]],[[-1624476]],[[0]],[[-274351]],[[0]],[[-31451]],[[0]],[[-2191]],[[0]],[[-70]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
