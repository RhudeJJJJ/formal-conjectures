/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode033
import Proofs.RadenkovicGutmanD33Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3267],[0,3267,-2046]],[[0,0,0],[0,0,0],[0,0]],[[0,-29403,29403],[-29403,107811,-22671],[29403,-22671]],[[0,0,0],[0,0,0],[0,0]],[[-275319,323433,40095],[323433,75438,-80784],[40095,-80784]],[[0,0,0],[0,0,0],[0,0]],[[79299,1564596,-315414],[1564596,-1550241,-82401],[-315414,-82401]],[[0,0,0],[0,0,0],[0,0]],[[10312434,-3283533,-1164339],[-3283533,-5156118,-31647],[-1164339,-31647]],[[0,0,0],[0,0,0],[0,0]],[[30204207,-34555950,-1762596],[-34555950,-7533900,-4092],[-1762596,-4092]],[[0,0,0],[0,0],[0]],[[-55811877,-101140281,-1465365],[-101140281,-6133710],[-1465365]],[[0,0,0],[0,0],[0]],[[-563278254,-167280894,-716034],[-167280894,-2952345],[-716034]],[[0,0,0],[0,0],[0]],[[-1747923144,-180056943,-204633],[-180056943,-833778],[-204633]],[[0,0,0],[0,0],[0]],[[-3290155077,-133060389,-31647],[-133060389,-127677],[-31647]],[[0,0,0],[0,0],[0]],[[-4297103052,-68868558,-2046],[-68868558,-8184],[-2046]],[[0,0],[0]],[[-4109032356,-24947010],[-24947010]],[[0,0],[0]],[[-2951327544,-6196872],[-6196872]],[[0,0],[0]],[[-1610275755,-1005642],[-1005642]],[[0,0],[0]],[[-668427309,-96030],[-96030]],[[0,0],[0]],[[-209585970,-4092],[-4092]],[[0]],[[-48790764]],[[0]],[[-8170239]],[[0]],[[-929907]],[[0]],[[-64383]],[[0]],[[-2046]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
