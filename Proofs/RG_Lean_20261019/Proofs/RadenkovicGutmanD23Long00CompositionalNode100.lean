/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode043
import Proofs.RadenkovicGutmanD23Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-4761],[0,-9522,2898],[-4761,2898]],[[0,0,0],[0,0,0],[0,0]],[[0,-188163,-15180],[-188163,13110,12558],[-15180,12558]],[[0,0,0],[0,0,0],[0,0]],[[-1751220,-1534491,42389],[-1534491,374578,15456],[42389,15456]],[[0,0,0],[0,0,0],[0,0]],[[-21188520,-4718979,261970],[-4718979,1276454,6762],[261970,6762]],[[0,0,0],[0,0,0],[0,0]],[[-113527494,-5592036,496386],[-5592036,2012868,966],[496386,966]],[[0,0,0],[0,0],[0]],[[-355191990,3980633,482126],[3980633,1764100],[482126]],[[0,0,0],[0,0],[0]],[[-715704110,23175881,265305],[23175881,905418],[265305]],[[0,0,0],[0,0],[0]],[[-954148376,37186768,83398],[37186768,270158],[83398]],[[0,0,0],[0,0],[0]],[[-801632478,34637379,13961],[34637379,43378],[13961]],[[0,0,0],[0,0],[0]],[[-300060484,21065401,966],[21065401,2898],[966]],[[0,0],[0]],[[195695960,8628450],[8628450]],[[0,0],[0]],[[397942550,2365435],[2365435]],[[0,0],[0]],[[327806902,416645],[416645]],[[0,0],[0]],[[173774706,42665],[42665]],[[0,0],[0]],[[64470426,1932],[1932]],[[0]],[[17014020]],[[0]],[[3143870]],[[0]],[[387688]],[[0]],[[28704]],[[0]],[[966]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
