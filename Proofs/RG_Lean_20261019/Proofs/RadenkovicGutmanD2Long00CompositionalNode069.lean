/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode042
import Proofs.RadenkovicGutmanD2Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e069 : NestedArithmetic.Expr 3 := .times e042 e064
noncomputable def p069 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-12],[0,-12,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-108,-180],[-108,-720,-64],[-180,-64,0]],[[0,0,0],[0,0,0],[0,0]],[[-3240,-8964,-1488],[-8964,-6096,-116],[-1488,-116]],[[0,0,0],[0,0,0],[0,0]],[[-117720,-94104,-4964],[-94104,-21104,-92],[-4964,-92]],[[0,0,0],[0,0,0],[0,0]],[[-1311984,-453856,-8780],[-453856,-39360,-32],[-8780,-32]],[[0,0,0],[0,0,0],[0,0]],[[-7636944,-1282720,-9124],[-1282720,-43824,-4],[-9124,-4]],[[0,0,0],[0,0,0],[0,0]],[[-27854056,-2354928,-5820],[-2354928,-30384,0],[-5820,0]],[[0,0,0],[0,0],[0]],[[-69614888,-2962880,-2300],[-2962880,-13200],[-2300]],[[0,0,0],[0,0],[0]],[[-125530656,-2630588,-548],[-2630588,-3488],[-548]],[[0,0,0],[0,0],[0]],[[-168640312,-1671776,-72],[-1671776,-512],[-72]],[[0,0,0],[0,0],[0]],[[-172270080,-762352,-4],[-762352,-32],[-4]],[[0,0,0],[0,0],[0]],[[-135499264,-247068,0],[-247068,0],[0]],[[0,0],[0]],[[-82593064,-55476],[-55476]],[[0,0],[0]],[[-39056896,-8196],[-8196]],[[0,0],[0]],[[-14265224,-716],[-716]],[[0,0],[0]],[[-3980488,-28],[-28]],[[0,0],[0]],[[-831920,0],[0]],[[0]],[[-125944]],[[0]],[[-13032]],[[0]],[[-824]],[[0]],[[-24]],[[0]],[[0]]]
theorem step069 : p069=NestedArithmetic.mul p042 p064 := by decide +kernel
#print axioms step069
theorem h069 : NestedArithmetic.compile e069=p069 := StagedExprCompile.compile_times e069 e042 e064 p042 p064 p069 rfl h042 h064 step069
#print axioms h069
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
