/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode089
import Proofs.RadenkovicGutmanD19Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2166],[0,2166,-646]],[[0,0,0],[0,0,0],[0,0]],[[0,0,25992],[0,87723,-2128],[25992,-2128]],[[0,0,0],[0,0,0],[0,0]],[[81567,712557,141474],[712557,425106,-18962],[141474,-18962]],[[0,0,0],[0,0,0],[0,0]],[[6081615,6253470,296324],[6253470,706971,-22762],[296324,-22762]],[[0,0,0],[0,0,0],[0,0]],[[66389382,23942223,269154],[23942223,249926,-9348],[269154,-9348]],[[0,0,0],[0,0,0],[0,0]],[[348738711,52300236,33326],[52300236,-668116,-1254],[33326,-1254]],[[0,0,0],[0,0],[0]],[[1117538105,71394913,-137370],[71394913,-1000730],[-137370]],[[0,0,0],[0,0],[0]],[[2415948686,62140222,-119928],[62140222,-625917],[-119928]],[[0,0,0],[0,0],[0]],[[3711819176,32589674,-45258],[32589674,-206302],[-45258]],[[0,0,0],[0,0],[0]],[[4166894237,7191196,-8322],[7191196,-35093],[-8322]],[[0,0,0],[0,0],[0]],[[3458143830,-2652685,-608],[-2652685,-2432],[-608]],[[0,0],[0]],[[2114869974,-2741586],[-2741586]],[[0,0],[0]],[[929891008,-1035329],[-1035329]],[[0,0],[0]],[[272662673,-215384],[-215384]],[[0,0],[0]],[[39043309,-24377],[-24377]],[[0,0],[0]],[[-5999858,-1178],[-1178]],[[0]],[[-4809964]],[[0]],[[-1273893]],[[0]],[[-189411]],[[0]],[[-15713]],[[0]],[[-570]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
