/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode051
import Proofs.RadenkovicGutmanD37Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-4107],[0,-4107]],[[0,0,0],[0,0,0],[0,0]],[[0,36963,-61605],[36963,-184815,-18019],[-61605,-18019]],[[0,0,0],[0,0,0],[0,0]],[[554445,-1221777,-474303],[-1221777,-1362636,-22866],[-474303,-22866]],[[0,0,0],[0,0,0],[0,0]],[[-3171825,-14883768,-1454174],[-14883768,-3996999,-10767],[-1454174,-10767]],[[0,0,0],[0,0,0],[0,0]],[[-93580326,-69914645,-2328965],[-69914645,-6161240,-1887],[-2328965,-1887]],[[0,0,0],[0,0,0],[0,0]],[[-651107019,-183963852,-2142374],[-183963852,-5496424,-74],[-2142374,-74]],[[0,0,0],[0,0],[0]],[[-2466460219,-307740877,-1168275],[-307740877,-2928994],[-1168275]],[[0,0,0],[0,0],[0]],[[-6070663704,-347408170,-374070],[-347408170,-923335],[-374070]],[[0,0,0],[0,0],[0]],[[-10492426552,-272635869,-65823],[-272635869,-161468],[-65823]],[[0,0,0],[0,0],[0]],[[-13282192031,-150457799,-5217],[-150457799,-12987],[-5217]],[[0,0,0],[0,0],[0]],[[-12618807598,-58202110,-74],[-58202110,-222],[-74]],[[0,0],[0]],[[-9121042716,-15475250],[-15475250]],[[0,0],[0]],[[-5045127452,-2706698],[-2706698]],[[0,0],[0]],[[-2133385553,-284456],[-284456]],[[0,0],[0]],[[-684088375,-14504],[-14504]],[[0,0],[0]],[[-163540740,-148],[-148]],[[0]],[[-28289460]],[[0]],[[-3362005]],[[0]],[[-249269]],[[0]],[[-9287]],[[0]],[[-74]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
