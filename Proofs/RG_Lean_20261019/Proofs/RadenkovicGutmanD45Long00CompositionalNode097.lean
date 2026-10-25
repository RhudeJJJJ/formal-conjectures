/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode051
import Proofs.RadenkovicGutmanD45Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-6075],[0,-6075]],[[0,0,0],[0,0,0],[0,0]],[[0,54675,-91125],[54675,-273375,-26595],[-91125,-26595]],[[0,0,0],[0,0,0],[0,0]],[[820125,-1806705,-701055],[-1806705,-2013660,-33570],[-701055,-33570]],[[0,0,0],[0,0,0],[0,0]],[[-4683825,-21996360,-2147310],[-21996360,-5899095,-15615],[-2147310,-15615]],[[0,0,0],[0,0,0],[0,0]],[[-138230550,-103259205,-3434805],[-103259205,-9078120,-2655],[-3434805,-2655]],[[0,0,0],[0,0,0],[0,0]],[[-961430715,-271509660,-3154230],[-271509660,-8080200,-90],[-3154230,-90]],[[0,0,0],[0,0],[0]],[[-3640426875,-453823965,-1715715],[-453823965,-4291650],[-1715715]],[[0,0,0],[0,0],[0]],[[-8955849960,-511835130,-547110],[-511835130,-1345815],[-547110]],[[0,0,0],[0,0],[0]],[[-15470985240,-401208525,-95535],[-401208525,-233100],[-95535]],[[0,0,0],[0,0],[0]],[[-19572968655,-221086215,-7425],[-221086215,-18315],[-7425]],[[0,0,0],[0,0],[0]],[[-18582956190,-85354830,-90],[-85354830,-270],[-90]],[[0,0],[0]],[[-13421532060,-22630770],[-22630770]],[[0,0],[0]],[[-7416913500,-3940650],[-3940650]],[[0,0],[0]],[[-3132685665,-410760],[-410760]],[[0,0],[0]],[[-1003024215,-20520],[-20520]],[[0,0],[0]],[[-239303700,-180],[-180]],[[0]],[[-41274900]],[[0]],[[-4882725]],[[0]],[[-358965]],[[0]],[[-13095]],[[0]],[[-90]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
