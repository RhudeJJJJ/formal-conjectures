/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode035
import Proofs.RadenkovicGutmanD42Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-15876],[0,-31752,10080],[-15876,10080]],[[0,0,0],[0,0,0],[0,0]],[[0,-433188,-46872],[-433188,87696,43680],[-46872,43680]],[[0,0,0],[0,0,0],[0,0]],[[-2653560,-2229444,167580],[-2229444,1605240,53760],[167580,53760]],[[0,0,0],[0,0,0],[0,0]],[[-18302760,2250612,946008],[2250612,5399856,23520],[946008,23520]],[[0,0,0],[0,0,0],[0,0]],[[2862216,43899240,1760304],[43899240,8607648,3360],[1760304,3360]],[[0,0,0],[0,0],[0]],[[455547456,149591988,1695960],[149591988,7665840],[1695960]],[[0,0,0],[0,0],[0]],[[2286967536,275305212,928956],[275305212,4001592],[928956]],[[0,0,0],[0,0],[0]],[[6216783216,322630896,291144],[322630896,1213968],[291144]],[[0,0,0],[0,0],[0]],[[11182391976,255716244,48636],[255716244,198072],[48636]],[[0,0,0],[0,0],[0]],[[14341441128,140338044,3360],[140338044,13440],[3360]],[[0,0],[0]],[[13607586048,53421816],[53421816]],[[0,0],[0]],[[9739768248,13846140],[13846140]],[[0,0],[0]],[[5305257048,2331252],[2331252]],[[0,0],[0]],[[2200219728,229908],[229908]],[[0,0],[0]],[[689477712,10080],[10080]],[[0]],[[160437312]],[[0]],[[26856312]],[[0]],[[3055752]],[[0]],[[211512]],[[0]],[[6720]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
