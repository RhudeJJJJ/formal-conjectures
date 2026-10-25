/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode033
import Proofs.RadenkovicGutmanD26Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2028],[0,2028]],[[0,0,0],[0,0,0],[0,0]],[[0,-18252,18252],[-18252,66924,8788],[18252,8788]],[[0,0,0],[0,0,0],[0,0]],[[-273780,200772,127764],[200772,458328,10816],[127764,10816]],[[0,0,0],[0,0,0],[0,0]],[[-1733940,2822976,352872],[2822976,1232348,4732],[352872,4732]],[[0,0,0],[0,0,0],[0,0]],[[949104,12775724,511732],[12775724,1737320,676],[511732,676]],[[0,0,0],[0,0],[0]],[[44658588,31632744,429936],[31632744,1419600],[429936]],[[0,0,0],[0,0],[0]],[[212283604,49693436,215644],[49693436,693576],[215644]],[[0,0,0],[0,0],[0]],[[561870920,52872664,63544],[52872664,199420],[63544]],[[0,0,0],[0,0],[0]],[[997329840,39295204,10140],[39295204,31096],[10140]],[[0,0,0],[0,0],[0]],[[1273769900,20622732,676],[20622732,2028],[676]],[[0,0],[0]],[[1211594800,7605000],[7605000]],[[0,0],[0]],[[873556944,1926600],[1926600]],[[0,0],[0]],[[480928032,319072],[319072]],[[0,0],[0]],[[202046260,31096],[31096]],[[0,0],[0]],[[64228788,1352],[1352]],[[0]],[[15173496]],[[0]],[[2579616]],[[0]],[[298116]],[[0]],[[20956]],[[0]],[[676]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
