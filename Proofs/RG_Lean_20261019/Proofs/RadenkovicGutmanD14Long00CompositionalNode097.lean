/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode051
import Proofs.RadenkovicGutmanD14Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-588],[0,-588]],[[0,0,0],[0,0,0],[0,0]],[[0,5292,-8820],[5292,-26460,-2632],[-8820,-2632]],[[0,0,0],[0,0,0],[0,0]],[[79380,-175392,-68376],[-175392,-196812,-3500],[-68376,-3500]],[[0,0,0],[0,0,0],[0,0]],[[-461160,-2148300,-211484],[-2148300,-584052,-1820],[-211484,-1820]],[[0,0,0],[0,0,0],[0,0]],[[-13569444,-10150364,-342524],[-10150364,-913836,-392],[-342524,-392]],[[0,0,0],[0,0,0],[0,0]],[[-94717308,-26880476,-319900],[-26880476,-831656,-28],[-319900,-28]],[[0,0,0],[0,0],[0]],[[-360204376,-45294340,-178332],[-45294340,-455896],[-178332]],[[0,0,0],[0,0],[0]],[[-890395324,-51567404,-59108],[-51567404,-150052],[-59108]],[[0,0,0],[0,0],[0]],[[-1546229160,-40884396,-11060],[-40884396,-28252],[-11060]],[[0,0,0],[0,0],[0]],[[-1967632268,-22854328,-1008],[-22854328,-2660],[-1008]],[[0,0,0],[0,0],[0]],[[-1880478404,-8991724,-28],[-8991724,-84],[-28]],[[0,0],[0]],[[-1368605952,-2448096],[-2448096]],[[0,0],[0]],[[-763230608,-443912],[-443912]],[[0,0],[0]],[[-325991204,-49672],[-49672]],[[0,0],[0]],[[-105872032,-2912],[-2912]],[[0,0],[0]],[[-25742220,-56],[-56]],[[0]],[[-4560360]],[[0]],[[-562100]],[[0]],[[-44408]],[[0]],[[-1904]],[[0]],[[-28]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
