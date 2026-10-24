/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode070
import Proofs.RadenkovicGutmanD5Long00CompositionalNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e070 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,120],[0,120,56]],[[0,0,0],[0,0,0],[0,0,0]],[[0,1080,1980],[1080,5688,1648],[1980,1648,4]],[[0,0,0],[0,0,0],[0,0]],[[11016,70092,20976],[70092,64452,3920],[20976,3920]],[[0,0,0],[0,0,0],[0,0]],[[559656,771912,79456],[771912,251168,3576],[79456,3576]],[[0,0,0],[0,0,0],[0,0]],[[6803460,3805420,153120],[3805420,495716,1392],[153120,1392]],[[0,0,0],[0,0,0],[0,0]],[[40767204,10793412,171208],[10793412,569224,216],[171208,216]],[[0,0,0],[0,0,0],[0,0]],[[149450380,19712116,117616],[19712116,403136,8],[117616,8]],[[0,0,0],[0,0],[0]],[[371443544,24614048,50564],[24614048,179168],[50564]],[[0,0,0],[0,0],[0]],[[663393592,21731696,13408],[21731696,49188],[13408]],[[0,0,0],[0,0],[0]],[[882450976,13804516,2068],[13804516,7856],[2068]],[[0,0,0],[0,0],[0]],[[894353844,6342548,160],[6342548,628],[160]],[[0,0,0],[0,0],[0]],[[700343848,2095020,4],[2095020,16],[4]],[[0,0],[0]],[[426946880,487900],[487900]],[[0,0],[0]],[[203053272,77040],[77040]],[[0,0],[0]],[[75101044,7660],[7660]],[[0,0],[0]],[[21407240,412],[412]],[[0,0],[0]],[[4625864,8],[8]],[[0]],[[737440]],[[0]],[[82948]],[[0]],[[6096]],[[0]],[[252]],[[0]],[[4]]]
theorem step083 : p083=NestedHorner.add p070 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e070 e082 p070 p082 p083 rfl h070 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
