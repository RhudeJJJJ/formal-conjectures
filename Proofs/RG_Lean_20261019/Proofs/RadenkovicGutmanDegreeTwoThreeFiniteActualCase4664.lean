/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4664 : Family 10 := level10.get ⟨785,by decide⟩
def sourceMap4664 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4664 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4664_checked : acceptsGraphIso
    (source (graph core4664) (root 10) 2 2) DegreeTwoThreeSpectrum7455.graph sourceMap4664=true := by decide +kernel
theorem fusedMap4664_checked : acceptsGraphIso
    (fused (graph core4664) (root 10) 2 2) DegreeTwoThreeSpectrum5566.graph fusedMap4664=true := by decide +kernel
theorem certified4664 : Certified (graph core4664) (root 10) 2 2 :=
  of_native_maps core4664 DegreeTwoThreeSpectrum7455.graph DegreeTwoThreeSpectrum5566.graph
    sourceMap4664 fusedMap4664 sourceMap4664_checked fusedMap4664_checked
    DegreeTwoThreeFiniteComparisons.comparison4664
#print axioms sourceMap4664_checked
#print axioms fusedMap4664_checked
#print axioms certified4664
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
