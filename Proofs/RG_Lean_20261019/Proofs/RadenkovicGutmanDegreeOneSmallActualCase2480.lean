/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2480 : Family 10 := level10.get ⟨1646,by decide⟩
def sourceMap2480 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (sourceLabel 10 0 0 v)
def fusedMap2480 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2480_checked : acceptsGraphIso
    (source (graph core2480) (root 10) 0 0) DegreeOneSmallSpectrum2015.graph sourceMap2480=true := by decide +kernel
theorem fusedMap2480_checked : acceptsGraphIso
    (fused (graph core2480) (root 10) 0 0) DegreeOneSmallSpectrum1774.graph fusedMap2480=true := by decide +kernel
theorem certified2480 : Certified (graph core2480) (root 10) 0 0 :=
  of_native_maps core2480 DegreeOneSmallSpectrum2015.graph DegreeOneSmallSpectrum1774.graph
    sourceMap2480 fusedMap2480 sourceMap2480_checked fusedMap2480_checked
    DegreeOneSmallComparisons.comparison2480
#print axioms sourceMap2480_checked
#print axioms fusedMap2480_checked
#print axioms certified2480
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
