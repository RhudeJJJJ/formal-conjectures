/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2458 : Family 10 := level10.get ⟨1526,by decide⟩
def sourceMap2458 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2458 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2458_checked : acceptsGraphIso
    (source (graph core2458) (root 10) 0 0) DegreeOneSmallSpectrum1993.graph sourceMap2458=true := by decide +kernel
theorem fusedMap2458_checked : acceptsGraphIso
    (fused (graph core2458) (root 10) 0 0) DegreeOneSmallSpectrum1522.graph fusedMap2458=true := by decide +kernel
theorem certified2458 : Certified (graph core2458) (root 10) 0 0 :=
  of_native_maps core2458 DegreeOneSmallSpectrum1993.graph DegreeOneSmallSpectrum1522.graph
    sourceMap2458 fusedMap2458 sourceMap2458_checked fusedMap2458_checked
    DegreeOneSmallComparisons.comparison2458
#print axioms sourceMap2458_checked
#print axioms fusedMap2458_checked
#print axioms certified2458
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
