/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1437 : Family 9 := level9.get ⟨175,by decide⟩
def sourceMap1437 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1437 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1437_checked : acceptsGraphIso
    (source (graph core1437) (root 9) 0 0) DegreeOneSmallSpectrum746.graph sourceMap1437=true := by decide +kernel
theorem fusedMap1437_checked : acceptsGraphIso
    (fused (graph core1437) (root 9) 0 0) DegreeOneSmallSpectrum459.graph fusedMap1437=true := by decide +kernel
theorem certified1437 : Certified (graph core1437) (root 9) 0 0 :=
  of_native_maps core1437 DegreeOneSmallSpectrum746.graph DegreeOneSmallSpectrum459.graph
    sourceMap1437 fusedMap1437 sourceMap1437_checked fusedMap1437_checked
    DegreeOneSmallComparisons.comparison1437
#print axioms sourceMap1437_checked
#print axioms fusedMap1437_checked
#print axioms certified1437
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
