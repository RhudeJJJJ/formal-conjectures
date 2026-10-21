/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons27
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1371 : Family 9 := level9.get ⟨118,by decide⟩
def sourceMap1371 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1371 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1371_checked : acceptsGraphIso
    (source (graph core1371) (root 9) 0 0) DegreeOneSmallSpectrum442.graph sourceMap1371=true := by decide +kernel
theorem fusedMap1371_checked : acceptsGraphIso
    (fused (graph core1371) (root 9) 0 0) DegreeOneSmallSpectrum584.graph fusedMap1371=true := by decide +kernel
theorem certified1371 : Certified (graph core1371) (root 9) 0 0 :=
  of_native_maps core1371 DegreeOneSmallSpectrum442.graph DegreeOneSmallSpectrum584.graph
    sourceMap1371 fusedMap1371 sourceMap1371_checked fusedMap1371_checked
    DegreeOneSmallComparisons.comparison1371
#print axioms sourceMap1371_checked
#print axioms fusedMap1371_checked
#print axioms certified1371
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
