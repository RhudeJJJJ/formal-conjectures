/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons24
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1249 : Family 9 := level9.get ⟨31,by decide⟩
def sourceMap1249 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,6,4,5] (sourceLabel 9 0 0 v)
def fusedMap1249 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1249_checked : acceptsGraphIso
    (source (graph core1249) (root 9) 0 0) DegreeOneSmallSpectrum479.graph sourceMap1249=true := by decide +kernel
theorem fusedMap1249_checked : acceptsGraphIso
    (fused (graph core1249) (root 9) 0 0) DegreeOneSmallSpectrum395.graph fusedMap1249=true := by decide +kernel
theorem certified1249 : Certified (graph core1249) (root 9) 0 0 :=
  of_native_maps core1249 DegreeOneSmallSpectrum479.graph DegreeOneSmallSpectrum395.graph
    sourceMap1249 fusedMap1249 sourceMap1249_checked fusedMap1249_checked
    DegreeOneSmallComparisons.comparison1249
#print axioms sourceMap1249_checked
#print axioms fusedMap1249_checked
#print axioms certified1249
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
