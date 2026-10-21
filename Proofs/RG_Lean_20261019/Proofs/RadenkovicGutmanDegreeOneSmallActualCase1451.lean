/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1451 : Family 9 := level9.get ⟨187,by decide⟩
def sourceMap1451 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,5,0,1,2,3,4,6,7,8,10,11] (sourceLabel 9 0 0 v)
def fusedMap1451 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap1451_checked : acceptsGraphIso
    (source (graph core1451) (root 9) 0 0) DegreeOneSmallSpectrum492.graph sourceMap1451=true := by decide +kernel
theorem fusedMap1451_checked : acceptsGraphIso
    (fused (graph core1451) (root 9) 0 0) DegreeOneSmallSpectrum491.graph fusedMap1451=true := by decide +kernel
theorem certified1451 : Certified (graph core1451) (root 9) 0 0 :=
  of_native_maps core1451 DegreeOneSmallSpectrum492.graph DegreeOneSmallSpectrum491.graph
    sourceMap1451 fusedMap1451 sourceMap1451_checked fusedMap1451_checked
    DegreeOneSmallComparisons.comparison1451
#print axioms sourceMap1451_checked
#print axioms fusedMap1451_checked
#print axioms certified1451
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
