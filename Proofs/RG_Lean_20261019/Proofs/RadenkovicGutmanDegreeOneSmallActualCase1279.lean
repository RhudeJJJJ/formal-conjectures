/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1279 : Family 9 := level9.get ⟨52,by decide⟩
def sourceMap1279 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1279 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1279_checked : acceptsGraphIso
    (source (graph core1279) (root 9) 0 0) DegreeOneSmallSpectrum448.graph sourceMap1279=true := by decide +kernel
theorem fusedMap1279_checked : acceptsGraphIso
    (fused (graph core1279) (root 9) 0 0) DegreeOneSmallSpectrum457.graph fusedMap1279=true := by decide +kernel
theorem certified1279 : Certified (graph core1279) (root 9) 0 0 :=
  of_native_maps core1279 DegreeOneSmallSpectrum448.graph DegreeOneSmallSpectrum457.graph
    sourceMap1279 fusedMap1279 sourceMap1279_checked fusedMap1279_checked
    DegreeOneSmallComparisons.comparison1279
#print axioms sourceMap1279_checked
#print axioms fusedMap1279_checked
#print axioms certified1279
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
