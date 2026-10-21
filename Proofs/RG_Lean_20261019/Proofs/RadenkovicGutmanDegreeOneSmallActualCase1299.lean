/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1299 : Family 9 := level9.get ⟨65,by decide⟩
def sourceMap1299 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1299 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1299_checked : acceptsGraphIso
    (source (graph core1299) (root 9) 0 0) DegreeOneSmallSpectrum437.graph sourceMap1299=true := by decide +kernel
theorem fusedMap1299_checked : acceptsGraphIso
    (fused (graph core1299) (root 9) 0 0) DegreeOneSmallSpectrum496.graph fusedMap1299=true := by decide +kernel
theorem certified1299 : Certified (graph core1299) (root 9) 0 0 :=
  of_native_maps core1299 DegreeOneSmallSpectrum437.graph DegreeOneSmallSpectrum496.graph
    sourceMap1299 fusedMap1299 sourceMap1299_checked fusedMap1299_checked
    DegreeOneSmallComparisons.comparison1299
#print axioms sourceMap1299_checked
#print axioms fusedMap1299_checked
#print axioms certified1299
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
