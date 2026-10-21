/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1691 : Family 9 := level9.get ⟨458,by decide⟩
def sourceMap1691 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (sourceLabel 9 0 0 v)
def fusedMap1691 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1691_checked : acceptsGraphIso
    (source (graph core1691) (root 9) 0 0) DegreeOneSmallSpectrum813.graph sourceMap1691=true := by decide +kernel
theorem fusedMap1691_checked : acceptsGraphIso
    (fused (graph core1691) (root 9) 0 0) DegreeOneSmallSpectrum812.graph fusedMap1691=true := by decide +kernel
theorem certified1691 : Certified (graph core1691) (root 9) 0 0 :=
  of_native_maps core1691 DegreeOneSmallSpectrum813.graph DegreeOneSmallSpectrum812.graph
    sourceMap1691 fusedMap1691 sourceMap1691_checked fusedMap1691_checked
    DegreeOneSmallComparisons.comparison1691
#print axioms sourceMap1691_checked
#print axioms fusedMap1691_checked
#print axioms certified1691
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
