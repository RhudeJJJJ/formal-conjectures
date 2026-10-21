/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1802 : Family 10 := level10.get ⟨40,by decide⟩
def sourceMap1802 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1802 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap1802_checked : acceptsGraphIso
    (source (graph core1802) (root 10) 0 0) DegreeOneSmallSpectrum889.graph sourceMap1802=true := by decide +kernel
theorem fusedMap1802_checked : acceptsGraphIso
    (fused (graph core1802) (root 10) 0 0) DegreeOneSmallSpectrum978.graph fusedMap1802=true := by decide +kernel
theorem certified1802 : Certified (graph core1802) (root 10) 0 0 :=
  of_native_maps core1802 DegreeOneSmallSpectrum889.graph DegreeOneSmallSpectrum978.graph
    sourceMap1802 fusedMap1802 sourceMap1802_checked fusedMap1802_checked
    DegreeOneSmallComparisons.comparison1802
#print axioms sourceMap1802_checked
#print axioms fusedMap1802_checked
#print axioms certified1802
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
