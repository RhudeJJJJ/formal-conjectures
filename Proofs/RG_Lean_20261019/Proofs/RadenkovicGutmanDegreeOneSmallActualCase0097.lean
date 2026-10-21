/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0097 : Family 4 := level4.get ⟨0,by decide⟩
def sourceMap0097 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,5,6,7,8,4,1,2,3] (sourceLabel 4 0 2 v)
def fusedMap0097 : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 4 0 2 v)
theorem sourceMap0097_checked : acceptsGraphIso
    (source (graph core0097) (root 4) 0 2) DegreeOneSmallSpectrum036.graph sourceMap0097=true := by decide +kernel
theorem fusedMap0097_checked : acceptsGraphIso
    (fused (graph core0097) (root 4) 0 2) DegreeOneSmallSpectrum037.graph fusedMap0097=true := by decide +kernel
theorem certified0097 : Certified (graph core0097) (root 4) 0 2 :=
  of_native_maps core0097 DegreeOneSmallSpectrum036.graph DegreeOneSmallSpectrum037.graph
    sourceMap0097 fusedMap0097 sourceMap0097_checked fusedMap0097_checked
    DegreeOneSmallComparisons.comparison0097
#print axioms sourceMap0097_checked
#print axioms fusedMap0097_checked
#print axioms certified0097
def sourceMap0097swap : (Vertices 4 ⊕ Fin 3 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,5,6,7,8,1,2,3,4] (sourceLabel 4 2 0 v)
def fusedMap0097swap : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 4 2 0 v)
theorem sourceMap0097swap_checked : acceptsGraphIso
    (source (graph core0097) (root 4) 2 0) DegreeOneSmallSpectrum036.graph sourceMap0097swap=true := by decide +kernel
theorem fusedMap0097swap_checked : acceptsGraphIso
    (fused (graph core0097) (root 4) 2 0) DegreeOneSmallSpectrum037.graph fusedMap0097swap=true := by decide +kernel
theorem certified0097swap : Certified (graph core0097) (root 4) 2 0 :=
  of_native_maps core0097 DegreeOneSmallSpectrum036.graph DegreeOneSmallSpectrum037.graph
    sourceMap0097swap fusedMap0097swap sourceMap0097swap_checked fusedMap0097swap_checked
    DegreeOneSmallComparisons.comparison0097
#print axioms sourceMap0097swap_checked
#print axioms fusedMap0097swap_checked
#print axioms certified0097swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
