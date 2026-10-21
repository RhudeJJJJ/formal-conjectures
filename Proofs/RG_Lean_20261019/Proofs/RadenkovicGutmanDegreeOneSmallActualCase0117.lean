/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0117 : Family 4 := level4.get ⟨1,by decide⟩
def sourceMap0117 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (sourceLabel 4 0 6 v)
def fusedMap0117 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 0 6 v)
theorem sourceMap0117_checked : acceptsGraphIso
    (source (graph core0117) (root 4) 0 6) DegreeOneSmallSpectrum887.graph sourceMap0117=true := by decide +kernel
theorem fusedMap0117_checked : acceptsGraphIso
    (fused (graph core0117) (root 4) 0 6) DegreeOneSmallSpectrum856.graph fusedMap0117=true := by decide +kernel
theorem certified0117 : Certified (graph core0117) (root 4) 0 6 :=
  of_native_maps core0117 DegreeOneSmallSpectrum887.graph DegreeOneSmallSpectrum856.graph
    sourceMap0117 fusedMap0117 sourceMap0117_checked fusedMap0117_checked
    DegreeOneSmallComparisons.comparison0117
#print axioms sourceMap0117_checked
#print axioms fusedMap0117_checked
#print axioms certified0117
def sourceMap0117swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,8,9,10,11,12,7] (sourceLabel 4 6 0 v)
def fusedMap0117swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 6 0 v)
theorem sourceMap0117swap_checked : acceptsGraphIso
    (source (graph core0117) (root 4) 6 0) DegreeOneSmallSpectrum887.graph sourceMap0117swap=true := by decide +kernel
theorem fusedMap0117swap_checked : acceptsGraphIso
    (fused (graph core0117) (root 4) 6 0) DegreeOneSmallSpectrum856.graph fusedMap0117swap=true := by decide +kernel
theorem certified0117swap : Certified (graph core0117) (root 4) 6 0 :=
  of_native_maps core0117 DegreeOneSmallSpectrum887.graph DegreeOneSmallSpectrum856.graph
    sourceMap0117swap fusedMap0117swap sourceMap0117swap_checked fusedMap0117swap_checked
    DegreeOneSmallComparisons.comparison0117
#print axioms sourceMap0117swap_checked
#print axioms fusedMap0117swap_checked
#print axioms certified0117swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
