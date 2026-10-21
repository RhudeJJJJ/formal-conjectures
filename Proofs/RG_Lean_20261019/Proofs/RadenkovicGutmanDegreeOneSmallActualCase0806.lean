/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0806 : Family 8 := level8.get ⟨20,by decide⟩
def sourceMap0806 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0806 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0806_checked : acceptsGraphIso
    (source (graph core0806) (root 8) 1 1) DegreeOneSmallSpectrum1343.graph sourceMap0806=true := by decide +kernel
theorem fusedMap0806_checked : acceptsGraphIso
    (fused (graph core0806) (root 8) 1 1) DegreeOneSmallSpectrum951.graph fusedMap0806=true := by decide +kernel
theorem certified0806 : Certified (graph core0806) (root 8) 1 1 :=
  of_native_maps core0806 DegreeOneSmallSpectrum1343.graph DegreeOneSmallSpectrum951.graph
    sourceMap0806 fusedMap0806 sourceMap0806_checked fusedMap0806_checked
    DegreeOneSmallComparisons.comparison0806
#print axioms sourceMap0806_checked
#print axioms fusedMap0806_checked
#print axioms certified0806
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
