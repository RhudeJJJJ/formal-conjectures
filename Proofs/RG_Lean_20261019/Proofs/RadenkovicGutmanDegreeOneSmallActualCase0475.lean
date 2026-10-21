/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0475 : Family 7 := level7.get ⟨4,by decide⟩
def sourceMap0475 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,3,4,5,6] (sourceLabel 7 1 1 v)
def fusedMap0475 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0475_checked : acceptsGraphIso
    (source (graph core0475) (root 7) 1 1) DegreeOneSmallSpectrum518.graph sourceMap0475=true := by decide +kernel
theorem fusedMap0475_checked : acceptsGraphIso
    (fused (graph core0475) (root 7) 1 1) DegreeOneSmallSpectrum396.graph fusedMap0475=true := by decide +kernel
theorem certified0475 : Certified (graph core0475) (root 7) 1 1 :=
  of_native_maps core0475 DegreeOneSmallSpectrum518.graph DegreeOneSmallSpectrum396.graph
    sourceMap0475 fusedMap0475 sourceMap0475_checked fusedMap0475_checked
    DegreeOneSmallComparisons.comparison0475
#print axioms sourceMap0475_checked
#print axioms fusedMap0475_checked
#print axioms certified0475
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
