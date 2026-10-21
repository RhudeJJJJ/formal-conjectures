/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0818 : Family 8 := level8.get ⟨23,by decide⟩
def sourceMap0818 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0818 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 1 1 v)
theorem sourceMap0818_checked : acceptsGraphIso
    (source (graph core0818) (root 8) 1 1) DegreeOneSmallSpectrum1330.graph sourceMap0818=true := by decide +kernel
theorem fusedMap0818_checked : acceptsGraphIso
    (fused (graph core0818) (root 8) 1 1) DegreeOneSmallSpectrum966.graph fusedMap0818=true := by decide +kernel
theorem certified0818 : Certified (graph core0818) (root 8) 1 1 :=
  of_native_maps core0818 DegreeOneSmallSpectrum1330.graph DegreeOneSmallSpectrum966.graph
    sourceMap0818 fusedMap0818 sourceMap0818_checked fusedMap0818_checked
    DegreeOneSmallComparisons.comparison0818
#print axioms sourceMap0818_checked
#print axioms fusedMap0818_checked
#print axioms certified0818
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
