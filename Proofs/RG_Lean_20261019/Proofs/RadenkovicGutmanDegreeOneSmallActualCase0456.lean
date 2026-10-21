/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0456 : Family 7 := level7.get ⟨1,by decide⟩
def sourceMap0456 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0456 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0456_checked : acceptsGraphIso
    (source (graph core0456) (root 7) 0 3) DegreeOneSmallSpectrum907.graph sourceMap0456=true := by decide +kernel
theorem fusedMap0456_checked : acceptsGraphIso
    (fused (graph core0456) (root 7) 0 3) DegreeOneSmallSpectrum856.graph fusedMap0456=true := by decide +kernel
theorem certified0456 : Certified (graph core0456) (root 7) 0 3 :=
  of_native_maps core0456 DegreeOneSmallSpectrum907.graph DegreeOneSmallSpectrum856.graph
    sourceMap0456 fusedMap0456 sourceMap0456_checked fusedMap0456_checked
    DegreeOneSmallComparisons.comparison0456
#print axioms sourceMap0456_checked
#print axioms fusedMap0456_checked
#print axioms certified0456
def sourceMap0456swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0456swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0456swap_checked : acceptsGraphIso
    (source (graph core0456) (root 7) 3 0) DegreeOneSmallSpectrum907.graph sourceMap0456swap=true := by decide +kernel
theorem fusedMap0456swap_checked : acceptsGraphIso
    (fused (graph core0456) (root 7) 3 0) DegreeOneSmallSpectrum856.graph fusedMap0456swap=true := by decide +kernel
theorem certified0456swap : Certified (graph core0456) (root 7) 3 0 :=
  of_native_maps core0456 DegreeOneSmallSpectrum907.graph DegreeOneSmallSpectrum856.graph
    sourceMap0456swap fusedMap0456swap sourceMap0456swap_checked fusedMap0456swap_checked
    DegreeOneSmallComparisons.comparison0456
#print axioms sourceMap0456swap_checked
#print axioms fusedMap0456swap_checked
#print axioms certified0456swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
