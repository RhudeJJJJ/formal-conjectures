/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0777 : Family 8 := level8.get ⟨11,by decide⟩
def sourceMap0777 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0777 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0777_checked : acceptsGraphIso
    (source (graph core0777) (root 8) 0 2) DegreeOneSmallSpectrum892.graph sourceMap0777=true := by decide +kernel
theorem fusedMap0777_checked : acceptsGraphIso
    (fused (graph core0777) (root 8) 0 2) DegreeOneSmallSpectrum894.graph fusedMap0777=true := by decide +kernel
theorem certified0777 : Certified (graph core0777) (root 8) 0 2 :=
  of_native_maps core0777 DegreeOneSmallSpectrum892.graph DegreeOneSmallSpectrum894.graph
    sourceMap0777 fusedMap0777 sourceMap0777_checked fusedMap0777_checked
    DegreeOneSmallComparisons.comparison0777
#print axioms sourceMap0777_checked
#print axioms fusedMap0777_checked
#print axioms certified0777
def sourceMap0777swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0777swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0777swap_checked : acceptsGraphIso
    (source (graph core0777) (root 8) 2 0) DegreeOneSmallSpectrum892.graph sourceMap0777swap=true := by decide +kernel
theorem fusedMap0777swap_checked : acceptsGraphIso
    (fused (graph core0777) (root 8) 2 0) DegreeOneSmallSpectrum894.graph fusedMap0777swap=true := by decide +kernel
theorem certified0777swap : Certified (graph core0777) (root 8) 2 0 :=
  of_native_maps core0777 DegreeOneSmallSpectrum892.graph DegreeOneSmallSpectrum894.graph
    sourceMap0777swap fusedMap0777swap sourceMap0777swap_checked fusedMap0777swap_checked
    DegreeOneSmallComparisons.comparison0777
#print axioms sourceMap0777swap_checked
#print axioms fusedMap0777swap_checked
#print axioms certified0777swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
