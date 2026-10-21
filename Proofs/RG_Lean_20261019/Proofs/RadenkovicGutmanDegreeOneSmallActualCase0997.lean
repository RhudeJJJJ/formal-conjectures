/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0997 : Family 8 := level8.get ⟨99,by decide⟩
def sourceMap0997 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0997 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0997_checked : acceptsGraphIso
    (source (graph core0997) (root 8) 0 2) DegreeOneSmallSpectrum1014.graph sourceMap0997=true := by decide +kernel
theorem fusedMap0997_checked : acceptsGraphIso
    (fused (graph core0997) (root 8) 0 2) DegreeOneSmallSpectrum1015.graph fusedMap0997=true := by decide +kernel
theorem certified0997 : Certified (graph core0997) (root 8) 0 2 :=
  of_native_maps core0997 DegreeOneSmallSpectrum1014.graph DegreeOneSmallSpectrum1015.graph
    sourceMap0997 fusedMap0997 sourceMap0997_checked fusedMap0997_checked
    DegreeOneSmallComparisons.comparison0997
#print axioms sourceMap0997_checked
#print axioms fusedMap0997_checked
#print axioms certified0997
def sourceMap0997swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0997swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0997swap_checked : acceptsGraphIso
    (source (graph core0997) (root 8) 2 0) DegreeOneSmallSpectrum1014.graph sourceMap0997swap=true := by decide +kernel
theorem fusedMap0997swap_checked : acceptsGraphIso
    (fused (graph core0997) (root 8) 2 0) DegreeOneSmallSpectrum1015.graph fusedMap0997swap=true := by decide +kernel
theorem certified0997swap : Certified (graph core0997) (root 8) 2 0 :=
  of_native_maps core0997 DegreeOneSmallSpectrum1014.graph DegreeOneSmallSpectrum1015.graph
    sourceMap0997swap fusedMap0997swap sourceMap0997swap_checked fusedMap0997swap_checked
    DegreeOneSmallComparisons.comparison0997
#print axioms sourceMap0997swap_checked
#print axioms fusedMap0997swap_checked
#print axioms certified0997swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
