/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0881 : Family 8 := level8.get ⟨46,by decide⟩
def sourceMap0881 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,11,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap0881 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0881_checked : acceptsGraphIso
    (source (graph core0881) (root 8) 0 2) DegreeOneSmallSpectrum1245.graph sourceMap0881=true := by decide +kernel
theorem fusedMap0881_checked : acceptsGraphIso
    (fused (graph core0881) (root 8) 0 2) DegreeOneSmallSpectrum882.graph fusedMap0881=true := by decide +kernel
theorem certified0881 : Certified (graph core0881) (root 8) 0 2 :=
  of_native_maps core0881 DegreeOneSmallSpectrum1245.graph DegreeOneSmallSpectrum882.graph
    sourceMap0881 fusedMap0881 sourceMap0881_checked fusedMap0881_checked
    DegreeOneSmallComparisons.comparison0881
#print axioms sourceMap0881_checked
#print axioms fusedMap0881_checked
#print axioms certified0881
def sourceMap0881swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 8 2 0 v)
def fusedMap0881swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0881swap_checked : acceptsGraphIso
    (source (graph core0881) (root 8) 2 0) DegreeOneSmallSpectrum1245.graph sourceMap0881swap=true := by decide +kernel
theorem fusedMap0881swap_checked : acceptsGraphIso
    (fused (graph core0881) (root 8) 2 0) DegreeOneSmallSpectrum882.graph fusedMap0881swap=true := by decide +kernel
theorem certified0881swap : Certified (graph core0881) (root 8) 2 0 :=
  of_native_maps core0881 DegreeOneSmallSpectrum1245.graph DegreeOneSmallSpectrum882.graph
    sourceMap0881swap fusedMap0881swap sourceMap0881swap_checked fusedMap0881swap_checked
    DegreeOneSmallComparisons.comparison0881
#print axioms sourceMap0881swap_checked
#print axioms fusedMap0881swap_checked
#print axioms certified0881swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
