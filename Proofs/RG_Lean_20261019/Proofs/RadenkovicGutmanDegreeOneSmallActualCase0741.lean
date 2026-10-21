/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0741 : Family 8 := level8.get ⟨1,by decide⟩
def sourceMap0741 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0741 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0741_checked : acceptsGraphIso
    (source (graph core0741) (root 8) 0 2) DegreeOneSmallSpectrum904.graph sourceMap0741=true := by decide +kernel
theorem fusedMap0741_checked : acceptsGraphIso
    (fused (graph core0741) (root 8) 0 2) DegreeOneSmallSpectrum856.graph fusedMap0741=true := by decide +kernel
theorem certified0741 : Certified (graph core0741) (root 8) 0 2 :=
  of_native_maps core0741 DegreeOneSmallSpectrum904.graph DegreeOneSmallSpectrum856.graph
    sourceMap0741 fusedMap0741 sourceMap0741_checked fusedMap0741_checked
    DegreeOneSmallComparisons.comparison0741
#print axioms sourceMap0741_checked
#print axioms fusedMap0741_checked
#print axioms certified0741
def sourceMap0741swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0741swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0741swap_checked : acceptsGraphIso
    (source (graph core0741) (root 8) 2 0) DegreeOneSmallSpectrum904.graph sourceMap0741swap=true := by decide +kernel
theorem fusedMap0741swap_checked : acceptsGraphIso
    (fused (graph core0741) (root 8) 2 0) DegreeOneSmallSpectrum856.graph fusedMap0741swap=true := by decide +kernel
theorem certified0741swap : Certified (graph core0741) (root 8) 2 0 :=
  of_native_maps core0741 DegreeOneSmallSpectrum904.graph DegreeOneSmallSpectrum856.graph
    sourceMap0741swap fusedMap0741swap sourceMap0741swap_checked fusedMap0741swap_checked
    DegreeOneSmallComparisons.comparison0741
#print axioms sourceMap0741swap_checked
#print axioms fusedMap0741swap_checked
#print axioms certified0741swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
