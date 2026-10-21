/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0848 : Family 8 := level8.get ⟨36,by decide⟩
def sourceMap0848 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0848 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0848_checked : acceptsGraphIso
    (source (graph core0848) (root 8) 0 1) DegreeOneSmallSpectrum415.graph sourceMap0848=true := by decide +kernel
theorem fusedMap0848_checked : acceptsGraphIso
    (fused (graph core0848) (root 8) 0 1) DegreeOneSmallSpectrum417.graph fusedMap0848=true := by decide +kernel
theorem certified0848 : Certified (graph core0848) (root 8) 0 1 :=
  of_native_maps core0848 DegreeOneSmallSpectrum415.graph DegreeOneSmallSpectrum417.graph
    sourceMap0848 fusedMap0848 sourceMap0848_checked fusedMap0848_checked
    DegreeOneSmallComparisons.comparison0848
#print axioms sourceMap0848_checked
#print axioms fusedMap0848_checked
#print axioms certified0848
def sourceMap0848swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0848swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0848swap_checked : acceptsGraphIso
    (source (graph core0848) (root 8) 1 0) DegreeOneSmallSpectrum415.graph sourceMap0848swap=true := by decide +kernel
theorem fusedMap0848swap_checked : acceptsGraphIso
    (fused (graph core0848) (root 8) 1 0) DegreeOneSmallSpectrum417.graph fusedMap0848swap=true := by decide +kernel
theorem certified0848swap : Certified (graph core0848) (root 8) 1 0 :=
  of_native_maps core0848 DegreeOneSmallSpectrum415.graph DegreeOneSmallSpectrum417.graph
    sourceMap0848swap fusedMap0848swap sourceMap0848swap_checked fusedMap0848swap_checked
    DegreeOneSmallComparisons.comparison0848
#print axioms sourceMap0848swap_checked
#print axioms fusedMap0848swap_checked
#print axioms certified0848swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
