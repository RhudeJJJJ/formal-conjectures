/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0853 : Family 8 := level8.get ⟨37,by decide⟩
def sourceMap0853 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,11,8,9,10] (sourceLabel 8 0 2 v)
def fusedMap0853 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0853_checked : acceptsGraphIso
    (source (graph core0853) (root 8) 0 2) DegreeOneSmallSpectrum1080.graph sourceMap0853=true := by decide +kernel
theorem fusedMap0853_checked : acceptsGraphIso
    (fused (graph core0853) (root 8) 0 2) DegreeOneSmallSpectrum865.graph fusedMap0853=true := by decide +kernel
theorem certified0853 : Certified (graph core0853) (root 8) 0 2 :=
  of_native_maps core0853 DegreeOneSmallSpectrum1080.graph DegreeOneSmallSpectrum865.graph
    sourceMap0853 fusedMap0853 sourceMap0853_checked fusedMap0853_checked
    DegreeOneSmallComparisons.comparison0853
#print axioms sourceMap0853_checked
#print axioms fusedMap0853_checked
#print axioms certified0853
def sourceMap0853swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 8 2 0 v)
def fusedMap0853swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0853swap_checked : acceptsGraphIso
    (source (graph core0853) (root 8) 2 0) DegreeOneSmallSpectrum1080.graph sourceMap0853swap=true := by decide +kernel
theorem fusedMap0853swap_checked : acceptsGraphIso
    (fused (graph core0853) (root 8) 2 0) DegreeOneSmallSpectrum865.graph fusedMap0853swap=true := by decide +kernel
theorem certified0853swap : Certified (graph core0853) (root 8) 2 0 :=
  of_native_maps core0853 DegreeOneSmallSpectrum1080.graph DegreeOneSmallSpectrum865.graph
    sourceMap0853swap fusedMap0853swap sourceMap0853swap_checked fusedMap0853swap_checked
    DegreeOneSmallComparisons.comparison0853
#print axioms sourceMap0853swap_checked
#print axioms fusedMap0853swap_checked
#print axioms certified0853swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
