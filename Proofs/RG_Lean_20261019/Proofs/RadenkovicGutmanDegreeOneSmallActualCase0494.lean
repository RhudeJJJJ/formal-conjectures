/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0494 : Family 7 := level7.get ⟨8,by decide⟩
def sourceMap0494 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 3) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,8,9,10] (sourceLabel 7 1 2 v)
def fusedMap0494 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 1 2 v)
theorem sourceMap0494_checked : acceptsGraphIso
    (source (graph core0494) (root 7) 1 2) DegreeOneSmallSpectrum1177.graph sourceMap0494=true := by decide +kernel
theorem fusedMap0494_checked : acceptsGraphIso
    (fused (graph core0494) (root 7) 1 2) DegreeOneSmallSpectrum879.graph fusedMap0494=true := by decide +kernel
theorem certified0494 : Certified (graph core0494) (root 7) 1 2 :=
  of_native_maps core0494 DegreeOneSmallSpectrum1177.graph DegreeOneSmallSpectrum879.graph
    sourceMap0494 fusedMap0494 sourceMap0494_checked fusedMap0494_checked
    DegreeOneSmallComparisons.comparison0494
#print axioms sourceMap0494_checked
#print axioms fusedMap0494_checked
#print axioms certified0494
def sourceMap0494swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 2 1 v)
def fusedMap0494swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 2 1 v)
theorem sourceMap0494swap_checked : acceptsGraphIso
    (source (graph core0494) (root 7) 2 1) DegreeOneSmallSpectrum1177.graph sourceMap0494swap=true := by decide +kernel
theorem fusedMap0494swap_checked : acceptsGraphIso
    (fused (graph core0494) (root 7) 2 1) DegreeOneSmallSpectrum879.graph fusedMap0494swap=true := by decide +kernel
theorem certified0494swap : Certified (graph core0494) (root 7) 2 1 :=
  of_native_maps core0494 DegreeOneSmallSpectrum1177.graph DegreeOneSmallSpectrum879.graph
    sourceMap0494swap fusedMap0494swap sourceMap0494swap_checked fusedMap0494swap_checked
    DegreeOneSmallComparisons.comparison0494
#print axioms sourceMap0494swap_checked
#print axioms fusedMap0494swap_checked
#print axioms certified0494swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
