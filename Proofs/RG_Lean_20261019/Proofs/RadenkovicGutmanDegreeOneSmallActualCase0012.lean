/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0012 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0012 : (Vertices 1 ⊕ Fin 2 ⊕ Fin 4) → Fin 8 :=
  fun v => ![1,4,2,3,0,5,6,7] (sourceLabel 1 1 3 v)
def fusedMap0012 : (Vertices 1 ⊕ Fin 6) → Fin 8 :=
  fun v => ![2,3,1,0,4,5,6,7] (fusedLabel 1 1 3 v)
theorem sourceMap0012_checked : acceptsGraphIso
    (source (graph core0012) (root 1) 1 3) DegreeOneSmallSpectrum025.graph sourceMap0012=true := by decide +kernel
theorem fusedMap0012_checked : acceptsGraphIso
    (fused (graph core0012) (root 1) 1 3) DegreeOneSmallSpectrum016.graph fusedMap0012=true := by decide +kernel
theorem certified0012 : Certified (graph core0012) (root 1) 1 3 :=
  of_native_maps core0012 DegreeOneSmallSpectrum025.graph DegreeOneSmallSpectrum016.graph
    sourceMap0012 fusedMap0012 sourceMap0012_checked fusedMap0012_checked
    DegreeOneSmallComparisons.comparison0012
#print axioms sourceMap0012_checked
#print axioms fusedMap0012_checked
#print axioms certified0012
def sourceMap0012swap : (Vertices 1 ⊕ Fin 4 ⊕ Fin 2) → Fin 8 :=
  fun v => ![1,4,0,5,6,7,2,3] (sourceLabel 1 3 1 v)
def fusedMap0012swap : (Vertices 1 ⊕ Fin 6) → Fin 8 :=
  fun v => ![2,3,1,0,4,5,6,7] (fusedLabel 1 3 1 v)
theorem sourceMap0012swap_checked : acceptsGraphIso
    (source (graph core0012) (root 1) 3 1) DegreeOneSmallSpectrum025.graph sourceMap0012swap=true := by decide +kernel
theorem fusedMap0012swap_checked : acceptsGraphIso
    (fused (graph core0012) (root 1) 3 1) DegreeOneSmallSpectrum016.graph fusedMap0012swap=true := by decide +kernel
theorem certified0012swap : Certified (graph core0012) (root 1) 3 1 :=
  of_native_maps core0012 DegreeOneSmallSpectrum025.graph DegreeOneSmallSpectrum016.graph
    sourceMap0012swap fusedMap0012swap sourceMap0012swap_checked fusedMap0012swap_checked
    DegreeOneSmallComparisons.comparison0012
#print axioms sourceMap0012swap_checked
#print axioms fusedMap0012swap_checked
#print axioms certified0012swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
