/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0793 : Family 8 := level8.get ⟨16,by decide⟩
def sourceMap0793 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0793 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0793_checked : acceptsGraphIso
    (source (graph core0793) (root 8) 0 2) DegreeOneSmallSpectrum927.graph sourceMap0793=true := by decide +kernel
theorem fusedMap0793_checked : acceptsGraphIso
    (fused (graph core0793) (root 8) 0 2) DegreeOneSmallSpectrum929.graph fusedMap0793=true := by decide +kernel
theorem certified0793 : Certified (graph core0793) (root 8) 0 2 :=
  of_native_maps core0793 DegreeOneSmallSpectrum927.graph DegreeOneSmallSpectrum929.graph
    sourceMap0793 fusedMap0793 sourceMap0793_checked fusedMap0793_checked
    DegreeOneSmallComparisons.comparison0793
#print axioms sourceMap0793_checked
#print axioms fusedMap0793_checked
#print axioms certified0793
def sourceMap0793swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0793swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0793swap_checked : acceptsGraphIso
    (source (graph core0793) (root 8) 2 0) DegreeOneSmallSpectrum927.graph sourceMap0793swap=true := by decide +kernel
theorem fusedMap0793swap_checked : acceptsGraphIso
    (fused (graph core0793) (root 8) 2 0) DegreeOneSmallSpectrum929.graph fusedMap0793swap=true := by decide +kernel
theorem certified0793swap : Certified (graph core0793) (root 8) 2 0 :=
  of_native_maps core0793 DegreeOneSmallSpectrum927.graph DegreeOneSmallSpectrum929.graph
    sourceMap0793swap fusedMap0793swap sourceMap0793swap_checked fusedMap0793swap_checked
    DegreeOneSmallComparisons.comparison0793
#print axioms sourceMap0793swap_checked
#print axioms fusedMap0793swap_checked
#print axioms certified0793swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
