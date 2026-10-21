/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0852 : Family 8 := level8.get ⟨37,by decide⟩
def sourceMap0852 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,10,8,9] (sourceLabel 8 0 1 v)
def fusedMap0852 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (fusedLabel 8 0 1 v)
theorem sourceMap0852_checked : acceptsGraphIso
    (source (graph core0852) (root 8) 0 1) DegreeOneSmallSpectrum422.graph sourceMap0852=true := by decide +kernel
theorem fusedMap0852_checked : acceptsGraphIso
    (fused (graph core0852) (root 8) 0 1) DegreeOneSmallSpectrum427.graph fusedMap0852=true := by decide +kernel
theorem certified0852 : Certified (graph core0852) (root 8) 0 1 :=
  of_native_maps core0852 DegreeOneSmallSpectrum422.graph DegreeOneSmallSpectrum427.graph
    sourceMap0852 fusedMap0852 sourceMap0852_checked fusedMap0852_checked
    DegreeOneSmallComparisons.comparison0852
#print axioms sourceMap0852_checked
#print axioms fusedMap0852_checked
#print axioms certified0852
def sourceMap0852swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,8,9,10] (sourceLabel 8 1 0 v)
def fusedMap0852swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (fusedLabel 8 1 0 v)
theorem sourceMap0852swap_checked : acceptsGraphIso
    (source (graph core0852) (root 8) 1 0) DegreeOneSmallSpectrum422.graph sourceMap0852swap=true := by decide +kernel
theorem fusedMap0852swap_checked : acceptsGraphIso
    (fused (graph core0852) (root 8) 1 0) DegreeOneSmallSpectrum427.graph fusedMap0852swap=true := by decide +kernel
theorem certified0852swap : Certified (graph core0852) (root 8) 1 0 :=
  of_native_maps core0852 DegreeOneSmallSpectrum422.graph DegreeOneSmallSpectrum427.graph
    sourceMap0852swap fusedMap0852swap sourceMap0852swap_checked fusedMap0852swap_checked
    DegreeOneSmallComparisons.comparison0852
#print axioms sourceMap0852swap_checked
#print axioms fusedMap0852swap_checked
#print axioms certified0852swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
