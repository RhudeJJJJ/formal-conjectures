/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0809 : Family 8 := level8.get ⟨21,by decide⟩
def sourceMap0809 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0809 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0809_checked : acceptsGraphIso
    (source (graph core0809) (root 8) 0 2) DegreeOneSmallSpectrum954.graph sourceMap0809=true := by decide +kernel
theorem fusedMap0809_checked : acceptsGraphIso
    (fused (graph core0809) (root 8) 0 2) DegreeOneSmallSpectrum956.graph fusedMap0809=true := by decide +kernel
theorem certified0809 : Certified (graph core0809) (root 8) 0 2 :=
  of_native_maps core0809 DegreeOneSmallSpectrum954.graph DegreeOneSmallSpectrum956.graph
    sourceMap0809 fusedMap0809 sourceMap0809_checked fusedMap0809_checked
    DegreeOneSmallComparisons.comparison0809
#print axioms sourceMap0809_checked
#print axioms fusedMap0809_checked
#print axioms certified0809
def sourceMap0809swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0809swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0809swap_checked : acceptsGraphIso
    (source (graph core0809) (root 8) 2 0) DegreeOneSmallSpectrum954.graph sourceMap0809swap=true := by decide +kernel
theorem fusedMap0809swap_checked : acceptsGraphIso
    (fused (graph core0809) (root 8) 2 0) DegreeOneSmallSpectrum956.graph fusedMap0809swap=true := by decide +kernel
theorem certified0809swap : Certified (graph core0809) (root 8) 2 0 :=
  of_native_maps core0809 DegreeOneSmallSpectrum954.graph DegreeOneSmallSpectrum956.graph
    sourceMap0809swap fusedMap0809swap sourceMap0809swap_checked fusedMap0809swap_checked
    DegreeOneSmallComparisons.comparison0809
#print axioms sourceMap0809swap_checked
#print axioms fusedMap0809swap_checked
#print axioms certified0809swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
