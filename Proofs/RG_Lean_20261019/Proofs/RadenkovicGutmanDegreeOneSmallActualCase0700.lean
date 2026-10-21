/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0700 : Family 7 := level7.get ⟨71,by decide⟩
def sourceMap0700 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (sourceLabel 7 0 1 v)
def fusedMap0700 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0700_checked : acceptsGraphIso
    (source (graph core0700) (root 7) 0 1) DegreeOneSmallSpectrum274.graph sourceMap0700=true := by decide +kernel
theorem fusedMap0700_checked : acceptsGraphIso
    (fused (graph core0700) (root 7) 0 1) DegreeOneSmallSpectrum275.graph fusedMap0700=true := by decide +kernel
theorem certified0700 : Certified (graph core0700) (root 7) 0 1 :=
  of_native_maps core0700 DegreeOneSmallSpectrum274.graph DegreeOneSmallSpectrum275.graph
    sourceMap0700 fusedMap0700 sourceMap0700_checked fusedMap0700_checked
    DegreeOneSmallComparisons.comparison0700
#print axioms sourceMap0700_checked
#print axioms fusedMap0700_checked
#print axioms certified0700
def sourceMap0700swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 7 1 0 v)
def fusedMap0700swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0700swap_checked : acceptsGraphIso
    (source (graph core0700) (root 7) 1 0) DegreeOneSmallSpectrum274.graph sourceMap0700swap=true := by decide +kernel
theorem fusedMap0700swap_checked : acceptsGraphIso
    (fused (graph core0700) (root 7) 1 0) DegreeOneSmallSpectrum275.graph fusedMap0700swap=true := by decide +kernel
theorem certified0700swap : Certified (graph core0700) (root 7) 1 0 :=
  of_native_maps core0700 DegreeOneSmallSpectrum274.graph DegreeOneSmallSpectrum275.graph
    sourceMap0700swap fusedMap0700swap sourceMap0700swap_checked fusedMap0700swap_checked
    DegreeOneSmallComparisons.comparison0700
#print axioms sourceMap0700swap_checked
#print axioms fusedMap0700swap_checked
#print axioms certified0700swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
