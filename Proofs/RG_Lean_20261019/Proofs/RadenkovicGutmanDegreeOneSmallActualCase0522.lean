/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0522 : Family 7 := level7.get ⟨14,by decide⟩
def sourceMap0522 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (sourceLabel 7 0 3 v)
def fusedMap0522 : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 0 3 v)
theorem sourceMap0522_checked : acceptsGraphIso
    (source (graph core0522) (root 7) 0 3) DegreeOneSmallSpectrum928.graph sourceMap0522=true := by decide +kernel
theorem fusedMap0522_checked : acceptsGraphIso
    (fused (graph core0522) (root 7) 0 3) DegreeOneSmallSpectrum929.graph fusedMap0522=true := by decide +kernel
theorem certified0522 : Certified (graph core0522) (root 7) 0 3 :=
  of_native_maps core0522 DegreeOneSmallSpectrum928.graph DegreeOneSmallSpectrum929.graph
    sourceMap0522 fusedMap0522 sourceMap0522_checked fusedMap0522_checked
    DegreeOneSmallComparisons.comparison0522
#print axioms sourceMap0522_checked
#print axioms fusedMap0522_checked
#print axioms certified0522
def sourceMap0522swap : (Vertices 7 ⊕ Fin 4 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 7 3 0 v)
def fusedMap0522swap : (Vertices 7 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 7 3 0 v)
theorem sourceMap0522swap_checked : acceptsGraphIso
    (source (graph core0522) (root 7) 3 0) DegreeOneSmallSpectrum928.graph sourceMap0522swap=true := by decide +kernel
theorem fusedMap0522swap_checked : acceptsGraphIso
    (fused (graph core0522) (root 7) 3 0) DegreeOneSmallSpectrum929.graph fusedMap0522swap=true := by decide +kernel
theorem certified0522swap : Certified (graph core0522) (root 7) 3 0 :=
  of_native_maps core0522 DegreeOneSmallSpectrum928.graph DegreeOneSmallSpectrum929.graph
    sourceMap0522swap fusedMap0522swap sourceMap0522swap_checked fusedMap0522swap_checked
    DegreeOneSmallComparisons.comparison0522
#print axioms sourceMap0522swap_checked
#print axioms fusedMap0522swap_checked
#print axioms certified0522swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
