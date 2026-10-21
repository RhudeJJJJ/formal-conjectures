/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0368 : Family 6 := level6.get ⟨14,by decide⟩
def sourceMap0368 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (sourceLabel 6 0 2 v)
def fusedMap0368 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0368_checked : acceptsGraphIso
    (source (graph core0368) (root 6) 0 2) DegreeOneSmallSpectrum221.graph sourceMap0368=true := by decide +kernel
theorem fusedMap0368_checked : acceptsGraphIso
    (fused (graph core0368) (root 6) 0 2) DegreeOneSmallSpectrum222.graph fusedMap0368=true := by decide +kernel
theorem certified0368 : Certified (graph core0368) (root 6) 0 2 :=
  of_native_maps core0368 DegreeOneSmallSpectrum221.graph DegreeOneSmallSpectrum222.graph
    sourceMap0368 fusedMap0368 sourceMap0368_checked fusedMap0368_checked
    DegreeOneSmallComparisons.comparison0368
#print axioms sourceMap0368_checked
#print axioms fusedMap0368_checked
#print axioms certified0368
def sourceMap0368swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 6 2 0 v)
def fusedMap0368swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0368swap_checked : acceptsGraphIso
    (source (graph core0368) (root 6) 2 0) DegreeOneSmallSpectrum221.graph sourceMap0368swap=true := by decide +kernel
theorem fusedMap0368swap_checked : acceptsGraphIso
    (fused (graph core0368) (root 6) 2 0) DegreeOneSmallSpectrum222.graph fusedMap0368swap=true := by decide +kernel
theorem certified0368swap : Certified (graph core0368) (root 6) 2 0 :=
  of_native_maps core0368 DegreeOneSmallSpectrum221.graph DegreeOneSmallSpectrum222.graph
    sourceMap0368swap fusedMap0368swap sourceMap0368swap_checked fusedMap0368swap_checked
    DegreeOneSmallComparisons.comparison0368
#print axioms sourceMap0368swap_checked
#print axioms fusedMap0368swap_checked
#print axioms certified0368swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
