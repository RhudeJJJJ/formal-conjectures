/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0628 : Family 7 := level7.get ⟨43,by decide⟩
def sourceMap0628 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,9,7,8] (sourceLabel 7 0 1 v)
def fusedMap0628 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap0628_checked : acceptsGraphIso
    (source (graph core0628) (root 7) 0 1) DegreeOneSmallSpectrum336.graph sourceMap0628=true := by decide +kernel
theorem fusedMap0628_checked : acceptsGraphIso
    (fused (graph core0628) (root 7) 0 1) DegreeOneSmallSpectrum204.graph fusedMap0628=true := by decide +kernel
theorem certified0628 : Certified (graph core0628) (root 7) 0 1 :=
  of_native_maps core0628 DegreeOneSmallSpectrum336.graph DegreeOneSmallSpectrum204.graph
    sourceMap0628 fusedMap0628 sourceMap0628_checked fusedMap0628_checked
    DegreeOneSmallComparisons.comparison0628
#print axioms sourceMap0628_checked
#print axioms fusedMap0628_checked
#print axioms certified0628
def sourceMap0628swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (sourceLabel 7 1 0 v)
def fusedMap0628swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap0628swap_checked : acceptsGraphIso
    (source (graph core0628) (root 7) 1 0) DegreeOneSmallSpectrum336.graph sourceMap0628swap=true := by decide +kernel
theorem fusedMap0628swap_checked : acceptsGraphIso
    (fused (graph core0628) (root 7) 1 0) DegreeOneSmallSpectrum204.graph fusedMap0628swap=true := by decide +kernel
theorem certified0628swap : Certified (graph core0628) (root 7) 1 0 :=
  of_native_maps core0628 DegreeOneSmallSpectrum336.graph DegreeOneSmallSpectrum204.graph
    sourceMap0628swap fusedMap0628swap sourceMap0628swap_checked fusedMap0628swap_checked
    DegreeOneSmallComparisons.comparison0628
#print axioms sourceMap0628swap_checked
#print axioms fusedMap0628swap_checked
#print axioms certified0628swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
