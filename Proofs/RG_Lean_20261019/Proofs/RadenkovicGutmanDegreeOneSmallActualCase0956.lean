/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0956 : Family 8 := level8.get ⟨76,by decide⟩
def sourceMap0956 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap0956 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (fusedLabel 8 0 1 v)
theorem sourceMap0956_checked : acceptsGraphIso
    (source (graph core0956) (root 8) 0 1) DegreeOneSmallSpectrum548.graph sourceMap0956=true := by decide +kernel
theorem fusedMap0956_checked : acceptsGraphIso
    (fused (graph core0956) (root 8) 0 1) DegreeOneSmallSpectrum581.graph fusedMap0956=true := by decide +kernel
theorem certified0956 : Certified (graph core0956) (root 8) 0 1 :=
  of_native_maps core0956 DegreeOneSmallSpectrum548.graph DegreeOneSmallSpectrum581.graph
    sourceMap0956 fusedMap0956 sourceMap0956_checked fusedMap0956_checked
    DegreeOneSmallComparisons.comparison0956
#print axioms sourceMap0956_checked
#print axioms fusedMap0956_checked
#print axioms certified0956
def sourceMap0956swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap0956swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (fusedLabel 8 1 0 v)
theorem sourceMap0956swap_checked : acceptsGraphIso
    (source (graph core0956) (root 8) 1 0) DegreeOneSmallSpectrum548.graph sourceMap0956swap=true := by decide +kernel
theorem fusedMap0956swap_checked : acceptsGraphIso
    (fused (graph core0956) (root 8) 1 0) DegreeOneSmallSpectrum581.graph fusedMap0956swap=true := by decide +kernel
theorem certified0956swap : Certified (graph core0956) (root 8) 1 0 :=
  of_native_maps core0956 DegreeOneSmallSpectrum548.graph DegreeOneSmallSpectrum581.graph
    sourceMap0956swap fusedMap0956swap sourceMap0956swap_checked fusedMap0956swap_checked
    DegreeOneSmallComparisons.comparison0956
#print axioms sourceMap0956swap_checked
#print axioms fusedMap0956swap_checked
#print axioms certified0956swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
