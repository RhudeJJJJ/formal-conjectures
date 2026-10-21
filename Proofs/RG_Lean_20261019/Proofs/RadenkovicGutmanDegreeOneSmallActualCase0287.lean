/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0287 : Family 6 := level6.get ⟨2,by decide⟩
def sourceMap0287 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (sourceLabel 6 0 2 v)
def fusedMap0287 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0287_checked : acceptsGraphIso
    (source (graph core0287) (root 6) 0 2) DegreeOneSmallSpectrum216.graph sourceMap0287=true := by decide +kernel
theorem fusedMap0287_checked : acceptsGraphIso
    (fused (graph core0287) (root 6) 0 2) DegreeOneSmallSpectrum165.graph fusedMap0287=true := by decide +kernel
theorem certified0287 : Certified (graph core0287) (root 6) 0 2 :=
  of_native_maps core0287 DegreeOneSmallSpectrum216.graph DegreeOneSmallSpectrum165.graph
    sourceMap0287 fusedMap0287 sourceMap0287_checked fusedMap0287_checked
    DegreeOneSmallComparisons.comparison0287
#print axioms sourceMap0287_checked
#print axioms fusedMap0287_checked
#print axioms certified0287
def sourceMap0287swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 6 2 0 v)
def fusedMap0287swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0287swap_checked : acceptsGraphIso
    (source (graph core0287) (root 6) 2 0) DegreeOneSmallSpectrum216.graph sourceMap0287swap=true := by decide +kernel
theorem fusedMap0287swap_checked : acceptsGraphIso
    (fused (graph core0287) (root 6) 2 0) DegreeOneSmallSpectrum165.graph fusedMap0287swap=true := by decide +kernel
theorem certified0287swap : Certified (graph core0287) (root 6) 2 0 :=
  of_native_maps core0287 DegreeOneSmallSpectrum216.graph DegreeOneSmallSpectrum165.graph
    sourceMap0287swap fusedMap0287swap sourceMap0287swap_checked fusedMap0287swap_checked
    DegreeOneSmallComparisons.comparison0287
#print axioms sourceMap0287swap_checked
#print axioms fusedMap0287swap_checked
#print axioms certified0287swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
