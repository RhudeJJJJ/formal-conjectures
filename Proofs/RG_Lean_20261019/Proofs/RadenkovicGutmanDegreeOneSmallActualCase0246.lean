/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0246 : Family 5 := level5.get ⟨9,by decide⟩
def sourceMap0246 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 0 3 v)
def fusedMap0246 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 0 3 v)
theorem sourceMap0246_checked : acceptsGraphIso
    (source (graph core0246) (root 5) 0 3) DegreeOneSmallSpectrum204.graph sourceMap0246=true := by decide +kernel
theorem fusedMap0246_checked : acceptsGraphIso
    (fused (graph core0246) (root 5) 0 3) DegreeOneSmallSpectrum207.graph fusedMap0246=true := by decide +kernel
theorem certified0246 : Certified (graph core0246) (root 5) 0 3 :=
  of_native_maps core0246 DegreeOneSmallSpectrum204.graph DegreeOneSmallSpectrum207.graph
    sourceMap0246 fusedMap0246 sourceMap0246_checked fusedMap0246_checked
    DegreeOneSmallComparisons.comparison0246
#print axioms sourceMap0246_checked
#print axioms fusedMap0246_checked
#print axioms certified0246
def sourceMap0246swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,7,8,9,10,6] (sourceLabel 5 3 0 v)
def fusedMap0246swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 3 0 v)
theorem sourceMap0246swap_checked : acceptsGraphIso
    (source (graph core0246) (root 5) 3 0) DegreeOneSmallSpectrum204.graph sourceMap0246swap=true := by decide +kernel
theorem fusedMap0246swap_checked : acceptsGraphIso
    (fused (graph core0246) (root 5) 3 0) DegreeOneSmallSpectrum207.graph fusedMap0246swap=true := by decide +kernel
theorem certified0246swap : Certified (graph core0246) (root 5) 3 0 :=
  of_native_maps core0246 DegreeOneSmallSpectrum204.graph DegreeOneSmallSpectrum207.graph
    sourceMap0246swap fusedMap0246swap sourceMap0246swap_checked fusedMap0246swap_checked
    DegreeOneSmallComparisons.comparison0246
#print axioms sourceMap0246swap_checked
#print axioms fusedMap0246swap_checked
#print axioms certified0246swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
