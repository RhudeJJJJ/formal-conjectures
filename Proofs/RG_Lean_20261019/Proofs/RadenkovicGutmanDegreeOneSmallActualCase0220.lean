/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0220 : Family 5 := level5.get ⟨6,by decide⟩
def sourceMap0220 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 2) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,8,6,7] (sourceLabel 5 0 1 v)
def fusedMap0220 : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 5 0 1 v)
theorem sourceMap0220_checked : acceptsGraphIso
    (source (graph core0220) (root 5) 0 1) DegreeOneSmallSpectrum046.graph sourceMap0220=true := by decide +kernel
theorem fusedMap0220_checked : acceptsGraphIso
    (fused (graph core0220) (root 5) 0 1) DegreeOneSmallSpectrum047.graph fusedMap0220=true := by decide +kernel
theorem certified0220 : Certified (graph core0220) (root 5) 0 1 :=
  of_native_maps core0220 DegreeOneSmallSpectrum046.graph DegreeOneSmallSpectrum047.graph
    sourceMap0220 fusedMap0220 sourceMap0220_checked fusedMap0220_checked
    DegreeOneSmallComparisons.comparison0220
#print axioms sourceMap0220_checked
#print axioms fusedMap0220_checked
#print axioms certified0220
def sourceMap0220swap : (Vertices 5 ⊕ Fin 2 ⊕ Fin 1) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,6,7,8] (sourceLabel 5 1 0 v)
def fusedMap0220swap : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 5 1 0 v)
theorem sourceMap0220swap_checked : acceptsGraphIso
    (source (graph core0220) (root 5) 1 0) DegreeOneSmallSpectrum046.graph sourceMap0220swap=true := by decide +kernel
theorem fusedMap0220swap_checked : acceptsGraphIso
    (fused (graph core0220) (root 5) 1 0) DegreeOneSmallSpectrum047.graph fusedMap0220swap=true := by decide +kernel
theorem certified0220swap : Certified (graph core0220) (root 5) 1 0 :=
  of_native_maps core0220 DegreeOneSmallSpectrum046.graph DegreeOneSmallSpectrum047.graph
    sourceMap0220swap fusedMap0220swap sourceMap0220swap_checked fusedMap0220swap_checked
    DegreeOneSmallComparisons.comparison0220
#print axioms sourceMap0220swap_checked
#print axioms fusedMap0220swap_checked
#print axioms certified0220swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
