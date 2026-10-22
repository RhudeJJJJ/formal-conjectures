/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2074 : Family 6 := level6.get ⟨28,by decide⟩
def sourceMap2074 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap2074 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap2074_checked : acceptsGraphIso
    (source (graph core2074) (root 6) 0 4) DegreeOneSmallSpectrum1323.graph sourceMap2074=true := by decide +kernel
theorem fusedMap2074_checked : acceptsGraphIso
    (fused (graph core2074) (root 6) 0 4) DegreeOneSmallSpectrum910.graph fusedMap2074=true := by decide +kernel
theorem certified2074 : Certified (graph core2074) (root 6) 0 4 :=
  of_native_maps core2074 DegreeOneSmallSpectrum1323.graph DegreeOneSmallSpectrum910.graph
    sourceMap2074 fusedMap2074 sourceMap2074_checked fusedMap2074_checked
    DegreeTwoThreeFiniteComparisons.comparison2074
#print axioms sourceMap2074_checked
#print axioms fusedMap2074_checked
#print axioms certified2074
def sourceMap2074swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,8] (sourceLabel 6 4 0 v)
def fusedMap2074swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap2074swap_checked : acceptsGraphIso
    (source (graph core2074) (root 6) 4 0) DegreeOneSmallSpectrum1323.graph sourceMap2074swap=true := by decide +kernel
theorem fusedMap2074swap_checked : acceptsGraphIso
    (fused (graph core2074) (root 6) 4 0) DegreeOneSmallSpectrum910.graph fusedMap2074swap=true := by decide +kernel
theorem certified2074swap : Certified (graph core2074) (root 6) 4 0 :=
  of_native_maps core2074 DegreeOneSmallSpectrum1323.graph DegreeOneSmallSpectrum910.graph
    sourceMap2074swap fusedMap2074swap sourceMap2074swap_checked fusedMap2074swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2074
#print axioms sourceMap2074swap_checked
#print axioms fusedMap2074swap_checked
#print axioms certified2074swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
