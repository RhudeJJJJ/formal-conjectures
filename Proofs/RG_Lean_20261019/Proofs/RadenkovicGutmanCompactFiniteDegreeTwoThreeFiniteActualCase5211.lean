/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5211 : Family 8 := level8.get ⟨265,by decide⟩
def sourceMap5211 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,5,6,7,8,9,10,11,12,2,3,4,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5211 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5211_checked : acceptsGraphIso
    (source (graph core5211) (root 8) 2 4) DegreeTwoThreeSpectrum7553.graph sourceMap5211=true := by decide +kernel
theorem fusedMap5211_checked : acceptsGraphIso
    (fused (graph core5211) (root 8) 2 4) DegreeTwoThreeSpectrum5965.graph fusedMap5211=true := by decide +kernel
theorem certified5211 : Certified (graph core5211) (root 8) 2 4 :=
  of_native_maps core5211 DegreeTwoThreeSpectrum7553.graph DegreeTwoThreeSpectrum5965.graph
    sourceMap5211 fusedMap5211 sourceMap5211_checked fusedMap5211_checked
    DegreeTwoThreeFiniteComparisons.comparison5211
#print axioms sourceMap5211_checked
#print axioms fusedMap5211_checked
#print axioms certified5211
def sourceMap5211swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,5,6,7,8,9,10,11,12,0,13,14,15,16,2,3,4] (sourceLabel 8 4 2 v)
def fusedMap5211swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5211swap_checked : acceptsGraphIso
    (source (graph core5211) (root 8) 4 2) DegreeTwoThreeSpectrum7553.graph sourceMap5211swap=true := by decide +kernel
theorem fusedMap5211swap_checked : acceptsGraphIso
    (fused (graph core5211) (root 8) 4 2) DegreeTwoThreeSpectrum5965.graph fusedMap5211swap=true := by decide +kernel
theorem certified5211swap : Certified (graph core5211) (root 8) 4 2 :=
  of_native_maps core5211 DegreeTwoThreeSpectrum7553.graph DegreeTwoThreeSpectrum5965.graph
    sourceMap5211swap fusedMap5211swap sourceMap5211swap_checked fusedMap5211swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5211
#print axioms sourceMap5211swap_checked
#print axioms fusedMap5211swap_checked
#print axioms certified5211swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
