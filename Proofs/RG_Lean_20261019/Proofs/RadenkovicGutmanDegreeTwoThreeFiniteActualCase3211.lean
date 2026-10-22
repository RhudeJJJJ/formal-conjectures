/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3211 : Family 8 := level8.get ⟨211,by decide⟩
def sourceMap3211 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3211 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3211_checked : acceptsGraphIso
    (source (graph core3211) (root 8) 0 5) DegreeTwoThreeSpectrum4271.graph sourceMap3211=true := by decide +kernel
theorem fusedMap3211_checked : acceptsGraphIso
    (fused (graph core3211) (root 8) 0 5) DegreeTwoThreeSpectrum4272.graph fusedMap3211=true := by decide +kernel
theorem certified3211 : Certified (graph core3211) (root 8) 0 5 :=
  of_native_maps core3211 DegreeTwoThreeSpectrum4271.graph DegreeTwoThreeSpectrum4272.graph
    sourceMap3211 fusedMap3211 sourceMap3211_checked fusedMap3211_checked
    DegreeTwoThreeFiniteComparisons.comparison3211
#print axioms sourceMap3211_checked
#print axioms fusedMap3211_checked
#print axioms certified3211
def sourceMap3211swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3211swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3211swap_checked : acceptsGraphIso
    (source (graph core3211) (root 8) 5 0) DegreeTwoThreeSpectrum4271.graph sourceMap3211swap=true := by decide +kernel
theorem fusedMap3211swap_checked : acceptsGraphIso
    (fused (graph core3211) (root 8) 5 0) DegreeTwoThreeSpectrum4272.graph fusedMap3211swap=true := by decide +kernel
theorem certified3211swap : Certified (graph core3211) (root 8) 5 0 :=
  of_native_maps core3211 DegreeTwoThreeSpectrum4271.graph DegreeTwoThreeSpectrum4272.graph
    sourceMap3211swap fusedMap3211swap sourceMap3211swap_checked fusedMap3211swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3211
#print axioms sourceMap3211swap_checked
#print axioms fusedMap3211swap_checked
#print axioms certified3211swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
