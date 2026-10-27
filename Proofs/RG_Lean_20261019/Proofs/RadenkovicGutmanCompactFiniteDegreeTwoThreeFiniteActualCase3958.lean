/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3958 : Family 7 := level7.get ⟨36,by decide⟩
def sourceMap3958 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3958 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3958_checked : acceptsGraphIso
    (source (graph core3958) (root 7) 1 5) DegreeTwoThreeSpectrum4364.graph sourceMap3958=true := by decide +kernel
theorem fusedMap3958_checked : acceptsGraphIso
    (fused (graph core3958) (root 7) 1 5) DegreeTwoThreeSpectrum3953.graph fusedMap3958=true := by decide +kernel
theorem certified3958 : Certified (graph core3958) (root 7) 1 5 :=
  of_native_maps core3958 DegreeTwoThreeSpectrum4364.graph DegreeTwoThreeSpectrum3953.graph
    sourceMap3958 fusedMap3958 sourceMap3958_checked fusedMap3958_checked
    DegreeTwoThreeFiniteComparisons.comparison3958
#print axioms sourceMap3958_checked
#print axioms fusedMap3958_checked
#print axioms certified3958
def sourceMap3958swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,15,8,9] (sourceLabel 7 5 1 v)
def fusedMap3958swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3958swap_checked : acceptsGraphIso
    (source (graph core3958) (root 7) 5 1) DegreeTwoThreeSpectrum4364.graph sourceMap3958swap=true := by decide +kernel
theorem fusedMap3958swap_checked : acceptsGraphIso
    (fused (graph core3958) (root 7) 5 1) DegreeTwoThreeSpectrum3953.graph fusedMap3958swap=true := by decide +kernel
theorem certified3958swap : Certified (graph core3958) (root 7) 5 1 :=
  of_native_maps core3958 DegreeTwoThreeSpectrum4364.graph DegreeTwoThreeSpectrum3953.graph
    sourceMap3958swap fusedMap3958swap sourceMap3958swap_checked fusedMap3958swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3958
#print axioms sourceMap3958swap_checked
#print axioms fusedMap3958swap_checked
#print axioms certified3958swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
