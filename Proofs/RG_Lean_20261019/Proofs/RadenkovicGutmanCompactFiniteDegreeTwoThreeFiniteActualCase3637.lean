/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3637 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap3637 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 8) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12,13] (sourceLabel 4 0 7 v)
def fusedMap3637 : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 0 7 v)
theorem sourceMap3637_checked : acceptsGraphIso
    (source (graph core3637) (root 4) 0 7) DegreeTwoThreeSpectrum1724.graph sourceMap3637=true := by decide +kernel
theorem fusedMap3637_checked : acceptsGraphIso
    (fused (graph core3637) (root 4) 0 7) DegreeTwoThreeSpectrum1728.graph fusedMap3637=true := by decide +kernel
theorem certified3637 : Certified (graph core3637) (root 4) 0 7 :=
  of_native_maps core3637 DegreeTwoThreeSpectrum1724.graph DegreeTwoThreeSpectrum1728.graph
    sourceMap3637 fusedMap3637 sourceMap3637_checked fusedMap3637_checked
    DegreeTwoThreeFiniteComparisons.comparison3637
#print axioms sourceMap3637_checked
#print axioms fusedMap3637_checked
#print axioms certified3637
def sourceMap3637swap : (Vertices 4 ⊕ Fin 8 ⊕ Fin 1) → Fin 14 :=
  fun v => ![2,3,4,5,6,1,0,8,9,10,11,12,13,7] (sourceLabel 4 7 0 v)
def fusedMap3637swap : (Vertices 4 ⊕ Fin 9) → Fin 14 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12,13] (fusedLabel 4 7 0 v)
theorem sourceMap3637swap_checked : acceptsGraphIso
    (source (graph core3637) (root 4) 7 0) DegreeTwoThreeSpectrum1724.graph sourceMap3637swap=true := by decide +kernel
theorem fusedMap3637swap_checked : acceptsGraphIso
    (fused (graph core3637) (root 4) 7 0) DegreeTwoThreeSpectrum1728.graph fusedMap3637swap=true := by decide +kernel
theorem certified3637swap : Certified (graph core3637) (root 4) 7 0 :=
  of_native_maps core3637 DegreeTwoThreeSpectrum1724.graph DegreeTwoThreeSpectrum1728.graph
    sourceMap3637swap fusedMap3637swap sourceMap3637swap_checked fusedMap3637swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3637
#print axioms sourceMap3637swap_checked
#print axioms fusedMap3637swap_checked
#print axioms certified3637swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
