/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3778 : Family 6 := level6.get ⟨17,by decide⟩
def sourceMap3778 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 6 1 4 v)
def fusedMap3778 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 1 4 v)
theorem sourceMap3778_checked : acceptsGraphIso
    (source (graph core3778) (root 6) 1 4) DegreeTwoThreeSpectrum1912.graph sourceMap3778=true := by decide +kernel
theorem fusedMap3778_checked : acceptsGraphIso
    (fused (graph core3778) (root 6) 1 4) DegreeTwoThreeSpectrum1729.graph fusedMap3778=true := by decide +kernel
theorem certified3778 : Certified (graph core3778) (root 6) 1 4 :=
  of_native_maps core3778 DegreeTwoThreeSpectrum1912.graph DegreeTwoThreeSpectrum1729.graph
    sourceMap3778 fusedMap3778 sourceMap3778_checked fusedMap3778_checked
    DegreeTwoThreeFiniteComparisons.comparison3778
#print axioms sourceMap3778_checked
#print axioms fusedMap3778_checked
#print axioms certified3778
def sourceMap3778swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 2) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,9,10,11,12,13,7,8] (sourceLabel 6 4 1 v)
def fusedMap3778swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13] (fusedLabel 6 4 1 v)
theorem sourceMap3778swap_checked : acceptsGraphIso
    (source (graph core3778) (root 6) 4 1) DegreeTwoThreeSpectrum1912.graph sourceMap3778swap=true := by decide +kernel
theorem fusedMap3778swap_checked : acceptsGraphIso
    (fused (graph core3778) (root 6) 4 1) DegreeTwoThreeSpectrum1729.graph fusedMap3778swap=true := by decide +kernel
theorem certified3778swap : Certified (graph core3778) (root 6) 4 1 :=
  of_native_maps core3778 DegreeTwoThreeSpectrum1912.graph DegreeTwoThreeSpectrum1729.graph
    sourceMap3778swap fusedMap3778swap sourceMap3778swap_checked fusedMap3778swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3778
#print axioms sourceMap3778swap_checked
#print axioms fusedMap3778swap_checked
#print axioms certified3778swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
