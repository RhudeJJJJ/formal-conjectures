/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons75
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3784 : Family 6 := level6.get ⟨31,by decide⟩
def sourceMap3784 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 5) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13] (sourceLabel 6 1 4 v)
def fusedMap3784 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 1 4 v)
theorem sourceMap3784_checked : acceptsGraphIso
    (source (graph core3784) (root 6) 1 4) DegreeTwoThreeSpectrum2150.graph sourceMap3784=true := by decide +kernel
theorem fusedMap3784_checked : acceptsGraphIso
    (fused (graph core3784) (root 6) 1 4) DegreeTwoThreeSpectrum1834.graph fusedMap3784=true := by decide +kernel
theorem certified3784 : Certified (graph core3784) (root 6) 1 4 :=
  of_native_maps core3784 DegreeTwoThreeSpectrum2150.graph DegreeTwoThreeSpectrum1834.graph
    sourceMap3784 fusedMap3784 sourceMap3784_checked fusedMap3784_checked
    DegreeTwoThreeFiniteComparisons.comparison3784
#print axioms sourceMap3784_checked
#print axioms fusedMap3784_checked
#print axioms certified3784
def sourceMap3784swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 2) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,0,10,11,12,13,8,9] (sourceLabel 6 4 1 v)
def fusedMap3784swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 4 1 v)
theorem sourceMap3784swap_checked : acceptsGraphIso
    (source (graph core3784) (root 6) 4 1) DegreeTwoThreeSpectrum2150.graph sourceMap3784swap=true := by decide +kernel
theorem fusedMap3784swap_checked : acceptsGraphIso
    (fused (graph core3784) (root 6) 4 1) DegreeTwoThreeSpectrum1834.graph fusedMap3784swap=true := by decide +kernel
theorem certified3784swap : Certified (graph core3784) (root 6) 4 1 :=
  of_native_maps core3784 DegreeTwoThreeSpectrum2150.graph DegreeTwoThreeSpectrum1834.graph
    sourceMap3784swap fusedMap3784swap sourceMap3784swap_checked fusedMap3784swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3784
#print axioms sourceMap3784swap_checked
#print axioms fusedMap3784swap_checked
#print axioms certified3784swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
