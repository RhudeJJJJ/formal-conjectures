/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3102 : Family 6 := level6.get ⟨41,by decide⟩
def sourceMap3102 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 6) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13] (sourceLabel 6 0 5 v)
def fusedMap3102 : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 0 5 v)
theorem sourceMap3102_checked : acceptsGraphIso
    (source (graph core3102) (root 6) 0 5) DegreeTwoThreeSpectrum1989.graph sourceMap3102=true := by decide +kernel
theorem fusedMap3102_checked : acceptsGraphIso
    (fused (graph core3102) (root 6) 0 5) DegreeTwoThreeSpectrum1757.graph fusedMap3102=true := by decide +kernel
theorem certified3102 : Certified (graph core3102) (root 6) 0 5 :=
  of_native_maps core3102 DegreeTwoThreeSpectrum1989.graph DegreeTwoThreeSpectrum1757.graph
    sourceMap3102 fusedMap3102 sourceMap3102_checked fusedMap3102_checked
    DegreeTwoThreeFiniteComparisons.comparison3102
#print axioms sourceMap3102_checked
#print axioms fusedMap3102_checked
#print axioms certified3102
def sourceMap3102swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 1) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,9] (sourceLabel 6 5 0 v)
def fusedMap3102swap : (Vertices 6 ⊕ Fin 7) → Fin 14 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13] (fusedLabel 6 5 0 v)
theorem sourceMap3102swap_checked : acceptsGraphIso
    (source (graph core3102) (root 6) 5 0) DegreeTwoThreeSpectrum1989.graph sourceMap3102swap=true := by decide +kernel
theorem fusedMap3102swap_checked : acceptsGraphIso
    (fused (graph core3102) (root 6) 5 0) DegreeTwoThreeSpectrum1757.graph fusedMap3102swap=true := by decide +kernel
theorem certified3102swap : Certified (graph core3102) (root 6) 5 0 :=
  of_native_maps core3102 DegreeTwoThreeSpectrum1989.graph DegreeTwoThreeSpectrum1757.graph
    sourceMap3102swap fusedMap3102swap sourceMap3102swap_checked fusedMap3102swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3102
#print axioms sourceMap3102swap_checked
#print axioms fusedMap3102swap_checked
#print axioms certified3102swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
