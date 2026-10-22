/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3235 : Family 8 := level8.get ⟨271,by decide⟩
def sourceMap3235 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3235 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3235_checked : acceptsGraphIso
    (source (graph core3235) (root 8) 0 5) DegreeTwoThreeSpectrum4693.graph sourceMap3235=true := by decide +kernel
theorem fusedMap3235_checked : acceptsGraphIso
    (fused (graph core3235) (root 8) 0 5) DegreeTwoThreeSpectrum4204.graph fusedMap3235=true := by decide +kernel
theorem certified3235 : Certified (graph core3235) (root 8) 0 5 :=
  of_native_maps core3235 DegreeTwoThreeSpectrum4693.graph DegreeTwoThreeSpectrum4204.graph
    sourceMap3235 fusedMap3235 sourceMap3235_checked fusedMap3235_checked
    DegreeTwoThreeFiniteComparisons.comparison3235
#print axioms sourceMap3235_checked
#print axioms fusedMap3235_checked
#print axioms certified3235
def sourceMap3235swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,11] (sourceLabel 8 5 0 v)
def fusedMap3235swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3235swap_checked : acceptsGraphIso
    (source (graph core3235) (root 8) 5 0) DegreeTwoThreeSpectrum4693.graph sourceMap3235swap=true := by decide +kernel
theorem fusedMap3235swap_checked : acceptsGraphIso
    (fused (graph core3235) (root 8) 5 0) DegreeTwoThreeSpectrum4204.graph fusedMap3235swap=true := by decide +kernel
theorem certified3235swap : Certified (graph core3235) (root 8) 5 0 :=
  of_native_maps core3235 DegreeTwoThreeSpectrum4693.graph DegreeTwoThreeSpectrum4204.graph
    sourceMap3235swap fusedMap3235swap sourceMap3235swap_checked fusedMap3235swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3235
#print axioms sourceMap3235swap_checked
#print axioms fusedMap3235swap_checked
#print axioms certified3235swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
