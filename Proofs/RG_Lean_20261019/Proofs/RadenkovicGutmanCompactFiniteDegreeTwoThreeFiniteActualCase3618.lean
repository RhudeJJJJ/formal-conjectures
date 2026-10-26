/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3618 : Family 8 := level8.get ⟨225,by decide⟩
def sourceMap3618 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3618 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3618_checked : acceptsGraphIso
    (source (graph core3618) (root 8) 0 6) DegreeTwoThreeSpectrum6359.graph sourceMap3618=true := by decide +kernel
theorem fusedMap3618_checked : acceptsGraphIso
    (fused (graph core3618) (root 8) 0 6) DegreeTwoThreeSpectrum5311.graph fusedMap3618=true := by decide +kernel
theorem certified3618 : Certified (graph core3618) (root 8) 0 6 :=
  of_native_maps core3618 DegreeTwoThreeSpectrum6359.graph DegreeTwoThreeSpectrum5311.graph
    sourceMap3618 fusedMap3618 sourceMap3618_checked fusedMap3618_checked
    DegreeTwoThreeFiniteComparisons.comparison3618
#print axioms sourceMap3618_checked
#print axioms fusedMap3618_checked
#print axioms certified3618
def sourceMap3618swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3618swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3618swap_checked : acceptsGraphIso
    (source (graph core3618) (root 8) 6 0) DegreeTwoThreeSpectrum6359.graph sourceMap3618swap=true := by decide +kernel
theorem fusedMap3618swap_checked : acceptsGraphIso
    (fused (graph core3618) (root 8) 6 0) DegreeTwoThreeSpectrum5311.graph fusedMap3618swap=true := by decide +kernel
theorem certified3618swap : Certified (graph core3618) (root 8) 6 0 :=
  of_native_maps core3618 DegreeTwoThreeSpectrum6359.graph DegreeTwoThreeSpectrum5311.graph
    sourceMap3618swap fusedMap3618swap sourceMap3618swap_checked fusedMap3618swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3618
#print axioms sourceMap3618swap_checked
#print axioms fusedMap3618swap_checked
#print axioms certified3618swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
