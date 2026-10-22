/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2618 : Family 10 := level10.get ⟨588,by decide⟩
def sourceMap2618 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2618 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2618_checked : acceptsGraphIso
    (source (graph core2618) (root 10) 0 4) DegreeTwoThreeSpectrum6277.graph sourceMap2618=true := by decide +kernel
theorem fusedMap2618_checked : acceptsGraphIso
    (fused (graph core2618) (root 10) 0 4) DegreeTwoThreeSpectrum5259.graph fusedMap2618=true := by decide +kernel
theorem certified2618 : Certified (graph core2618) (root 10) 0 4 :=
  of_native_maps core2618 DegreeTwoThreeSpectrum6277.graph DegreeTwoThreeSpectrum5259.graph
    sourceMap2618 fusedMap2618 sourceMap2618_checked fusedMap2618_checked
    DegreeTwoThreeFiniteComparisons.comparison2618
#print axioms sourceMap2618_checked
#print axioms fusedMap2618_checked
#print axioms certified2618
def sourceMap2618swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2618swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2618swap_checked : acceptsGraphIso
    (source (graph core2618) (root 10) 4 0) DegreeTwoThreeSpectrum6277.graph sourceMap2618swap=true := by decide +kernel
theorem fusedMap2618swap_checked : acceptsGraphIso
    (fused (graph core2618) (root 10) 4 0) DegreeTwoThreeSpectrum5259.graph fusedMap2618swap=true := by decide +kernel
theorem certified2618swap : Certified (graph core2618) (root 10) 4 0 :=
  of_native_maps core2618 DegreeTwoThreeSpectrum6277.graph DegreeTwoThreeSpectrum5259.graph
    sourceMap2618swap fusedMap2618swap sourceMap2618swap_checked fusedMap2618swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2618
#print axioms sourceMap2618swap_checked
#print axioms fusedMap2618swap_checked
#print axioms certified2618swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
