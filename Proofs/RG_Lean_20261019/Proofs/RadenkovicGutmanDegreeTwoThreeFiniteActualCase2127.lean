/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2127 : Family 8 := level8.get ⟨43,by decide⟩
def sourceMap2127 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12] (sourceLabel 8 0 4 v)
def fusedMap2127 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2127_checked : acceptsGraphIso
    (source (graph core2127) (root 8) 0 4) DegreeTwoThreeSpectrum2560.graph sourceMap2127=true := by decide +kernel
theorem fusedMap2127_checked : acceptsGraphIso
    (fused (graph core2127) (root 8) 0 4) DegreeTwoThreeSpectrum2325.graph fusedMap2127=true := by decide +kernel
theorem certified2127 : Certified (graph core2127) (root 8) 0 4 :=
  of_native_maps core2127 DegreeTwoThreeSpectrum2560.graph DegreeTwoThreeSpectrum2325.graph
    sourceMap2127 fusedMap2127 sourceMap2127_checked fusedMap2127_checked
    DegreeTwoThreeFiniteComparisons.comparison2127
#print axioms sourceMap2127_checked
#print axioms fusedMap2127_checked
#print axioms certified2127
def sourceMap2127swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,13,8,9,10,11,12,14] (sourceLabel 8 4 0 v)
def fusedMap2127swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2127swap_checked : acceptsGraphIso
    (source (graph core2127) (root 8) 4 0) DegreeTwoThreeSpectrum2560.graph sourceMap2127swap=true := by decide +kernel
theorem fusedMap2127swap_checked : acceptsGraphIso
    (fused (graph core2127) (root 8) 4 0) DegreeTwoThreeSpectrum2325.graph fusedMap2127swap=true := by decide +kernel
theorem certified2127swap : Certified (graph core2127) (root 8) 4 0 :=
  of_native_maps core2127 DegreeTwoThreeSpectrum2560.graph DegreeTwoThreeSpectrum2325.graph
    sourceMap2127swap fusedMap2127swap sourceMap2127swap_checked fusedMap2127swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2127
#print axioms sourceMap2127swap_checked
#print axioms fusedMap2127swap_checked
#print axioms certified2127swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
