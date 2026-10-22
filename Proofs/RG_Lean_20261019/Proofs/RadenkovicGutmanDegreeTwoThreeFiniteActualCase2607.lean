/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2607 : Family 10 := level10.get ⟨553,by decide⟩
def sourceMap2607 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2607 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2607_checked : acceptsGraphIso
    (source (graph core2607) (root 10) 0 4) DegreeTwoThreeSpectrum6166.graph sourceMap2607=true := by decide +kernel
theorem fusedMap2607_checked : acceptsGraphIso
    (fused (graph core2607) (root 10) 0 4) DegreeTwoThreeSpectrum5208.graph fusedMap2607=true := by decide +kernel
theorem certified2607 : Certified (graph core2607) (root 10) 0 4 :=
  of_native_maps core2607 DegreeTwoThreeSpectrum6166.graph DegreeTwoThreeSpectrum5208.graph
    sourceMap2607 fusedMap2607 sourceMap2607_checked fusedMap2607_checked
    DegreeTwoThreeFiniteComparisons.comparison2607
#print axioms sourceMap2607_checked
#print axioms fusedMap2607_checked
#print axioms certified2607
def sourceMap2607swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2607swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2607swap_checked : acceptsGraphIso
    (source (graph core2607) (root 10) 4 0) DegreeTwoThreeSpectrum6166.graph sourceMap2607swap=true := by decide +kernel
theorem fusedMap2607swap_checked : acceptsGraphIso
    (fused (graph core2607) (root 10) 4 0) DegreeTwoThreeSpectrum5208.graph fusedMap2607swap=true := by decide +kernel
theorem certified2607swap : Certified (graph core2607) (root 10) 4 0 :=
  of_native_maps core2607 DegreeTwoThreeSpectrum6166.graph DegreeTwoThreeSpectrum5208.graph
    sourceMap2607swap fusedMap2607swap sourceMap2607swap_checked fusedMap2607swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2607
#print axioms sourceMap2607swap_checked
#print axioms fusedMap2607swap_checked
#print axioms certified2607swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
