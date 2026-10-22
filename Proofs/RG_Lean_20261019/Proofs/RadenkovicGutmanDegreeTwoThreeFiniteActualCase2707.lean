/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2707 : Family 10 := level10.get ⟨837,by decide⟩
def sourceMap2707 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2707 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2707_checked : acceptsGraphIso
    (source (graph core2707) (root 10) 0 4) DegreeTwoThreeSpectrum6864.graph sourceMap2707=true := by decide +kernel
theorem fusedMap2707_checked : acceptsGraphIso
    (fused (graph core2707) (root 10) 0 4) DegreeTwoThreeSpectrum5666.graph fusedMap2707=true := by decide +kernel
theorem certified2707 : Certified (graph core2707) (root 10) 0 4 :=
  of_native_maps core2707 DegreeTwoThreeSpectrum6864.graph DegreeTwoThreeSpectrum5666.graph
    sourceMap2707 fusedMap2707 sourceMap2707_checked fusedMap2707_checked
    DegreeTwoThreeFiniteComparisons.comparison2707
#print axioms sourceMap2707_checked
#print axioms fusedMap2707_checked
#print axioms certified2707
def sourceMap2707swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2707swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2707swap_checked : acceptsGraphIso
    (source (graph core2707) (root 10) 4 0) DegreeTwoThreeSpectrum6864.graph sourceMap2707swap=true := by decide +kernel
theorem fusedMap2707swap_checked : acceptsGraphIso
    (fused (graph core2707) (root 10) 4 0) DegreeTwoThreeSpectrum5666.graph fusedMap2707swap=true := by decide +kernel
theorem certified2707swap : Certified (graph core2707) (root 10) 4 0 :=
  of_native_maps core2707 DegreeTwoThreeSpectrum6864.graph DegreeTwoThreeSpectrum5666.graph
    sourceMap2707swap fusedMap2707swap sourceMap2707swap_checked fusedMap2707swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2707
#print axioms sourceMap2707swap_checked
#print axioms fusedMap2707swap_checked
#print axioms certified2707swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
