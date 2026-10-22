/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2733 : Family 10 := level10.get ⟨909,by decide⟩
def sourceMap2733 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2733 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2733_checked : acceptsGraphIso
    (source (graph core2733) (root 10) 0 4) DegreeTwoThreeSpectrum6983.graph sourceMap2733=true := by decide +kernel
theorem fusedMap2733_checked : acceptsGraphIso
    (fused (graph core2733) (root 10) 0 4) DegreeTwoThreeSpectrum5777.graph fusedMap2733=true := by decide +kernel
theorem certified2733 : Certified (graph core2733) (root 10) 0 4 :=
  of_native_maps core2733 DegreeTwoThreeSpectrum6983.graph DegreeTwoThreeSpectrum5777.graph
    sourceMap2733 fusedMap2733 sourceMap2733_checked fusedMap2733_checked
    DegreeTwoThreeFiniteComparisons.comparison2733
#print axioms sourceMap2733_checked
#print axioms fusedMap2733_checked
#print axioms certified2733
def sourceMap2733swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2733swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2733swap_checked : acceptsGraphIso
    (source (graph core2733) (root 10) 4 0) DegreeTwoThreeSpectrum6983.graph sourceMap2733swap=true := by decide +kernel
theorem fusedMap2733swap_checked : acceptsGraphIso
    (fused (graph core2733) (root 10) 4 0) DegreeTwoThreeSpectrum5777.graph fusedMap2733swap=true := by decide +kernel
theorem certified2733swap : Certified (graph core2733) (root 10) 4 0 :=
  of_native_maps core2733 DegreeTwoThreeSpectrum6983.graph DegreeTwoThreeSpectrum5777.graph
    sourceMap2733swap fusedMap2733swap sourceMap2733swap_checked fusedMap2733swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2733
#print axioms sourceMap2733swap_checked
#print axioms fusedMap2733swap_checked
#print axioms certified2733swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
