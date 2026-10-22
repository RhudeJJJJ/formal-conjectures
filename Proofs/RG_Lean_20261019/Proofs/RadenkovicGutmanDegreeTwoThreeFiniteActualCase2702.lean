/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2702 : Family 10 := level10.get ⟨822,by decide⟩
def sourceMap2702 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,16,7,8,9,10,11] (sourceLabel 10 0 4 v)
def fusedMap2702 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2702_checked : acceptsGraphIso
    (source (graph core2702) (root 10) 0 4) DegreeTwoThreeSpectrum6791.graph sourceMap2702=true := by decide +kernel
theorem fusedMap2702_checked : acceptsGraphIso
    (fused (graph core2702) (root 10) 0 4) DegreeTwoThreeSpectrum5631.graph fusedMap2702=true := by decide +kernel
theorem certified2702 : Certified (graph core2702) (root 10) 0 4 :=
  of_native_maps core2702 DegreeTwoThreeSpectrum6791.graph DegreeTwoThreeSpectrum5631.graph
    sourceMap2702 fusedMap2702 sourceMap2702_checked fusedMap2702_checked
    DegreeTwoThreeFiniteComparisons.comparison2702
#print axioms sourceMap2702_checked
#print axioms fusedMap2702_checked
#print axioms certified2702
def sourceMap2702swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11,16] (sourceLabel 10 4 0 v)
def fusedMap2702swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2702swap_checked : acceptsGraphIso
    (source (graph core2702) (root 10) 4 0) DegreeTwoThreeSpectrum6791.graph sourceMap2702swap=true := by decide +kernel
theorem fusedMap2702swap_checked : acceptsGraphIso
    (fused (graph core2702) (root 10) 4 0) DegreeTwoThreeSpectrum5631.graph fusedMap2702swap=true := by decide +kernel
theorem certified2702swap : Certified (graph core2702) (root 10) 4 0 :=
  of_native_maps core2702 DegreeTwoThreeSpectrum6791.graph DegreeTwoThreeSpectrum5631.graph
    sourceMap2702swap fusedMap2702swap sourceMap2702swap_checked fusedMap2702swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2702
#print axioms sourceMap2702swap_checked
#print axioms fusedMap2702swap_checked
#print axioms certified2702swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
