/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2480 : Family 10 := level10.get ⟨139,by decide⟩
def sourceMap2480 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2480 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2480_checked : acceptsGraphIso
    (source (graph core2480) (root 10) 0 4) DegreeTwoThreeSpectrum5808.graph sourceMap2480=true := by decide +kernel
theorem fusedMap2480_checked : acceptsGraphIso
    (fused (graph core2480) (root 10) 0 4) DegreeTwoThreeSpectrum5070.graph fusedMap2480=true := by decide +kernel
theorem certified2480 : Certified (graph core2480) (root 10) 0 4 :=
  of_native_maps core2480 DegreeTwoThreeSpectrum5808.graph DegreeTwoThreeSpectrum5070.graph
    sourceMap2480 fusedMap2480 sourceMap2480_checked fusedMap2480_checked
    DegreeTwoThreeFiniteComparisons.comparison2480
#print axioms sourceMap2480_checked
#print axioms fusedMap2480_checked
#print axioms certified2480
def sourceMap2480swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2480swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2480swap_checked : acceptsGraphIso
    (source (graph core2480) (root 10) 4 0) DegreeTwoThreeSpectrum5808.graph sourceMap2480swap=true := by decide +kernel
theorem fusedMap2480swap_checked : acceptsGraphIso
    (fused (graph core2480) (root 10) 4 0) DegreeTwoThreeSpectrum5070.graph fusedMap2480swap=true := by decide +kernel
theorem certified2480swap : Certified (graph core2480) (root 10) 4 0 :=
  of_native_maps core2480 DegreeTwoThreeSpectrum5808.graph DegreeTwoThreeSpectrum5070.graph
    sourceMap2480swap fusedMap2480swap sourceMap2480swap_checked fusedMap2480swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2480
#print axioms sourceMap2480swap_checked
#print axioms fusedMap2480swap_checked
#print axioms certified2480swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
