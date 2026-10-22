/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2751 : Family 10 := level10.get ⟨952,by decide⟩
def sourceMap2751 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2751 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2751_checked : acceptsGraphIso
    (source (graph core2751) (root 10) 0 4) DegreeTwoThreeSpectrum7029.graph sourceMap2751=true := by decide +kernel
theorem fusedMap2751_checked : acceptsGraphIso
    (fused (graph core2751) (root 10) 0 4) DegreeTwoThreeSpectrum5852.graph fusedMap2751=true := by decide +kernel
theorem certified2751 : Certified (graph core2751) (root 10) 0 4 :=
  of_native_maps core2751 DegreeTwoThreeSpectrum7029.graph DegreeTwoThreeSpectrum5852.graph
    sourceMap2751 fusedMap2751 sourceMap2751_checked fusedMap2751_checked
    DegreeTwoThreeFiniteComparisons.comparison2751
#print axioms sourceMap2751_checked
#print axioms fusedMap2751_checked
#print axioms certified2751
def sourceMap2751swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2751swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2751swap_checked : acceptsGraphIso
    (source (graph core2751) (root 10) 4 0) DegreeTwoThreeSpectrum7029.graph sourceMap2751swap=true := by decide +kernel
theorem fusedMap2751swap_checked : acceptsGraphIso
    (fused (graph core2751) (root 10) 4 0) DegreeTwoThreeSpectrum5852.graph fusedMap2751swap=true := by decide +kernel
theorem certified2751swap : Certified (graph core2751) (root 10) 4 0 :=
  of_native_maps core2751 DegreeTwoThreeSpectrum7029.graph DegreeTwoThreeSpectrum5852.graph
    sourceMap2751swap fusedMap2751swap sourceMap2751swap_checked fusedMap2751swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2751
#print axioms sourceMap2751swap_checked
#print axioms fusedMap2751swap_checked
#print axioms certified2751swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
