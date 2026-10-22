/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2758 : Family 10 := level10.get ⟨966,by decide⟩
def sourceMap2758 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,16,7,8,9,10,11] (sourceLabel 10 0 4 v)
def fusedMap2758 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2758_checked : acceptsGraphIso
    (source (graph core2758) (root 10) 0 4) DegreeTwoThreeSpectrum7036.graph sourceMap2758=true := by decide +kernel
theorem fusedMap2758_checked : acceptsGraphIso
    (fused (graph core2758) (root 10) 0 4) DegreeTwoThreeSpectrum5885.graph fusedMap2758=true := by decide +kernel
theorem certified2758 : Certified (graph core2758) (root 10) 0 4 :=
  of_native_maps core2758 DegreeTwoThreeSpectrum7036.graph DegreeTwoThreeSpectrum5885.graph
    sourceMap2758 fusedMap2758 sourceMap2758_checked fusedMap2758_checked
    DegreeTwoThreeFiniteComparisons.comparison2758
#print axioms sourceMap2758_checked
#print axioms fusedMap2758_checked
#print axioms certified2758
def sourceMap2758swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11,16] (sourceLabel 10 4 0 v)
def fusedMap2758swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2758swap_checked : acceptsGraphIso
    (source (graph core2758) (root 10) 4 0) DegreeTwoThreeSpectrum7036.graph sourceMap2758swap=true := by decide +kernel
theorem fusedMap2758swap_checked : acceptsGraphIso
    (fused (graph core2758) (root 10) 4 0) DegreeTwoThreeSpectrum5885.graph fusedMap2758swap=true := by decide +kernel
theorem certified2758swap : Certified (graph core2758) (root 10) 4 0 :=
  of_native_maps core2758 DegreeTwoThreeSpectrum7036.graph DegreeTwoThreeSpectrum5885.graph
    sourceMap2758swap fusedMap2758swap sourceMap2758swap_checked fusedMap2758swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2758
#print axioms sourceMap2758swap_checked
#print axioms fusedMap2758swap_checked
#print axioms certified2758swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
