/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons55
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2788 : Family 10 := level10.get ⟨1047,by decide⟩
def sourceMap2788 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2788 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2788_checked : acceptsGraphIso
    (source (graph core2788) (root 10) 0 4) DegreeTwoThreeSpectrum6077.graph sourceMap2788=true := by decide +kernel
theorem fusedMap2788_checked : acceptsGraphIso
    (fused (graph core2788) (root 10) 0 4) DegreeTwoThreeSpectrum6078.graph fusedMap2788=true := by decide +kernel
theorem certified2788 : Certified (graph core2788) (root 10) 0 4 :=
  of_native_maps core2788 DegreeTwoThreeSpectrum6077.graph DegreeTwoThreeSpectrum6078.graph
    sourceMap2788 fusedMap2788 sourceMap2788_checked fusedMap2788_checked
    DegreeTwoThreeFiniteComparisons.comparison2788
#print axioms sourceMap2788_checked
#print axioms fusedMap2788_checked
#print axioms certified2788
def sourceMap2788swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2788swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2788swap_checked : acceptsGraphIso
    (source (graph core2788) (root 10) 4 0) DegreeTwoThreeSpectrum6077.graph sourceMap2788swap=true := by decide +kernel
theorem fusedMap2788swap_checked : acceptsGraphIso
    (fused (graph core2788) (root 10) 4 0) DegreeTwoThreeSpectrum6078.graph fusedMap2788swap=true := by decide +kernel
theorem certified2788swap : Certified (graph core2788) (root 10) 4 0 :=
  of_native_maps core2788 DegreeTwoThreeSpectrum6077.graph DegreeTwoThreeSpectrum6078.graph
    sourceMap2788swap fusedMap2788swap sourceMap2788swap_checked fusedMap2788swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2788
#print axioms sourceMap2788swap_checked
#print axioms fusedMap2788swap_checked
#print axioms certified2788swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
