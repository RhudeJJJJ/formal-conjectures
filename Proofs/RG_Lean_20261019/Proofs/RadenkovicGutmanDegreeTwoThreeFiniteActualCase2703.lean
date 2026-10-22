/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2703 : Family 10 := level10.get ⟨823,by decide⟩
def sourceMap2703 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,16,7,8,9,10,11] (sourceLabel 10 0 4 v)
def fusedMap2703 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2703_checked : acceptsGraphIso
    (source (graph core2703) (root 10) 0 4) DegreeTwoThreeSpectrum6792.graph sourceMap2703=true := by decide +kernel
theorem fusedMap2703_checked : acceptsGraphIso
    (fused (graph core2703) (root 10) 0 4) DegreeTwoThreeSpectrum5632.graph fusedMap2703=true := by decide +kernel
theorem certified2703 : Certified (graph core2703) (root 10) 0 4 :=
  of_native_maps core2703 DegreeTwoThreeSpectrum6792.graph DegreeTwoThreeSpectrum5632.graph
    sourceMap2703 fusedMap2703 sourceMap2703_checked fusedMap2703_checked
    DegreeTwoThreeFiniteComparisons.comparison2703
#print axioms sourceMap2703_checked
#print axioms fusedMap2703_checked
#print axioms certified2703
def sourceMap2703swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11,16] (sourceLabel 10 4 0 v)
def fusedMap2703swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2703swap_checked : acceptsGraphIso
    (source (graph core2703) (root 10) 4 0) DegreeTwoThreeSpectrum6792.graph sourceMap2703swap=true := by decide +kernel
theorem fusedMap2703swap_checked : acceptsGraphIso
    (fused (graph core2703) (root 10) 4 0) DegreeTwoThreeSpectrum5632.graph fusedMap2703swap=true := by decide +kernel
theorem certified2703swap : Certified (graph core2703) (root 10) 4 0 :=
  of_native_maps core2703 DegreeTwoThreeSpectrum6792.graph DegreeTwoThreeSpectrum5632.graph
    sourceMap2703swap fusedMap2703swap sourceMap2703swap_checked fusedMap2703swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2703
#print axioms sourceMap2703swap_checked
#print axioms fusedMap2703swap_checked
#print axioms certified2703swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
