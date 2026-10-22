/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2721 : Family 10 := level10.get ⟨877,by decide⟩
def sourceMap2721 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2721 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2721_checked : acceptsGraphIso
    (source (graph core2721) (root 10) 0 4) DegreeTwoThreeSpectrum6936.graph sourceMap2721=true := by decide +kernel
theorem fusedMap2721_checked : acceptsGraphIso
    (fused (graph core2721) (root 10) 0 4) DegreeTwoThreeSpectrum5727.graph fusedMap2721=true := by decide +kernel
theorem certified2721 : Certified (graph core2721) (root 10) 0 4 :=
  of_native_maps core2721 DegreeTwoThreeSpectrum6936.graph DegreeTwoThreeSpectrum5727.graph
    sourceMap2721 fusedMap2721 sourceMap2721_checked fusedMap2721_checked
    DegreeTwoThreeFiniteComparisons.comparison2721
#print axioms sourceMap2721_checked
#print axioms fusedMap2721_checked
#print axioms certified2721
def sourceMap2721swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2721swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2721swap_checked : acceptsGraphIso
    (source (graph core2721) (root 10) 4 0) DegreeTwoThreeSpectrum6936.graph sourceMap2721swap=true := by decide +kernel
theorem fusedMap2721swap_checked : acceptsGraphIso
    (fused (graph core2721) (root 10) 4 0) DegreeTwoThreeSpectrum5727.graph fusedMap2721swap=true := by decide +kernel
theorem certified2721swap : Certified (graph core2721) (root 10) 4 0 :=
  of_native_maps core2721 DegreeTwoThreeSpectrum6936.graph DegreeTwoThreeSpectrum5727.graph
    sourceMap2721swap fusedMap2721swap sourceMap2721swap_checked fusedMap2721swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2721
#print axioms sourceMap2721swap_checked
#print axioms fusedMap2721swap_checked
#print axioms certified2721swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
