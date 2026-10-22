/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2615 : Family 10 := level10.get ⟨580,by decide⟩
def sourceMap2615 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2615 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2615_checked : acceptsGraphIso
    (source (graph core2615) (root 10) 0 4) DegreeTwoThreeSpectrum6253.graph sourceMap2615=true := by decide +kernel
theorem fusedMap2615_checked : acceptsGraphIso
    (fused (graph core2615) (root 10) 0 4) DegreeTwoThreeSpectrum5249.graph fusedMap2615=true := by decide +kernel
theorem certified2615 : Certified (graph core2615) (root 10) 0 4 :=
  of_native_maps core2615 DegreeTwoThreeSpectrum6253.graph DegreeTwoThreeSpectrum5249.graph
    sourceMap2615 fusedMap2615 sourceMap2615_checked fusedMap2615_checked
    DegreeTwoThreeFiniteComparisons.comparison2615
#print axioms sourceMap2615_checked
#print axioms fusedMap2615_checked
#print axioms certified2615
def sourceMap2615swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2615swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2615swap_checked : acceptsGraphIso
    (source (graph core2615) (root 10) 4 0) DegreeTwoThreeSpectrum6253.graph sourceMap2615swap=true := by decide +kernel
theorem fusedMap2615swap_checked : acceptsGraphIso
    (fused (graph core2615) (root 10) 4 0) DegreeTwoThreeSpectrum5249.graph fusedMap2615swap=true := by decide +kernel
theorem certified2615swap : Certified (graph core2615) (root 10) 4 0 :=
  of_native_maps core2615 DegreeTwoThreeSpectrum6253.graph DegreeTwoThreeSpectrum5249.graph
    sourceMap2615swap fusedMap2615swap sourceMap2615swap_checked fusedMap2615swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2615
#print axioms sourceMap2615swap_checked
#print axioms fusedMap2615swap_checked
#print axioms certified2615swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
