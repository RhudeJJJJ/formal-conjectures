/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2727 : Family 10 := level10.get ⟨891,by decide⟩
def sourceMap2727 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2727 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2727_checked : acceptsGraphIso
    (source (graph core2727) (root 10) 0 4) DegreeTwoThreeSpectrum6958.graph sourceMap2727=true := by decide +kernel
theorem fusedMap2727_checked : acceptsGraphIso
    (fused (graph core2727) (root 10) 0 4) DegreeTwoThreeSpectrum5749.graph fusedMap2727=true := by decide +kernel
theorem certified2727 : Certified (graph core2727) (root 10) 0 4 :=
  of_native_maps core2727 DegreeTwoThreeSpectrum6958.graph DegreeTwoThreeSpectrum5749.graph
    sourceMap2727 fusedMap2727 sourceMap2727_checked fusedMap2727_checked
    DegreeTwoThreeFiniteComparisons.comparison2727
#print axioms sourceMap2727_checked
#print axioms fusedMap2727_checked
#print axioms certified2727
def sourceMap2727swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2727swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2727swap_checked : acceptsGraphIso
    (source (graph core2727) (root 10) 4 0) DegreeTwoThreeSpectrum6958.graph sourceMap2727swap=true := by decide +kernel
theorem fusedMap2727swap_checked : acceptsGraphIso
    (fused (graph core2727) (root 10) 4 0) DegreeTwoThreeSpectrum5749.graph fusedMap2727swap=true := by decide +kernel
theorem certified2727swap : Certified (graph core2727) (root 10) 4 0 :=
  of_native_maps core2727 DegreeTwoThreeSpectrum6958.graph DegreeTwoThreeSpectrum5749.graph
    sourceMap2727swap fusedMap2727swap sourceMap2727swap_checked fusedMap2727swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2727
#print axioms sourceMap2727swap_checked
#print axioms fusedMap2727swap_checked
#print axioms certified2727swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
