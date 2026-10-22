/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2886 : Family 10 := level10.get ⟨1285,by decide⟩
def sourceMap2886 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2886 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2886_checked : acceptsGraphIso
    (source (graph core2886) (root 10) 0 4) DegreeTwoThreeSpectrum6554.graph sourceMap2886=true := by decide +kernel
theorem fusedMap2886_checked : acceptsGraphIso
    (fused (graph core2886) (root 10) 0 4) DegreeTwoThreeSpectrum6555.graph fusedMap2886=true := by decide +kernel
theorem certified2886 : Certified (graph core2886) (root 10) 0 4 :=
  of_native_maps core2886 DegreeTwoThreeSpectrum6554.graph DegreeTwoThreeSpectrum6555.graph
    sourceMap2886 fusedMap2886 sourceMap2886_checked fusedMap2886_checked
    DegreeTwoThreeFiniteComparisons.comparison2886
#print axioms sourceMap2886_checked
#print axioms fusedMap2886_checked
#print axioms certified2886
def sourceMap2886swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2886swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2886swap_checked : acceptsGraphIso
    (source (graph core2886) (root 10) 4 0) DegreeTwoThreeSpectrum6554.graph sourceMap2886swap=true := by decide +kernel
theorem fusedMap2886swap_checked : acceptsGraphIso
    (fused (graph core2886) (root 10) 4 0) DegreeTwoThreeSpectrum6555.graph fusedMap2886swap=true := by decide +kernel
theorem certified2886swap : Certified (graph core2886) (root 10) 4 0 :=
  of_native_maps core2886 DegreeTwoThreeSpectrum6554.graph DegreeTwoThreeSpectrum6555.graph
    sourceMap2886swap fusedMap2886swap sourceMap2886swap_checked fusedMap2886swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2886
#print axioms sourceMap2886swap_checked
#print axioms fusedMap2886swap_checked
#print axioms certified2886swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
