/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2890 : Family 10 := level10.get ⟨1292,by decide⟩
def sourceMap2890 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2890 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2890_checked : acceptsGraphIso
    (source (graph core2890) (root 10) 0 4) DegreeTwoThreeSpectrum6568.graph sourceMap2890=true := by decide +kernel
theorem fusedMap2890_checked : acceptsGraphIso
    (fused (graph core2890) (root 10) 0 4) DegreeTwoThreeSpectrum6569.graph fusedMap2890=true := by decide +kernel
theorem certified2890 : Certified (graph core2890) (root 10) 0 4 :=
  of_native_maps core2890 DegreeTwoThreeSpectrum6568.graph DegreeTwoThreeSpectrum6569.graph
    sourceMap2890 fusedMap2890 sourceMap2890_checked fusedMap2890_checked
    DegreeTwoThreeFiniteComparisons.comparison2890
#print axioms sourceMap2890_checked
#print axioms fusedMap2890_checked
#print axioms certified2890
def sourceMap2890swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2890swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2890swap_checked : acceptsGraphIso
    (source (graph core2890) (root 10) 4 0) DegreeTwoThreeSpectrum6568.graph sourceMap2890swap=true := by decide +kernel
theorem fusedMap2890swap_checked : acceptsGraphIso
    (fused (graph core2890) (root 10) 4 0) DegreeTwoThreeSpectrum6569.graph fusedMap2890swap=true := by decide +kernel
theorem certified2890swap : Certified (graph core2890) (root 10) 4 0 :=
  of_native_maps core2890 DegreeTwoThreeSpectrum6568.graph DegreeTwoThreeSpectrum6569.graph
    sourceMap2890swap fusedMap2890swap sourceMap2890swap_checked fusedMap2890swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2890
#print axioms sourceMap2890swap_checked
#print axioms fusedMap2890swap_checked
#print axioms certified2890swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
