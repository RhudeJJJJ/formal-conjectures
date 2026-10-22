/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2230 : Family 9 := level9.get ⟨78,by decide⟩
def sourceMap2230 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2230 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2230_checked : acceptsGraphIso
    (source (graph core2230) (root 9) 0 4) DegreeTwoThreeSpectrum4016.graph sourceMap2230=true := by decide +kernel
theorem fusedMap2230_checked : acceptsGraphIso
    (fused (graph core2230) (root 9) 0 4) DegreeTwoThreeSpectrum4017.graph fusedMap2230=true := by decide +kernel
theorem certified2230 : Certified (graph core2230) (root 9) 0 4 :=
  of_native_maps core2230 DegreeTwoThreeSpectrum4016.graph DegreeTwoThreeSpectrum4017.graph
    sourceMap2230 fusedMap2230 sourceMap2230_checked fusedMap2230_checked
    DegreeTwoThreeFiniteComparisons.comparison2230
#print axioms sourceMap2230_checked
#print axioms fusedMap2230_checked
#print axioms certified2230
def sourceMap2230swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2230swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2230swap_checked : acceptsGraphIso
    (source (graph core2230) (root 9) 4 0) DegreeTwoThreeSpectrum4016.graph sourceMap2230swap=true := by decide +kernel
theorem fusedMap2230swap_checked : acceptsGraphIso
    (fused (graph core2230) (root 9) 4 0) DegreeTwoThreeSpectrum4017.graph fusedMap2230swap=true := by decide +kernel
theorem certified2230swap : Certified (graph core2230) (root 9) 4 0 :=
  of_native_maps core2230 DegreeTwoThreeSpectrum4016.graph DegreeTwoThreeSpectrum4017.graph
    sourceMap2230swap fusedMap2230swap sourceMap2230swap_checked fusedMap2230swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2230
#print axioms sourceMap2230swap_checked
#print axioms fusedMap2230swap_checked
#print axioms certified2230swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
