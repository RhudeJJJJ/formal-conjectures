/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2236 : Family 9 := level9.get ⟨102,by decide⟩
def sourceMap2236 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2236 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2236_checked : acceptsGraphIso
    (source (graph core2236) (root 9) 0 4) DegreeTwoThreeSpectrum4090.graph sourceMap2236=true := by decide +kernel
theorem fusedMap2236_checked : acceptsGraphIso
    (fused (graph core2236) (root 9) 0 4) DegreeTwoThreeSpectrum4091.graph fusedMap2236=true := by decide +kernel
theorem certified2236 : Certified (graph core2236) (root 9) 0 4 :=
  of_native_maps core2236 DegreeTwoThreeSpectrum4090.graph DegreeTwoThreeSpectrum4091.graph
    sourceMap2236 fusedMap2236 sourceMap2236_checked fusedMap2236_checked
    DegreeTwoThreeFiniteComparisons.comparison2236
#print axioms sourceMap2236_checked
#print axioms fusedMap2236_checked
#print axioms certified2236
def sourceMap2236swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2236swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2236swap_checked : acceptsGraphIso
    (source (graph core2236) (root 9) 4 0) DegreeTwoThreeSpectrum4090.graph sourceMap2236swap=true := by decide +kernel
theorem fusedMap2236swap_checked : acceptsGraphIso
    (fused (graph core2236) (root 9) 4 0) DegreeTwoThreeSpectrum4091.graph fusedMap2236swap=true := by decide +kernel
theorem certified2236swap : Certified (graph core2236) (root 9) 4 0 :=
  of_native_maps core2236 DegreeTwoThreeSpectrum4090.graph DegreeTwoThreeSpectrum4091.graph
    sourceMap2236swap fusedMap2236swap sourceMap2236swap_checked fusedMap2236swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2236
#print axioms sourceMap2236swap_checked
#print axioms fusedMap2236swap_checked
#print axioms certified2236swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
