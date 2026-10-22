/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2222 : Family 9 := level9.get ⟨41,by decide⟩
def sourceMap2222 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,0,10,11,12,13,14,15,7,8,9,2,3,4,5,6] (sourceLabel 9 0 4 v)
def fusedMap2222 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,9,10,11,12,13,14,15,7,8,1,2,3,4,5,6] (fusedLabel 9 0 4 v)
theorem sourceMap2222_checked : acceptsGraphIso
    (source (graph core2222) (root 9) 0 4) DegreeTwoThreeSpectrum4160.graph sourceMap2222=true := by decide +kernel
theorem fusedMap2222_checked : acceptsGraphIso
    (fused (graph core2222) (root 9) 0 4) DegreeTwoThreeSpectrum3888.graph fusedMap2222=true := by decide +kernel
theorem certified2222 : Certified (graph core2222) (root 9) 0 4 :=
  of_native_maps core2222 DegreeTwoThreeSpectrum4160.graph DegreeTwoThreeSpectrum3888.graph
    sourceMap2222 fusedMap2222 sourceMap2222_checked fusedMap2222_checked
    DegreeTwoThreeFiniteComparisons.comparison2222
#print axioms sourceMap2222_checked
#print axioms fusedMap2222_checked
#print axioms certified2222
def sourceMap2222swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,0,10,11,12,13,14,15,7,8,2,3,4,5,6,9] (sourceLabel 9 4 0 v)
def fusedMap2222swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,9,10,11,12,13,14,15,7,8,1,2,3,4,5,6] (fusedLabel 9 4 0 v)
theorem sourceMap2222swap_checked : acceptsGraphIso
    (source (graph core2222) (root 9) 4 0) DegreeTwoThreeSpectrum4160.graph sourceMap2222swap=true := by decide +kernel
theorem fusedMap2222swap_checked : acceptsGraphIso
    (fused (graph core2222) (root 9) 4 0) DegreeTwoThreeSpectrum3888.graph fusedMap2222swap=true := by decide +kernel
theorem certified2222swap : Certified (graph core2222) (root 9) 4 0 :=
  of_native_maps core2222 DegreeTwoThreeSpectrum4160.graph DegreeTwoThreeSpectrum3888.graph
    sourceMap2222swap fusedMap2222swap sourceMap2222swap_checked fusedMap2222swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2222
#print axioms sourceMap2222swap_checked
#print axioms fusedMap2222swap_checked
#print axioms certified2222swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
