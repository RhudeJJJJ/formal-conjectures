/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2226 : Family 9 := level9.get ⟨63,by decide⟩
def sourceMap2226 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2226 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2226_checked : acceptsGraphIso
    (source (graph core2226) (root 9) 0 4) DegreeTwoThreeSpectrum3969.graph sourceMap2226=true := by decide +kernel
theorem fusedMap2226_checked : acceptsGraphIso
    (fused (graph core2226) (root 9) 0 4) DegreeTwoThreeSpectrum3970.graph fusedMap2226=true := by decide +kernel
theorem certified2226 : Certified (graph core2226) (root 9) 0 4 :=
  of_native_maps core2226 DegreeTwoThreeSpectrum3969.graph DegreeTwoThreeSpectrum3970.graph
    sourceMap2226 fusedMap2226 sourceMap2226_checked fusedMap2226_checked
    DegreeTwoThreeFiniteComparisons.comparison2226
#print axioms sourceMap2226_checked
#print axioms fusedMap2226_checked
#print axioms certified2226
def sourceMap2226swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2226swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2226swap_checked : acceptsGraphIso
    (source (graph core2226) (root 9) 4 0) DegreeTwoThreeSpectrum3969.graph sourceMap2226swap=true := by decide +kernel
theorem fusedMap2226swap_checked : acceptsGraphIso
    (fused (graph core2226) (root 9) 4 0) DegreeTwoThreeSpectrum3970.graph fusedMap2226swap=true := by decide +kernel
theorem certified2226swap : Certified (graph core2226) (root 9) 4 0 :=
  of_native_maps core2226 DegreeTwoThreeSpectrum3969.graph DegreeTwoThreeSpectrum3970.graph
    sourceMap2226swap fusedMap2226swap sourceMap2226swap_checked fusedMap2226swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2226
#print axioms sourceMap2226swap_checked
#print axioms fusedMap2226swap_checked
#print axioms certified2226swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
