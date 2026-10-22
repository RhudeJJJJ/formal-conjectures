/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2227 : Family 9 := level9.get ⟨66,by decide⟩
def sourceMap2227 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2227 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2227_checked : acceptsGraphIso
    (source (graph core2227) (root 9) 0 4) DegreeTwoThreeSpectrum3976.graph sourceMap2227=true := by decide +kernel
theorem fusedMap2227_checked : acceptsGraphIso
    (fused (graph core2227) (root 9) 0 4) DegreeTwoThreeSpectrum3977.graph fusedMap2227=true := by decide +kernel
theorem certified2227 : Certified (graph core2227) (root 9) 0 4 :=
  of_native_maps core2227 DegreeTwoThreeSpectrum3976.graph DegreeTwoThreeSpectrum3977.graph
    sourceMap2227 fusedMap2227 sourceMap2227_checked fusedMap2227_checked
    DegreeTwoThreeFiniteComparisons.comparison2227
#print axioms sourceMap2227_checked
#print axioms fusedMap2227_checked
#print axioms certified2227
def sourceMap2227swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2227swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2227swap_checked : acceptsGraphIso
    (source (graph core2227) (root 9) 4 0) DegreeTwoThreeSpectrum3976.graph sourceMap2227swap=true := by decide +kernel
theorem fusedMap2227swap_checked : acceptsGraphIso
    (fused (graph core2227) (root 9) 4 0) DegreeTwoThreeSpectrum3977.graph fusedMap2227swap=true := by decide +kernel
theorem certified2227swap : Certified (graph core2227) (root 9) 4 0 :=
  of_native_maps core2227 DegreeTwoThreeSpectrum3976.graph DegreeTwoThreeSpectrum3977.graph
    sourceMap2227swap fusedMap2227swap sourceMap2227swap_checked fusedMap2227swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2227
#print axioms sourceMap2227swap_checked
#print axioms fusedMap2227swap_checked
#print axioms certified2227swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
