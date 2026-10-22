/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2309 : Family 9 := level9.get ⟨312,by decide⟩
def sourceMap2309 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,6,7,8,9,10] (sourceLabel 9 0 4 v)
def fusedMap2309 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2309_checked : acceptsGraphIso
    (source (graph core2309) (root 9) 0 4) DegreeTwoThreeSpectrum4662.graph sourceMap2309=true := by decide +kernel
theorem fusedMap2309_checked : acceptsGraphIso
    (fused (graph core2309) (root 9) 0 4) DegreeTwoThreeSpectrum4155.graph fusedMap2309=true := by decide +kernel
theorem certified2309 : Certified (graph core2309) (root 9) 0 4 :=
  of_native_maps core2309 DegreeTwoThreeSpectrum4662.graph DegreeTwoThreeSpectrum4155.graph
    sourceMap2309 fusedMap2309 sourceMap2309_checked fusedMap2309_checked
    DegreeTwoThreeFiniteComparisons.comparison2309
#print axioms sourceMap2309_checked
#print axioms fusedMap2309_checked
#print axioms certified2309
def sourceMap2309swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,6,7,8,9,10,15] (sourceLabel 9 4 0 v)
def fusedMap2309swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2309swap_checked : acceptsGraphIso
    (source (graph core2309) (root 9) 4 0) DegreeTwoThreeSpectrum4662.graph sourceMap2309swap=true := by decide +kernel
theorem fusedMap2309swap_checked : acceptsGraphIso
    (fused (graph core2309) (root 9) 4 0) DegreeTwoThreeSpectrum4155.graph fusedMap2309swap=true := by decide +kernel
theorem certified2309swap : Certified (graph core2309) (root 9) 4 0 :=
  of_native_maps core2309 DegreeTwoThreeSpectrum4662.graph DegreeTwoThreeSpectrum4155.graph
    sourceMap2309swap fusedMap2309swap sourceMap2309swap_checked fusedMap2309swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2309
#print axioms sourceMap2309swap_checked
#print axioms fusedMap2309swap_checked
#print axioms certified2309swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
