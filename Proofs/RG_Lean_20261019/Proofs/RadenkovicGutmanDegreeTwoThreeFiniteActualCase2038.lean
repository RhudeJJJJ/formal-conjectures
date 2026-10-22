/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2038 : Family 10 := level10.get ⟨1737,by decide⟩
def sourceMap2038 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap2038 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2038_checked : acceptsGraphIso
    (source (graph core2038) (root 10) 0 2) DegreeTwoThreeSpectrum3835.graph sourceMap2038=true := by decide +kernel
theorem fusedMap2038_checked : acceptsGraphIso
    (fused (graph core2038) (root 10) 0 2) DegreeTwoThreeSpectrum3459.graph fusedMap2038=true := by decide +kernel
theorem certified2038 : Certified (graph core2038) (root 10) 0 2 :=
  of_native_maps core2038 DegreeTwoThreeSpectrum3835.graph DegreeTwoThreeSpectrum3459.graph
    sourceMap2038 fusedMap2038 sourceMap2038_checked fusedMap2038_checked
    DegreeTwoThreeFiniteComparisons.comparison2038
#print axioms sourceMap2038_checked
#print axioms fusedMap2038_checked
#print axioms certified2038
def sourceMap2038swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap2038swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2038swap_checked : acceptsGraphIso
    (source (graph core2038) (root 10) 2 0) DegreeTwoThreeSpectrum3835.graph sourceMap2038swap=true := by decide +kernel
theorem fusedMap2038swap_checked : acceptsGraphIso
    (fused (graph core2038) (root 10) 2 0) DegreeTwoThreeSpectrum3459.graph fusedMap2038swap=true := by decide +kernel
theorem certified2038swap : Certified (graph core2038) (root 10) 2 0 :=
  of_native_maps core2038 DegreeTwoThreeSpectrum3835.graph DegreeTwoThreeSpectrum3459.graph
    sourceMap2038swap fusedMap2038swap sourceMap2038swap_checked fusedMap2038swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2038
#print axioms sourceMap2038swap_checked
#print axioms fusedMap2038swap_checked
#print axioms certified2038swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
