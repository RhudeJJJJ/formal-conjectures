/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2934 : Family 10 := level10.get ⟨1393,by decide⟩
def sourceMap2934 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2934 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2934_checked : acceptsGraphIso
    (source (graph core2934) (root 10) 0 4) DegreeTwoThreeSpectrum6757.graph sourceMap2934=true := by decide +kernel
theorem fusedMap2934_checked : acceptsGraphIso
    (fused (graph core2934) (root 10) 0 4) DegreeTwoThreeSpectrum6758.graph fusedMap2934=true := by decide +kernel
theorem certified2934 : Certified (graph core2934) (root 10) 0 4 :=
  of_native_maps core2934 DegreeTwoThreeSpectrum6757.graph DegreeTwoThreeSpectrum6758.graph
    sourceMap2934 fusedMap2934 sourceMap2934_checked fusedMap2934_checked
    DegreeTwoThreeFiniteComparisons.comparison2934
#print axioms sourceMap2934_checked
#print axioms fusedMap2934_checked
#print axioms certified2934
def sourceMap2934swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2934swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2934swap_checked : acceptsGraphIso
    (source (graph core2934) (root 10) 4 0) DegreeTwoThreeSpectrum6757.graph sourceMap2934swap=true := by decide +kernel
theorem fusedMap2934swap_checked : acceptsGraphIso
    (fused (graph core2934) (root 10) 4 0) DegreeTwoThreeSpectrum6758.graph fusedMap2934swap=true := by decide +kernel
theorem certified2934swap : Certified (graph core2934) (root 10) 4 0 :=
  of_native_maps core2934 DegreeTwoThreeSpectrum6757.graph DegreeTwoThreeSpectrum6758.graph
    sourceMap2934swap fusedMap2934swap sourceMap2934swap_checked fusedMap2934swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2934
#print axioms sourceMap2934swap_checked
#print axioms fusedMap2934swap_checked
#print axioms certified2934swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
