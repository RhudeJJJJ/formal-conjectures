/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1934 : Family 10 := level10.get ⟨1450,by decide⟩
def sourceMap1934 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1934 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1934_checked : acceptsGraphIso
    (source (graph core1934) (root 10) 0 2) DegreeTwoThreeSpectrum3295.graph sourceMap1934=true := by decide +kernel
theorem fusedMap1934_checked : acceptsGraphIso
    (fused (graph core1934) (root 10) 0 2) DegreeTwoThreeSpectrum3690.graph fusedMap1934=true := by decide +kernel
theorem certified1934 : Certified (graph core1934) (root 10) 0 2 :=
  of_native_maps core1934 DegreeTwoThreeSpectrum3295.graph DegreeTwoThreeSpectrum3690.graph
    sourceMap1934 fusedMap1934 sourceMap1934_checked fusedMap1934_checked
    DegreeTwoThreeFiniteComparisons.comparison1934
#print axioms sourceMap1934_checked
#print axioms fusedMap1934_checked
#print axioms certified1934
def sourceMap1934swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1934swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1934swap_checked : acceptsGraphIso
    (source (graph core1934) (root 10) 2 0) DegreeTwoThreeSpectrum3295.graph sourceMap1934swap=true := by decide +kernel
theorem fusedMap1934swap_checked : acceptsGraphIso
    (fused (graph core1934) (root 10) 2 0) DegreeTwoThreeSpectrum3690.graph fusedMap1934swap=true := by decide +kernel
theorem certified1934swap : Certified (graph core1934) (root 10) 2 0 :=
  of_native_maps core1934 DegreeTwoThreeSpectrum3295.graph DegreeTwoThreeSpectrum3690.graph
    sourceMap1934swap fusedMap1934swap sourceMap1934swap_checked fusedMap1934swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1934
#print axioms sourceMap1934swap_checked
#print axioms fusedMap1934swap_checked
#print axioms certified1934swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
