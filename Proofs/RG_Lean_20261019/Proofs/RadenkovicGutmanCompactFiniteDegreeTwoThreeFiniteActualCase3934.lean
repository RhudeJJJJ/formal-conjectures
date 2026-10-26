/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3934 : Family 6 := level6.get ⟨5,by decide⟩
def sourceMap3934 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,8,6,7,9,10,11,12,13,14] (sourceLabel 6 1 5 v)
def fusedMap3934 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13,14] (fusedLabel 6 1 5 v)
theorem sourceMap3934_checked : acceptsGraphIso
    (source (graph core3934) (root 6) 1 5) DegreeTwoThreeSpectrum2430.graph sourceMap3934=true := by decide +kernel
theorem fusedMap3934_checked : acceptsGraphIso
    (fused (graph core3934) (root 6) 1 5) DegreeTwoThreeSpectrum2313.graph fusedMap3934=true := by decide +kernel
theorem certified3934 : Certified (graph core3934) (root 6) 1 5 :=
  of_native_maps core3934 DegreeTwoThreeSpectrum2430.graph DegreeTwoThreeSpectrum2313.graph
    sourceMap3934 fusedMap3934 sourceMap3934_checked fusedMap3934_checked
    DegreeTwoThreeFiniteComparisons.comparison3934
#print axioms sourceMap3934_checked
#print axioms fusedMap3934_checked
#print axioms certified3934
def sourceMap3934swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,8,9,10,11,12,13,14,6,7] (sourceLabel 6 5 1 v)
def fusedMap3934swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13,14] (fusedLabel 6 5 1 v)
theorem sourceMap3934swap_checked : acceptsGraphIso
    (source (graph core3934) (root 6) 5 1) DegreeTwoThreeSpectrum2430.graph sourceMap3934swap=true := by decide +kernel
theorem fusedMap3934swap_checked : acceptsGraphIso
    (fused (graph core3934) (root 6) 5 1) DegreeTwoThreeSpectrum2313.graph fusedMap3934swap=true := by decide +kernel
theorem certified3934swap : Certified (graph core3934) (root 6) 5 1 :=
  of_native_maps core3934 DegreeTwoThreeSpectrum2430.graph DegreeTwoThreeSpectrum2313.graph
    sourceMap3934swap fusedMap3934swap sourceMap3934swap_checked fusedMap3934swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3934
#print axioms sourceMap3934swap_checked
#print axioms fusedMap3934swap_checked
#print axioms certified3934swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
