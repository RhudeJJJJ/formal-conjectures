/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2032 : Family 10 := level10.get ⟨1714,by decide⟩
def sourceMap2032 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap2032 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2032_checked : acceptsGraphIso
    (source (graph core2032) (root 10) 0 2) DegreeTwoThreeSpectrum3826.graph sourceMap2032=true := by decide +kernel
theorem fusedMap2032_checked : acceptsGraphIso
    (fused (graph core2032) (root 10) 0 2) DegreeTwoThreeSpectrum3394.graph fusedMap2032=true := by decide +kernel
theorem certified2032 : Certified (graph core2032) (root 10) 0 2 :=
  of_native_maps core2032 DegreeTwoThreeSpectrum3826.graph DegreeTwoThreeSpectrum3394.graph
    sourceMap2032 fusedMap2032 sourceMap2032_checked fusedMap2032_checked
    DegreeTwoThreeFiniteComparisons.comparison2032
#print axioms sourceMap2032_checked
#print axioms fusedMap2032_checked
#print axioms certified2032
def sourceMap2032swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap2032swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2032swap_checked : acceptsGraphIso
    (source (graph core2032) (root 10) 2 0) DegreeTwoThreeSpectrum3826.graph sourceMap2032swap=true := by decide +kernel
theorem fusedMap2032swap_checked : acceptsGraphIso
    (fused (graph core2032) (root 10) 2 0) DegreeTwoThreeSpectrum3394.graph fusedMap2032swap=true := by decide +kernel
theorem certified2032swap : Certified (graph core2032) (root 10) 2 0 :=
  of_native_maps core2032 DegreeTwoThreeSpectrum3826.graph DegreeTwoThreeSpectrum3394.graph
    sourceMap2032swap fusedMap2032swap sourceMap2032swap_checked fusedMap2032swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2032
#print axioms sourceMap2032swap_checked
#print axioms fusedMap2032swap_checked
#print axioms certified2032swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
