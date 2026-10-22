/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2966 : Family 10 := level10.get ⟨1468,by decide⟩
def sourceMap2966 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2966 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2966_checked : acceptsGraphIso
    (source (graph core2966) (root 10) 0 4) DegreeTwoThreeSpectrum6948.graph sourceMap2966=true := by decide +kernel
theorem fusedMap2966_checked : acceptsGraphIso
    (fused (graph core2966) (root 10) 0 4) DegreeTwoThreeSpectrum6949.graph fusedMap2966=true := by decide +kernel
theorem certified2966 : Certified (graph core2966) (root 10) 0 4 :=
  of_native_maps core2966 DegreeTwoThreeSpectrum6948.graph DegreeTwoThreeSpectrum6949.graph
    sourceMap2966 fusedMap2966 sourceMap2966_checked fusedMap2966_checked
    DegreeTwoThreeFiniteComparisons.comparison2966
#print axioms sourceMap2966_checked
#print axioms fusedMap2966_checked
#print axioms certified2966
def sourceMap2966swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2966swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2966swap_checked : acceptsGraphIso
    (source (graph core2966) (root 10) 4 0) DegreeTwoThreeSpectrum6948.graph sourceMap2966swap=true := by decide +kernel
theorem fusedMap2966swap_checked : acceptsGraphIso
    (fused (graph core2966) (root 10) 4 0) DegreeTwoThreeSpectrum6949.graph fusedMap2966swap=true := by decide +kernel
theorem certified2966swap : Certified (graph core2966) (root 10) 4 0 :=
  of_native_maps core2966 DegreeTwoThreeSpectrum6948.graph DegreeTwoThreeSpectrum6949.graph
    sourceMap2966swap fusedMap2966swap sourceMap2966swap_checked fusedMap2966swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2966
#print axioms sourceMap2966swap_checked
#print axioms fusedMap2966swap_checked
#print axioms certified2966swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
