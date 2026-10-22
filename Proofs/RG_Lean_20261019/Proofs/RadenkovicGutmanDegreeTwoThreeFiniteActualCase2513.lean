/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2513 : Family 10 := level10.get ⟨257,by decide⟩
def sourceMap2513 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2513 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2513_checked : acceptsGraphIso
    (source (graph core2513) (root 10) 0 4) DegreeTwoThreeSpectrum5358.graph sourceMap2513=true := by decide +kernel
theorem fusedMap2513_checked : acceptsGraphIso
    (fused (graph core2513) (root 10) 0 4) DegreeTwoThreeSpectrum5360.graph fusedMap2513=true := by decide +kernel
theorem certified2513 : Certified (graph core2513) (root 10) 0 4 :=
  of_native_maps core2513 DegreeTwoThreeSpectrum5358.graph DegreeTwoThreeSpectrum5360.graph
    sourceMap2513 fusedMap2513 sourceMap2513_checked fusedMap2513_checked
    DegreeTwoThreeFiniteComparisons.comparison2513
#print axioms sourceMap2513_checked
#print axioms fusedMap2513_checked
#print axioms certified2513
def sourceMap2513swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2513swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2513swap_checked : acceptsGraphIso
    (source (graph core2513) (root 10) 4 0) DegreeTwoThreeSpectrum5358.graph sourceMap2513swap=true := by decide +kernel
theorem fusedMap2513swap_checked : acceptsGraphIso
    (fused (graph core2513) (root 10) 4 0) DegreeTwoThreeSpectrum5360.graph fusedMap2513swap=true := by decide +kernel
theorem certified2513swap : Certified (graph core2513) (root 10) 4 0 :=
  of_native_maps core2513 DegreeTwoThreeSpectrum5358.graph DegreeTwoThreeSpectrum5360.graph
    sourceMap2513swap fusedMap2513swap sourceMap2513swap_checked fusedMap2513swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2513
#print axioms sourceMap2513swap_checked
#print axioms fusedMap2513swap_checked
#print axioms certified2513swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
