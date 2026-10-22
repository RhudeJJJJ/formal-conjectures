/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2487 : Family 10 := level10.get ⟨162,by decide⟩
def sourceMap2487 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2487 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2487_checked : acceptsGraphIso
    (source (graph core2487) (root 10) 0 4) DegreeTwoThreeSpectrum5904.graph sourceMap2487=true := by decide +kernel
theorem fusedMap2487_checked : acceptsGraphIso
    (fused (graph core2487) (root 10) 0 4) DegreeTwoThreeSpectrum5102.graph fusedMap2487=true := by decide +kernel
theorem certified2487 : Certified (graph core2487) (root 10) 0 4 :=
  of_native_maps core2487 DegreeTwoThreeSpectrum5904.graph DegreeTwoThreeSpectrum5102.graph
    sourceMap2487 fusedMap2487 sourceMap2487_checked fusedMap2487_checked
    DegreeTwoThreeFiniteComparisons.comparison2487
#print axioms sourceMap2487_checked
#print axioms fusedMap2487_checked
#print axioms certified2487
def sourceMap2487swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2487swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2487swap_checked : acceptsGraphIso
    (source (graph core2487) (root 10) 4 0) DegreeTwoThreeSpectrum5904.graph sourceMap2487swap=true := by decide +kernel
theorem fusedMap2487swap_checked : acceptsGraphIso
    (fused (graph core2487) (root 10) 4 0) DegreeTwoThreeSpectrum5102.graph fusedMap2487swap=true := by decide +kernel
theorem certified2487swap : Certified (graph core2487) (root 10) 4 0 :=
  of_native_maps core2487 DegreeTwoThreeSpectrum5904.graph DegreeTwoThreeSpectrum5102.graph
    sourceMap2487swap fusedMap2487swap sourceMap2487swap_checked fusedMap2487swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2487
#print axioms sourceMap2487swap_checked
#print axioms fusedMap2487swap_checked
#print axioms certified2487swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
