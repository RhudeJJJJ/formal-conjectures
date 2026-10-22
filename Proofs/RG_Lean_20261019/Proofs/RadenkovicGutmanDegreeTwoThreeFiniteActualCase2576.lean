/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2576 : Family 10 := level10.get ⟨461,by decide⟩
def sourceMap2576 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2576 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2576_checked : acceptsGraphIso
    (source (graph core2576) (root 10) 0 4) DegreeTwoThreeSpectrum5898.graph sourceMap2576=true := by decide +kernel
theorem fusedMap2576_checked : acceptsGraphIso
    (fused (graph core2576) (root 10) 0 4) DegreeTwoThreeSpectrum5900.graph fusedMap2576=true := by decide +kernel
theorem certified2576 : Certified (graph core2576) (root 10) 0 4 :=
  of_native_maps core2576 DegreeTwoThreeSpectrum5898.graph DegreeTwoThreeSpectrum5900.graph
    sourceMap2576 fusedMap2576 sourceMap2576_checked fusedMap2576_checked
    DegreeTwoThreeFiniteComparisons.comparison2576
#print axioms sourceMap2576_checked
#print axioms fusedMap2576_checked
#print axioms certified2576
def sourceMap2576swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2576swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2576swap_checked : acceptsGraphIso
    (source (graph core2576) (root 10) 4 0) DegreeTwoThreeSpectrum5898.graph sourceMap2576swap=true := by decide +kernel
theorem fusedMap2576swap_checked : acceptsGraphIso
    (fused (graph core2576) (root 10) 4 0) DegreeTwoThreeSpectrum5900.graph fusedMap2576swap=true := by decide +kernel
theorem certified2576swap : Certified (graph core2576) (root 10) 4 0 :=
  of_native_maps core2576 DegreeTwoThreeSpectrum5898.graph DegreeTwoThreeSpectrum5900.graph
    sourceMap2576swap fusedMap2576swap sourceMap2576swap_checked fusedMap2576swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2576
#print axioms sourceMap2576swap_checked
#print axioms fusedMap2576swap_checked
#print axioms certified2576swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
