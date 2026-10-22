/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2505 : Family 10 := level10.get ⟨230,by decide⟩
def sourceMap2505 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2505 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2505_checked : acceptsGraphIso
    (source (graph core2505) (root 10) 0 4) DegreeTwoThreeSpectrum5280.graph sourceMap2505=true := by decide +kernel
theorem fusedMap2505_checked : acceptsGraphIso
    (fused (graph core2505) (root 10) 0 4) DegreeTwoThreeSpectrum5281.graph fusedMap2505=true := by decide +kernel
theorem certified2505 : Certified (graph core2505) (root 10) 0 4 :=
  of_native_maps core2505 DegreeTwoThreeSpectrum5280.graph DegreeTwoThreeSpectrum5281.graph
    sourceMap2505 fusedMap2505 sourceMap2505_checked fusedMap2505_checked
    DegreeTwoThreeFiniteComparisons.comparison2505
#print axioms sourceMap2505_checked
#print axioms fusedMap2505_checked
#print axioms certified2505
def sourceMap2505swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2505swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2505swap_checked : acceptsGraphIso
    (source (graph core2505) (root 10) 4 0) DegreeTwoThreeSpectrum5280.graph sourceMap2505swap=true := by decide +kernel
theorem fusedMap2505swap_checked : acceptsGraphIso
    (fused (graph core2505) (root 10) 4 0) DegreeTwoThreeSpectrum5281.graph fusedMap2505swap=true := by decide +kernel
theorem certified2505swap : Certified (graph core2505) (root 10) 4 0 :=
  of_native_maps core2505 DegreeTwoThreeSpectrum5280.graph DegreeTwoThreeSpectrum5281.graph
    sourceMap2505swap fusedMap2505swap sourceMap2505swap_checked fusedMap2505swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2505
#print axioms sourceMap2505swap_checked
#print axioms fusedMap2505swap_checked
#print axioms certified2505swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
