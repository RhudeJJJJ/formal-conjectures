/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2145 : Family 8 := level8.get ⟨98,by decide⟩
def sourceMap2145 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2145 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2145_checked : acceptsGraphIso
    (source (graph core2145) (root 8) 0 4) DegreeTwoThreeSpectrum2449.graph sourceMap2145=true := by decide +kernel
theorem fusedMap2145_checked : acceptsGraphIso
    (fused (graph core2145) (root 8) 0 4) DegreeTwoThreeSpectrum2451.graph fusedMap2145=true := by decide +kernel
theorem certified2145 : Certified (graph core2145) (root 8) 0 4 :=
  of_native_maps core2145 DegreeTwoThreeSpectrum2449.graph DegreeTwoThreeSpectrum2451.graph
    sourceMap2145 fusedMap2145 sourceMap2145_checked fusedMap2145_checked
    DegreeTwoThreeFiniteComparisons.comparison2145
#print axioms sourceMap2145_checked
#print axioms fusedMap2145_checked
#print axioms certified2145
def sourceMap2145swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2145swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2145swap_checked : acceptsGraphIso
    (source (graph core2145) (root 8) 4 0) DegreeTwoThreeSpectrum2449.graph sourceMap2145swap=true := by decide +kernel
theorem fusedMap2145swap_checked : acceptsGraphIso
    (fused (graph core2145) (root 8) 4 0) DegreeTwoThreeSpectrum2451.graph fusedMap2145swap=true := by decide +kernel
theorem certified2145swap : Certified (graph core2145) (root 8) 4 0 :=
  of_native_maps core2145 DegreeTwoThreeSpectrum2449.graph DegreeTwoThreeSpectrum2451.graph
    sourceMap2145swap fusedMap2145swap sourceMap2145swap_checked fusedMap2145swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2145
#print axioms sourceMap2145swap_checked
#print axioms fusedMap2145swap_checked
#print axioms certified2145swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
