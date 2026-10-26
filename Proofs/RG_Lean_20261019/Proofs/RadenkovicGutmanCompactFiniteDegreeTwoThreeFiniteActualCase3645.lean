/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3645 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap3645 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (sourceLabel 5 0 7 v)
def fusedMap3645 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 0 7 v)
theorem sourceMap3645_checked : acceptsGraphIso
    (source (graph core3645) (root 5) 0 7) DegreeTwoThreeSpectrum2509.graph sourceMap3645=true := by decide +kernel
theorem fusedMap3645_checked : acceptsGraphIso
    (fused (graph core3645) (root 5) 0 7) DegreeTwoThreeSpectrum2321.graph fusedMap3645=true := by decide +kernel
theorem certified3645 : Certified (graph core3645) (root 5) 0 7 :=
  of_native_maps core3645 DegreeTwoThreeSpectrum2509.graph DegreeTwoThreeSpectrum2321.graph
    sourceMap3645 fusedMap3645 sourceMap3645_checked fusedMap3645_checked
    DegreeTwoThreeFiniteComparisons.comparison3645
#print axioms sourceMap3645_checked
#print axioms fusedMap3645_checked
#print axioms certified3645
def sourceMap3645swap : (Vertices 5 ⊕ Fin 8 ⊕ Fin 1) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,10,11,12,13,14,9] (sourceLabel 5 7 0 v)
def fusedMap3645swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 7 0 v)
theorem sourceMap3645swap_checked : acceptsGraphIso
    (source (graph core3645) (root 5) 7 0) DegreeTwoThreeSpectrum2509.graph sourceMap3645swap=true := by decide +kernel
theorem fusedMap3645swap_checked : acceptsGraphIso
    (fused (graph core3645) (root 5) 7 0) DegreeTwoThreeSpectrum2321.graph fusedMap3645swap=true := by decide +kernel
theorem certified3645swap : Certified (graph core3645) (root 5) 7 0 :=
  of_native_maps core3645 DegreeTwoThreeSpectrum2509.graph DegreeTwoThreeSpectrum2321.graph
    sourceMap3645swap fusedMap3645swap sourceMap3645swap_checked fusedMap3645swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3645
#print axioms sourceMap3645swap_checked
#print axioms fusedMap3645swap_checked
#print axioms certified3645swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
