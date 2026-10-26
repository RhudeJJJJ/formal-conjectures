/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3897 : Family 8 := level8.get ⟨208,by decide⟩
def sourceMap3897 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,9,10,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3897 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3897_checked : acceptsGraphIso
    (source (graph core3897) (root 8) 1 4) DegreeTwoThreeSpectrum4723.graph sourceMap3897=true := by decide +kernel
theorem fusedMap3897_checked : acceptsGraphIso
    (fused (graph core3897) (root 8) 1 4) DegreeTwoThreeSpectrum4264.graph fusedMap3897=true := by decide +kernel
theorem certified3897 : Certified (graph core3897) (root 8) 1 4 :=
  of_native_maps core3897 DegreeTwoThreeSpectrum4723.graph DegreeTwoThreeSpectrum4264.graph
    sourceMap3897 fusedMap3897 sourceMap3897_checked fusedMap3897_checked
    DegreeTwoThreeFiniteComparisons.comparison3897
#print axioms sourceMap3897_checked
#print axioms fusedMap3897_checked
#print axioms certified3897
def sourceMap3897swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,0,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3897swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3897swap_checked : acceptsGraphIso
    (source (graph core3897) (root 8) 4 1) DegreeTwoThreeSpectrum4723.graph sourceMap3897swap=true := by decide +kernel
theorem fusedMap3897swap_checked : acceptsGraphIso
    (fused (graph core3897) (root 8) 4 1) DegreeTwoThreeSpectrum4264.graph fusedMap3897swap=true := by decide +kernel
theorem certified3897swap : Certified (graph core3897) (root 8) 4 1 :=
  of_native_maps core3897 DegreeTwoThreeSpectrum4723.graph DegreeTwoThreeSpectrum4264.graph
    sourceMap3897swap fusedMap3897swap sourceMap3897swap_checked fusedMap3897swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3897
#print axioms sourceMap3897swap_checked
#print axioms fusedMap3897swap_checked
#print axioms certified3897swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
