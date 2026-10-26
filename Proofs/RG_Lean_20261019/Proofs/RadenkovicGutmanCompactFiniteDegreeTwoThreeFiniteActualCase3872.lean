/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3872 : Family 8 := level8.get ⟨152,by decide⟩
def sourceMap3872 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3872 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3872_checked : acceptsGraphIso
    (source (graph core3872) (root 8) 1 4) DegreeTwoThreeSpectrum4497.graph sourceMap3872=true := by decide +kernel
theorem fusedMap3872_checked : acceptsGraphIso
    (fused (graph core3872) (root 8) 1 4) DegreeTwoThreeSpectrum4021.graph fusedMap3872=true := by decide +kernel
theorem certified3872 : Certified (graph core3872) (root 8) 1 4 :=
  of_native_maps core3872 DegreeTwoThreeSpectrum4497.graph DegreeTwoThreeSpectrum4021.graph
    sourceMap3872 fusedMap3872 sourceMap3872_checked fusedMap3872_checked
    DegreeTwoThreeFiniteComparisons.comparison3872
#print axioms sourceMap3872_checked
#print axioms fusedMap3872_checked
#print axioms certified3872
def sourceMap3872swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 8 4 1 v)
def fusedMap3872swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3872swap_checked : acceptsGraphIso
    (source (graph core3872) (root 8) 4 1) DegreeTwoThreeSpectrum4497.graph sourceMap3872swap=true := by decide +kernel
theorem fusedMap3872swap_checked : acceptsGraphIso
    (fused (graph core3872) (root 8) 4 1) DegreeTwoThreeSpectrum4021.graph fusedMap3872swap=true := by decide +kernel
theorem certified3872swap : Certified (graph core3872) (root 8) 4 1 :=
  of_native_maps core3872 DegreeTwoThreeSpectrum4497.graph DegreeTwoThreeSpectrum4021.graph
    sourceMap3872swap fusedMap3872swap sourceMap3872swap_checked fusedMap3872swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3872
#print axioms sourceMap3872swap_checked
#print axioms fusedMap3872swap_checked
#print axioms certified3872swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
