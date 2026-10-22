/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3656 : Family 6 := level6.get ⟨31,by decide⟩
def sourceMap3656 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (sourceLabel 6 0 7 v)
def fusedMap3656 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 0 7 v)
theorem sourceMap3656_checked : acceptsGraphIso
    (source (graph core3656) (root 6) 0 7) DegreeTwoThreeSpectrum4020.graph sourceMap3656=true := by decide +kernel
theorem fusedMap3656_checked : acceptsGraphIso
    (fused (graph core3656) (root 6) 0 7) DegreeTwoThreeSpectrum4023.graph fusedMap3656=true := by decide +kernel
theorem certified3656 : Certified (graph core3656) (root 6) 0 7 :=
  of_native_maps core3656 DegreeTwoThreeSpectrum4020.graph DegreeTwoThreeSpectrum4023.graph
    sourceMap3656 fusedMap3656 sourceMap3656_checked fusedMap3656_checked
    DegreeTwoThreeFiniteComparisons.comparison3656
#print axioms sourceMap3656_checked
#print axioms fusedMap3656_checked
#print axioms certified3656
def sourceMap3656swap : (Vertices 6 ⊕ Fin 8 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,15,9] (sourceLabel 6 7 0 v)
def fusedMap3656swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (fusedLabel 6 7 0 v)
theorem sourceMap3656swap_checked : acceptsGraphIso
    (source (graph core3656) (root 6) 7 0) DegreeTwoThreeSpectrum4020.graph sourceMap3656swap=true := by decide +kernel
theorem fusedMap3656swap_checked : acceptsGraphIso
    (fused (graph core3656) (root 6) 7 0) DegreeTwoThreeSpectrum4023.graph fusedMap3656swap=true := by decide +kernel
theorem certified3656swap : Certified (graph core3656) (root 6) 7 0 :=
  of_native_maps core3656 DegreeTwoThreeSpectrum4020.graph DegreeTwoThreeSpectrum4023.graph
    sourceMap3656swap fusedMap3656swap sourceMap3656swap_checked fusedMap3656swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3656
#print axioms sourceMap3656swap_checked
#print axioms fusedMap3656swap_checked
#print axioms certified3656swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
