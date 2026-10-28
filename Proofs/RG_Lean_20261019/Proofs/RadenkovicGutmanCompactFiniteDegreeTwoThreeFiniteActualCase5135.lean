/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5135 : Family 8 := level8.get ⟨68,by decide⟩
def sourceMap5135 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,15,16,12,13,14,7,8,9,10,11] (sourceLabel 8 2 4 v)
def fusedMap5135 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5135_checked : acceptsGraphIso
    (source (graph core5135) (root 8) 2 4) DegreeTwoThreeSpectrum6793.graph sourceMap5135=true := by decide +kernel
theorem fusedMap5135_checked : acceptsGraphIso
    (fused (graph core5135) (root 8) 2 4) DegreeTwoThreeSpectrum5034.graph fusedMap5135=true := by decide +kernel
theorem certified5135 : Certified (graph core5135) (root 8) 2 4 :=
  of_native_maps core5135 DegreeTwoThreeSpectrum6793.graph DegreeTwoThreeSpectrum5034.graph
    sourceMap5135 fusedMap5135 sourceMap5135_checked fusedMap5135_checked
    DegreeTwoThreeFiniteComparisons.comparison5135
#print axioms sourceMap5135_checked
#print axioms fusedMap5135_checked
#print axioms certified5135
def sourceMap5135swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,15,16,7,8,9,10,11,12,13,14] (sourceLabel 8 4 2 v)
def fusedMap5135swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5135swap_checked : acceptsGraphIso
    (source (graph core5135) (root 8) 4 2) DegreeTwoThreeSpectrum6793.graph sourceMap5135swap=true := by decide +kernel
theorem fusedMap5135swap_checked : acceptsGraphIso
    (fused (graph core5135) (root 8) 4 2) DegreeTwoThreeSpectrum5034.graph fusedMap5135swap=true := by decide +kernel
theorem certified5135swap : Certified (graph core5135) (root 8) 4 2 :=
  of_native_maps core5135 DegreeTwoThreeSpectrum6793.graph DegreeTwoThreeSpectrum5034.graph
    sourceMap5135swap fusedMap5135swap sourceMap5135swap_checked fusedMap5135swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5135
#print axioms sourceMap5135swap_checked
#print axioms fusedMap5135swap_checked
#print axioms certified5135swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
