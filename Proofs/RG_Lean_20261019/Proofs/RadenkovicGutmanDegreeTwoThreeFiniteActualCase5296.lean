/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5296 : Family 6 := level6.get ⟨24,by decide⟩
def sourceMap5296 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,11,8,9,10,1,0,12,13,14,15,16] (sourceLabel 6 2 6 v)
def fusedMap5296 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 2 6 v)
theorem sourceMap5296_checked : acceptsGraphIso
    (source (graph core5296) (root 6) 2 6) DegreeTwoThreeSpectrum6286.graph sourceMap5296=true := by decide +kernel
theorem fusedMap5296_checked : acceptsGraphIso
    (fused (graph core5296) (root 6) 2 6) DegreeTwoThreeSpectrum4975.graph fusedMap5296=true := by decide +kernel
theorem certified5296 : Certified (graph core5296) (root 6) 2 6 :=
  of_native_maps core5296 DegreeTwoThreeSpectrum6286.graph DegreeTwoThreeSpectrum4975.graph
    sourceMap5296 fusedMap5296 sourceMap5296_checked fusedMap5296_checked
    DegreeTwoThreeFiniteComparisons.comparison5296
#print axioms sourceMap5296_checked
#print axioms fusedMap5296_checked
#print axioms certified5296
def sourceMap5296swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,11,1,0,12,13,14,15,16,8,9,10] (sourceLabel 6 6 2 v)
def fusedMap5296swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 6 2 v)
theorem sourceMap5296swap_checked : acceptsGraphIso
    (source (graph core5296) (root 6) 6 2) DegreeTwoThreeSpectrum6286.graph sourceMap5296swap=true := by decide +kernel
theorem fusedMap5296swap_checked : acceptsGraphIso
    (fused (graph core5296) (root 6) 6 2) DegreeTwoThreeSpectrum4975.graph fusedMap5296swap=true := by decide +kernel
theorem certified5296swap : Certified (graph core5296) (root 6) 6 2 :=
  of_native_maps core5296 DegreeTwoThreeSpectrum6286.graph DegreeTwoThreeSpectrum4975.graph
    sourceMap5296swap fusedMap5296swap sourceMap5296swap_checked fusedMap5296swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5296
#print axioms sourceMap5296swap_checked
#print axioms fusedMap5296swap_checked
#print axioms certified5296swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
