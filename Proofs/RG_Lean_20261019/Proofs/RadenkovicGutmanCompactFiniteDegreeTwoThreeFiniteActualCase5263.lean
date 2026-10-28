/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5263 : Family 7 := level7.get ⟨68,by decide⟩
def sourceMap5263 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,7,8,9,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5263 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5263_checked : acceptsGraphIso
    (source (graph core5263) (root 7) 2 5) DegreeTwoThreeSpectrum6122.graph sourceMap5263=true := by decide +kernel
theorem fusedMap5263_checked : acceptsGraphIso
    (fused (graph core5263) (root 7) 2 5) DegreeTwoThreeSpectrum5188.graph fusedMap5263=true := by decide +kernel
theorem certified5263 : Certified (graph core5263) (root 7) 2 5 :=
  of_native_maps core5263 DegreeTwoThreeSpectrum6122.graph DegreeTwoThreeSpectrum5188.graph
    sourceMap5263 fusedMap5263 sourceMap5263_checked fusedMap5263_checked
    DegreeTwoThreeFiniteComparisons.comparison5263
#print axioms sourceMap5263_checked
#print axioms fusedMap5263_checked
#print axioms certified5263
def sourceMap5263swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,0,12,13,14,15,16,7,8,9] (sourceLabel 7 5 2 v)
def fusedMap5263swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5263swap_checked : acceptsGraphIso
    (source (graph core5263) (root 7) 5 2) DegreeTwoThreeSpectrum6122.graph sourceMap5263swap=true := by decide +kernel
theorem fusedMap5263swap_checked : acceptsGraphIso
    (fused (graph core5263) (root 7) 5 2) DegreeTwoThreeSpectrum5188.graph fusedMap5263swap=true := by decide +kernel
theorem certified5263swap : Certified (graph core5263) (root 7) 5 2 :=
  of_native_maps core5263 DegreeTwoThreeSpectrum6122.graph DegreeTwoThreeSpectrum5188.graph
    sourceMap5263swap fusedMap5263swap sourceMap5263swap_checked fusedMap5263swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5263
#print axioms sourceMap5263swap_checked
#print axioms fusedMap5263swap_checked
#print axioms certified5263swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
