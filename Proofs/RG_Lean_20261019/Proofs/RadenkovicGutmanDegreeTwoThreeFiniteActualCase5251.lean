/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5251 : Family 7 := level7.get ⟨37,by decide⟩
def sourceMap5251 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,7,8,9,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5251 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5251_checked : acceptsGraphIso
    (source (graph core5251) (root 7) 2 5) DegreeTwoThreeSpectrum6437.graph sourceMap5251=true := by decide +kernel
theorem fusedMap5251_checked : acceptsGraphIso
    (fused (graph core5251) (root 7) 2 5) DegreeTwoThreeSpectrum4988.graph fusedMap5251=true := by decide +kernel
theorem certified5251 : Certified (graph core5251) (root 7) 2 5 :=
  of_native_maps core5251 DegreeTwoThreeSpectrum6437.graph DegreeTwoThreeSpectrum4988.graph
    sourceMap5251 fusedMap5251 sourceMap5251_checked fusedMap5251_checked
    DegreeTwoThreeFiniteComparisons.comparison5251
#print axioms sourceMap5251_checked
#print axioms fusedMap5251_checked
#print axioms certified5251
def sourceMap5251swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,0,12,13,14,15,16,7,8,9] (sourceLabel 7 5 2 v)
def fusedMap5251swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5251swap_checked : acceptsGraphIso
    (source (graph core5251) (root 7) 5 2) DegreeTwoThreeSpectrum6437.graph sourceMap5251swap=true := by decide +kernel
theorem fusedMap5251swap_checked : acceptsGraphIso
    (fused (graph core5251) (root 7) 5 2) DegreeTwoThreeSpectrum4988.graph fusedMap5251swap=true := by decide +kernel
theorem certified5251swap : Certified (graph core5251) (root 7) 5 2 :=
  of_native_maps core5251 DegreeTwoThreeSpectrum6437.graph DegreeTwoThreeSpectrum4988.graph
    sourceMap5251swap fusedMap5251swap sourceMap5251swap_checked fusedMap5251swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5251
#print axioms sourceMap5251swap_checked
#print axioms fusedMap5251swap_checked
#print axioms certified5251swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
