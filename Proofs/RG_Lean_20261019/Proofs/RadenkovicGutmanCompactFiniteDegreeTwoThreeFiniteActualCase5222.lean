/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5222 : Family 5 := level5.get ⟨10,by decide⟩
def sourceMap5222 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,9,6,7,8,0,10,11,12,13,14] (sourceLabel 5 2 5 v)
def fusedMap5222 : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 2 5 v)
theorem sourceMap5222_checked : acceptsGraphIso
    (source (graph core5222) (root 5) 2 5) DegreeTwoThreeSpectrum2732.graph sourceMap5222=true := by decide +kernel
theorem fusedMap5222_checked : acceptsGraphIso
    (fused (graph core5222) (root 5) 2 5) DegreeTwoThreeSpectrum2365.graph fusedMap5222=true := by decide +kernel
theorem certified5222 : Certified (graph core5222) (root 5) 2 5 :=
  of_native_maps core5222 DegreeTwoThreeSpectrum2732.graph DegreeTwoThreeSpectrum2365.graph
    sourceMap5222 fusedMap5222 sourceMap5222_checked fusedMap5222_checked
    DegreeTwoThreeFiniteComparisons.comparison5222
#print axioms sourceMap5222_checked
#print axioms fusedMap5222_checked
#print axioms certified5222
def sourceMap5222swap : (Vertices 5 ⊕ Fin 6 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,5,9,0,10,11,12,13,14,6,7,8] (sourceLabel 5 5 2 v)
def fusedMap5222swap : (Vertices 5 ⊕ Fin 9) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,2,1,0,9,10,11,12,13,14] (fusedLabel 5 5 2 v)
theorem sourceMap5222swap_checked : acceptsGraphIso
    (source (graph core5222) (root 5) 5 2) DegreeTwoThreeSpectrum2732.graph sourceMap5222swap=true := by decide +kernel
theorem fusedMap5222swap_checked : acceptsGraphIso
    (fused (graph core5222) (root 5) 5 2) DegreeTwoThreeSpectrum2365.graph fusedMap5222swap=true := by decide +kernel
theorem certified5222swap : Certified (graph core5222) (root 5) 5 2 :=
  of_native_maps core5222 DegreeTwoThreeSpectrum2732.graph DegreeTwoThreeSpectrum2365.graph
    sourceMap5222swap fusedMap5222swap sourceMap5222swap_checked fusedMap5222swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5222
#print axioms sourceMap5222swap_checked
#print axioms fusedMap5222swap_checked
#print axioms certified5222swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
