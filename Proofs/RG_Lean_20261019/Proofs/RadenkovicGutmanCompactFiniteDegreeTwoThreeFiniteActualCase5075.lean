/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5075 : Family 6 := level6.get ⟨30,by decide⟩
def sourceMap5075 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,10,7,8,9,0,11,12,13,14] (sourceLabel 6 2 4 v)
def fusedMap5075 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap5075_checked : acceptsGraphIso
    (source (graph core5075) (root 6) 2 4) DegreeTwoThreeSpectrum3491.graph sourceMap5075=true := by decide +kernel
theorem fusedMap5075_checked : acceptsGraphIso
    (fused (graph core5075) (root 6) 2 4) DegreeTwoThreeSpectrum2355.graph fusedMap5075=true := by decide +kernel
theorem certified5075 : Certified (graph core5075) (root 6) 2 4 :=
  of_native_maps core5075 DegreeTwoThreeSpectrum3491.graph DegreeTwoThreeSpectrum2355.graph
    sourceMap5075 fusedMap5075 sourceMap5075_checked fusedMap5075_checked
    DegreeTwoThreeFiniteComparisons.comparison5075
#print axioms sourceMap5075_checked
#print axioms fusedMap5075_checked
#print axioms certified5075
def sourceMap5075swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,10,0,11,12,13,14,7,8,9] (sourceLabel 6 4 2 v)
def fusedMap5075swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap5075swap_checked : acceptsGraphIso
    (source (graph core5075) (root 6) 4 2) DegreeTwoThreeSpectrum3491.graph sourceMap5075swap=true := by decide +kernel
theorem fusedMap5075swap_checked : acceptsGraphIso
    (fused (graph core5075) (root 6) 4 2) DegreeTwoThreeSpectrum2355.graph fusedMap5075swap=true := by decide +kernel
theorem certified5075swap : Certified (graph core5075) (root 6) 4 2 :=
  of_native_maps core5075 DegreeTwoThreeSpectrum3491.graph DegreeTwoThreeSpectrum2355.graph
    sourceMap5075swap fusedMap5075swap sourceMap5075swap_checked fusedMap5075swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5075
#print axioms sourceMap5075swap_checked
#print axioms fusedMap5075swap_checked
#print axioms certified5075swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
