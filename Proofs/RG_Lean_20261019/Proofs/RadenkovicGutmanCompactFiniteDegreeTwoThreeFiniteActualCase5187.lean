/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5187 : Family 8 := level8.get ⟨203,by decide⟩
def sourceMap5187 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5187 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5187_checked : acceptsGraphIso
    (source (graph core5187) (root 8) 2 4) DegreeTwoThreeSpectrum7150.graph sourceMap5187=true := by decide +kernel
theorem fusedMap5187_checked : acceptsGraphIso
    (fused (graph core5187) (root 8) 2 4) DegreeTwoThreeSpectrum5183.graph fusedMap5187=true := by decide +kernel
theorem certified5187 : Certified (graph core5187) (root 8) 2 4 :=
  of_native_maps core5187 DegreeTwoThreeSpectrum7150.graph DegreeTwoThreeSpectrum5183.graph
    sourceMap5187 fusedMap5187 sourceMap5187_checked fusedMap5187_checked
    DegreeTwoThreeFiniteComparisons.comparison5187
#print axioms sourceMap5187_checked
#print axioms fusedMap5187_checked
#print axioms certified5187
def sourceMap5187swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,13,14,15,16,10,11,12] (sourceLabel 8 4 2 v)
def fusedMap5187swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5187swap_checked : acceptsGraphIso
    (source (graph core5187) (root 8) 4 2) DegreeTwoThreeSpectrum7150.graph sourceMap5187swap=true := by decide +kernel
theorem fusedMap5187swap_checked : acceptsGraphIso
    (fused (graph core5187) (root 8) 4 2) DegreeTwoThreeSpectrum5183.graph fusedMap5187swap=true := by decide +kernel
theorem certified5187swap : Certified (graph core5187) (root 8) 4 2 :=
  of_native_maps core5187 DegreeTwoThreeSpectrum7150.graph DegreeTwoThreeSpectrum5183.graph
    sourceMap5187swap fusedMap5187swap sourceMap5187swap_checked fusedMap5187swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5187
#print axioms sourceMap5187swap_checked
#print axioms fusedMap5187swap_checked
#print axioms certified5187swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
