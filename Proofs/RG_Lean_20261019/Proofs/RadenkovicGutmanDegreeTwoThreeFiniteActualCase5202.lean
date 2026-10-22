/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5202 : Family 8 := level8.get ⟨236,by decide⟩
def sourceMap5202 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5202 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5202_checked : acceptsGraphIso
    (source (graph core5202) (root 8) 2 4) DegreeTwoThreeSpectrum7355.graph sourceMap5202=true := by decide +kernel
theorem fusedMap5202_checked : acceptsGraphIso
    (fused (graph core5202) (root 8) 2 4) DegreeTwoThreeSpectrum5441.graph fusedMap5202=true := by decide +kernel
theorem certified5202 : Certified (graph core5202) (root 8) 2 4 :=
  of_native_maps core5202 DegreeTwoThreeSpectrum7355.graph DegreeTwoThreeSpectrum5441.graph
    sourceMap5202 fusedMap5202 sourceMap5202_checked fusedMap5202_checked
    DegreeTwoThreeFiniteComparisons.comparison5202
#print axioms sourceMap5202_checked
#print axioms fusedMap5202_checked
#print axioms certified5202
def sourceMap5202swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,13,14,15,16,10,11,12] (sourceLabel 8 4 2 v)
def fusedMap5202swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5202swap_checked : acceptsGraphIso
    (source (graph core5202) (root 8) 4 2) DegreeTwoThreeSpectrum7355.graph sourceMap5202swap=true := by decide +kernel
theorem fusedMap5202swap_checked : acceptsGraphIso
    (fused (graph core5202) (root 8) 4 2) DegreeTwoThreeSpectrum5441.graph fusedMap5202swap=true := by decide +kernel
theorem certified5202swap : Certified (graph core5202) (root 8) 4 2 :=
  of_native_maps core5202 DegreeTwoThreeSpectrum7355.graph DegreeTwoThreeSpectrum5441.graph
    sourceMap5202swap fusedMap5202swap sourceMap5202swap_checked fusedMap5202swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5202
#print axioms sourceMap5202swap_checked
#print axioms fusedMap5202swap_checked
#print axioms certified5202swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
