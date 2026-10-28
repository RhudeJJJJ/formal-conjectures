/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5196 : Family 8 := level8.get ⟨222,by decide⟩
def sourceMap5196 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5196 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5196_checked : acceptsGraphIso
    (source (graph core5196) (root 8) 2 4) DegreeTwoThreeSpectrum7258.graph sourceMap5196=true := by decide +kernel
theorem fusedMap5196_checked : acceptsGraphIso
    (fused (graph core5196) (root 8) 2 4) DegreeTwoThreeSpectrum5305.graph fusedMap5196=true := by decide +kernel
theorem certified5196 : Certified (graph core5196) (root 8) 2 4 :=
  of_native_maps core5196 DegreeTwoThreeSpectrum7258.graph DegreeTwoThreeSpectrum5305.graph
    sourceMap5196 fusedMap5196 sourceMap5196_checked fusedMap5196_checked
    DegreeTwoThreeFiniteComparisons.comparison5196
#print axioms sourceMap5196_checked
#print axioms fusedMap5196_checked
#print axioms certified5196
def sourceMap5196swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,13,14,15,16,10,11,12] (sourceLabel 8 4 2 v)
def fusedMap5196swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5196swap_checked : acceptsGraphIso
    (source (graph core5196) (root 8) 4 2) DegreeTwoThreeSpectrum7258.graph sourceMap5196swap=true := by decide +kernel
theorem fusedMap5196swap_checked : acceptsGraphIso
    (fused (graph core5196) (root 8) 4 2) DegreeTwoThreeSpectrum5305.graph fusedMap5196swap=true := by decide +kernel
theorem certified5196swap : Certified (graph core5196) (root 8) 4 2 :=
  of_native_maps core5196 DegreeTwoThreeSpectrum7258.graph DegreeTwoThreeSpectrum5305.graph
    sourceMap5196swap fusedMap5196swap sourceMap5196swap_checked fusedMap5196swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5196
#print axioms sourceMap5196swap_checked
#print axioms fusedMap5196swap_checked
#print axioms certified5196swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
