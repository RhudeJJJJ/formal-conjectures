/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5181 : Family 8 := level8.get ⟨190,by decide⟩
def sourceMap5181 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,9,10,11,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5181 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5181_checked : acceptsGraphIso
    (source (graph core5181) (root 8) 2 4) DegreeTwoThreeSpectrum7076.graph sourceMap5181=true := by decide +kernel
theorem fusedMap5181_checked : acceptsGraphIso
    (fused (graph core5181) (root 8) 2 4) DegreeTwoThreeSpectrum5136.graph fusedMap5181=true := by decide +kernel
theorem certified5181 : Certified (graph core5181) (root 8) 2 4 :=
  of_native_maps core5181 DegreeTwoThreeSpectrum7076.graph DegreeTwoThreeSpectrum5136.graph
    sourceMap5181 fusedMap5181 sourceMap5181_checked fusedMap5181_checked
    DegreeTwoThreeFiniteComparisons.comparison5181
#print axioms sourceMap5181_checked
#print axioms fusedMap5181_checked
#print axioms certified5181
def sourceMap5181swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,0,13,14,15,16,9,10,11] (sourceLabel 8 4 2 v)
def fusedMap5181swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5181swap_checked : acceptsGraphIso
    (source (graph core5181) (root 8) 4 2) DegreeTwoThreeSpectrum7076.graph sourceMap5181swap=true := by decide +kernel
theorem fusedMap5181swap_checked : acceptsGraphIso
    (fused (graph core5181) (root 8) 4 2) DegreeTwoThreeSpectrum5136.graph fusedMap5181swap=true := by decide +kernel
theorem certified5181swap : Certified (graph core5181) (root 8) 4 2 :=
  of_native_maps core5181 DegreeTwoThreeSpectrum7076.graph DegreeTwoThreeSpectrum5136.graph
    sourceMap5181swap fusedMap5181swap sourceMap5181swap_checked fusedMap5181swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5181
#print axioms sourceMap5181swap_checked
#print axioms fusedMap5181swap_checked
#print axioms certified5181swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
