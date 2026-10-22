/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5158 : Family 8 := level8.get ⟨135,by decide⟩
def sourceMap5158 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5158 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5158_checked : acceptsGraphIso
    (source (graph core5158) (root 8) 2 4) DegreeTwoThreeSpectrum6518.graph sourceMap5158=true := by decide +kernel
theorem fusedMap5158_checked : acceptsGraphIso
    (fused (graph core5158) (root 8) 2 4) DegreeTwoThreeSpectrum5435.graph fusedMap5158=true := by decide +kernel
theorem certified5158 : Certified (graph core5158) (root 8) 2 4 :=
  of_native_maps core5158 DegreeTwoThreeSpectrum6518.graph DegreeTwoThreeSpectrum5435.graph
    sourceMap5158 fusedMap5158 sourceMap5158_checked fusedMap5158_checked
    DegreeTwoThreeFiniteComparisons.comparison5158
#print axioms sourceMap5158_checked
#print axioms fusedMap5158_checked
#print axioms certified5158
def sourceMap5158swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5158swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5158swap_checked : acceptsGraphIso
    (source (graph core5158) (root 8) 4 2) DegreeTwoThreeSpectrum6518.graph sourceMap5158swap=true := by decide +kernel
theorem fusedMap5158swap_checked : acceptsGraphIso
    (fused (graph core5158) (root 8) 4 2) DegreeTwoThreeSpectrum5435.graph fusedMap5158swap=true := by decide +kernel
theorem certified5158swap : Certified (graph core5158) (root 8) 4 2 :=
  of_native_maps core5158 DegreeTwoThreeSpectrum6518.graph DegreeTwoThreeSpectrum5435.graph
    sourceMap5158swap fusedMap5158swap sourceMap5158swap_checked fusedMap5158swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5158
#print axioms sourceMap5158swap_checked
#print axioms fusedMap5158swap_checked
#print axioms certified5158swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
