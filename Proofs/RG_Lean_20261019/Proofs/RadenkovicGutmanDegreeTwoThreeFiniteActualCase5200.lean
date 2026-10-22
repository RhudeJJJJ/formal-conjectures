/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5200 : Family 8 := level8.get ⟨233,by decide⟩
def sourceMap5200 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,9,10,11,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5200 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5200_checked : acceptsGraphIso
    (source (graph core5200) (root 8) 2 4) DegreeTwoThreeSpectrum7334.graph sourceMap5200=true := by decide +kernel
theorem fusedMap5200_checked : acceptsGraphIso
    (fused (graph core5200) (root 8) 2 4) DegreeTwoThreeSpectrum5424.graph fusedMap5200=true := by decide +kernel
theorem certified5200 : Certified (graph core5200) (root 8) 2 4 :=
  of_native_maps core5200 DegreeTwoThreeSpectrum7334.graph DegreeTwoThreeSpectrum5424.graph
    sourceMap5200 fusedMap5200 sourceMap5200_checked fusedMap5200_checked
    DegreeTwoThreeFiniteComparisons.comparison5200
#print axioms sourceMap5200_checked
#print axioms fusedMap5200_checked
#print axioms certified5200
def sourceMap5200swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,12,0,13,14,15,16,9,10,11] (sourceLabel 8 4 2 v)
def fusedMap5200swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5200swap_checked : acceptsGraphIso
    (source (graph core5200) (root 8) 4 2) DegreeTwoThreeSpectrum7334.graph sourceMap5200swap=true := by decide +kernel
theorem fusedMap5200swap_checked : acceptsGraphIso
    (fused (graph core5200) (root 8) 4 2) DegreeTwoThreeSpectrum5424.graph fusedMap5200swap=true := by decide +kernel
theorem certified5200swap : Certified (graph core5200) (root 8) 4 2 :=
  of_native_maps core5200 DegreeTwoThreeSpectrum7334.graph DegreeTwoThreeSpectrum5424.graph
    sourceMap5200swap fusedMap5200swap sourceMap5200swap_checked fusedMap5200swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5200
#print axioms sourceMap5200swap_checked
#print axioms fusedMap5200swap_checked
#print axioms certified5200swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
