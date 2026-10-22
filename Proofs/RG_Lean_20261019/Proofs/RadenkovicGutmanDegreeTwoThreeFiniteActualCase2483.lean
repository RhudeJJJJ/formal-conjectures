/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2483 : Family 10 := level10.get ⟨150,by decide⟩
def sourceMap2483 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2483 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2483_checked : acceptsGraphIso
    (source (graph core2483) (root 10) 0 4) DegreeTwoThreeSpectrum5865.graph sourceMap2483=true := by decide +kernel
theorem fusedMap2483_checked : acceptsGraphIso
    (fused (graph core2483) (root 10) 0 4) DegreeTwoThreeSpectrum5086.graph fusedMap2483=true := by decide +kernel
theorem certified2483 : Certified (graph core2483) (root 10) 0 4 :=
  of_native_maps core2483 DegreeTwoThreeSpectrum5865.graph DegreeTwoThreeSpectrum5086.graph
    sourceMap2483 fusedMap2483 sourceMap2483_checked fusedMap2483_checked
    DegreeTwoThreeFiniteComparisons.comparison2483
#print axioms sourceMap2483_checked
#print axioms fusedMap2483_checked
#print axioms certified2483
def sourceMap2483swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2483swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2483swap_checked : acceptsGraphIso
    (source (graph core2483) (root 10) 4 0) DegreeTwoThreeSpectrum5865.graph sourceMap2483swap=true := by decide +kernel
theorem fusedMap2483swap_checked : acceptsGraphIso
    (fused (graph core2483) (root 10) 4 0) DegreeTwoThreeSpectrum5086.graph fusedMap2483swap=true := by decide +kernel
theorem certified2483swap : Certified (graph core2483) (root 10) 4 0 :=
  of_native_maps core2483 DegreeTwoThreeSpectrum5865.graph DegreeTwoThreeSpectrum5086.graph
    sourceMap2483swap fusedMap2483swap sourceMap2483swap_checked fusedMap2483swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2483
#print axioms sourceMap2483swap_checked
#print axioms fusedMap2483swap_checked
#print axioms certified2483swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
