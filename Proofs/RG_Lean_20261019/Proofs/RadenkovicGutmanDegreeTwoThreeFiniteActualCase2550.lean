/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2550 : Family 10 := level10.get ⟨384,by decide⟩
def sourceMap2550 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2550 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2550_checked : acceptsGraphIso
    (source (graph core2550) (root 10) 0 4) DegreeTwoThreeSpectrum5713.graph sourceMap2550=true := by decide +kernel
theorem fusedMap2550_checked : acceptsGraphIso
    (fused (graph core2550) (root 10) 0 4) DegreeTwoThreeSpectrum5714.graph fusedMap2550=true := by decide +kernel
theorem certified2550 : Certified (graph core2550) (root 10) 0 4 :=
  of_native_maps core2550 DegreeTwoThreeSpectrum5713.graph DegreeTwoThreeSpectrum5714.graph
    sourceMap2550 fusedMap2550 sourceMap2550_checked fusedMap2550_checked
    DegreeTwoThreeFiniteComparisons.comparison2550
#print axioms sourceMap2550_checked
#print axioms fusedMap2550_checked
#print axioms certified2550
def sourceMap2550swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2550swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2550swap_checked : acceptsGraphIso
    (source (graph core2550) (root 10) 4 0) DegreeTwoThreeSpectrum5713.graph sourceMap2550swap=true := by decide +kernel
theorem fusedMap2550swap_checked : acceptsGraphIso
    (fused (graph core2550) (root 10) 4 0) DegreeTwoThreeSpectrum5714.graph fusedMap2550swap=true := by decide +kernel
theorem certified2550swap : Certified (graph core2550) (root 10) 4 0 :=
  of_native_maps core2550 DegreeTwoThreeSpectrum5713.graph DegreeTwoThreeSpectrum5714.graph
    sourceMap2550swap fusedMap2550swap sourceMap2550swap_checked fusedMap2550swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2550
#print axioms sourceMap2550swap_checked
#print axioms fusedMap2550swap_checked
#print axioms certified2550swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
