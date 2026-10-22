/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2479 : Family 10 := level10.get ⟨135,by decide⟩
def sourceMap2479 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2479 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2479_checked : acceptsGraphIso
    (source (graph core2479) (root 10) 0 4) DegreeTwoThreeSpectrum5791.graph sourceMap2479=true := by decide +kernel
theorem fusedMap2479_checked : acceptsGraphIso
    (fused (graph core2479) (root 10) 0 4) DegreeTwoThreeSpectrum5065.graph fusedMap2479=true := by decide +kernel
theorem certified2479 : Certified (graph core2479) (root 10) 0 4 :=
  of_native_maps core2479 DegreeTwoThreeSpectrum5791.graph DegreeTwoThreeSpectrum5065.graph
    sourceMap2479 fusedMap2479 sourceMap2479_checked fusedMap2479_checked
    DegreeTwoThreeFiniteComparisons.comparison2479
#print axioms sourceMap2479_checked
#print axioms fusedMap2479_checked
#print axioms certified2479
def sourceMap2479swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2479swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2479swap_checked : acceptsGraphIso
    (source (graph core2479) (root 10) 4 0) DegreeTwoThreeSpectrum5791.graph sourceMap2479swap=true := by decide +kernel
theorem fusedMap2479swap_checked : acceptsGraphIso
    (fused (graph core2479) (root 10) 4 0) DegreeTwoThreeSpectrum5065.graph fusedMap2479swap=true := by decide +kernel
theorem certified2479swap : Certified (graph core2479) (root 10) 4 0 :=
  of_native_maps core2479 DegreeTwoThreeSpectrum5791.graph DegreeTwoThreeSpectrum5065.graph
    sourceMap2479swap fusedMap2479swap sourceMap2479swap_checked fusedMap2479swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2479
#print axioms sourceMap2479swap_checked
#print axioms fusedMap2479swap_checked
#print axioms certified2479swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
