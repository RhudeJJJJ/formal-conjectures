/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2475 : Family 10 := level10.get ⟨116,by decide⟩
def sourceMap2475 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,14,15,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2475 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2475_checked : acceptsGraphIso
    (source (graph core2475) (root 10) 0 4) DegreeTwoThreeSpectrum5651.graph sourceMap2475=true := by decide +kernel
theorem fusedMap2475_checked : acceptsGraphIso
    (fused (graph core2475) (root 10) 0 4) DegreeTwoThreeSpectrum5041.graph fusedMap2475=true := by decide +kernel
theorem certified2475 : Certified (graph core2475) (root 10) 0 4 :=
  of_native_maps core2475 DegreeTwoThreeSpectrum5651.graph DegreeTwoThreeSpectrum5041.graph
    sourceMap2475 fusedMap2475 sourceMap2475_checked fusedMap2475_checked
    DegreeTwoThreeFiniteComparisons.comparison2475
#print axioms sourceMap2475_checked
#print axioms fusedMap2475_checked
#print axioms certified2475
def sourceMap2475swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,16,14,9,10,11,12,13,15] (sourceLabel 10 4 0 v)
def fusedMap2475swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2475swap_checked : acceptsGraphIso
    (source (graph core2475) (root 10) 4 0) DegreeTwoThreeSpectrum5651.graph sourceMap2475swap=true := by decide +kernel
theorem fusedMap2475swap_checked : acceptsGraphIso
    (fused (graph core2475) (root 10) 4 0) DegreeTwoThreeSpectrum5041.graph fusedMap2475swap=true := by decide +kernel
theorem certified2475swap : Certified (graph core2475) (root 10) 4 0 :=
  of_native_maps core2475 DegreeTwoThreeSpectrum5651.graph DegreeTwoThreeSpectrum5041.graph
    sourceMap2475swap fusedMap2475swap sourceMap2475swap_checked fusedMap2475swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2475
#print axioms sourceMap2475swap_checked
#print axioms fusedMap2475swap_checked
#print axioms certified2475swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
