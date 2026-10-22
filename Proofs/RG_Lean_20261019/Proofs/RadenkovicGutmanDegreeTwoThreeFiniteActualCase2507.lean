/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2507 : Family 10 := level10.get ⟨237,by decide⟩
def sourceMap2507 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2507 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2507_checked : acceptsGraphIso
    (source (graph core2507) (root 10) 0 4) DegreeTwoThreeSpectrum5299.graph sourceMap2507=true := by decide +kernel
theorem fusedMap2507_checked : acceptsGraphIso
    (fused (graph core2507) (root 10) 0 4) DegreeTwoThreeSpectrum5300.graph fusedMap2507=true := by decide +kernel
theorem certified2507 : Certified (graph core2507) (root 10) 0 4 :=
  of_native_maps core2507 DegreeTwoThreeSpectrum5299.graph DegreeTwoThreeSpectrum5300.graph
    sourceMap2507 fusedMap2507 sourceMap2507_checked fusedMap2507_checked
    DegreeTwoThreeFiniteComparisons.comparison2507
#print axioms sourceMap2507_checked
#print axioms fusedMap2507_checked
#print axioms certified2507
def sourceMap2507swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2507swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2507swap_checked : acceptsGraphIso
    (source (graph core2507) (root 10) 4 0) DegreeTwoThreeSpectrum5299.graph sourceMap2507swap=true := by decide +kernel
theorem fusedMap2507swap_checked : acceptsGraphIso
    (fused (graph core2507) (root 10) 4 0) DegreeTwoThreeSpectrum5300.graph fusedMap2507swap=true := by decide +kernel
theorem certified2507swap : Certified (graph core2507) (root 10) 4 0 :=
  of_native_maps core2507 DegreeTwoThreeSpectrum5299.graph DegreeTwoThreeSpectrum5300.graph
    sourceMap2507swap fusedMap2507swap sourceMap2507swap_checked fusedMap2507swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2507
#print axioms sourceMap2507swap_checked
#print axioms fusedMap2507swap_checked
#print axioms certified2507swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
