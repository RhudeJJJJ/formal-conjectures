/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2492 : Family 10 := level10.get ⟨180,by decide⟩
def sourceMap2492 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,7,8,2,3,4,5,6] (sourceLabel 10 0 4 v)
def fusedMap2492 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2492_checked : acceptsGraphIso
    (source (graph core2492) (root 10) 0 4) DegreeTwoThreeSpectrum5948.graph sourceMap2492=true := by decide +kernel
theorem fusedMap2492_checked : acceptsGraphIso
    (fused (graph core2492) (root 10) 0 4) DegreeTwoThreeSpectrum5127.graph fusedMap2492=true := by decide +kernel
theorem certified2492 : Certified (graph core2492) (root 10) 0 4 :=
  of_native_maps core2492 DegreeTwoThreeSpectrum5948.graph DegreeTwoThreeSpectrum5127.graph
    sourceMap2492 fusedMap2492 sourceMap2492_checked fusedMap2492_checked
    DegreeTwoThreeFiniteComparisons.comparison2492
#print axioms sourceMap2492_checked
#print axioms fusedMap2492_checked
#print axioms certified2492
def sourceMap2492swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,7,2,3,4,5,6,8] (sourceLabel 10 4 0 v)
def fusedMap2492swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2492swap_checked : acceptsGraphIso
    (source (graph core2492) (root 10) 4 0) DegreeTwoThreeSpectrum5948.graph sourceMap2492swap=true := by decide +kernel
theorem fusedMap2492swap_checked : acceptsGraphIso
    (fused (graph core2492) (root 10) 4 0) DegreeTwoThreeSpectrum5127.graph fusedMap2492swap=true := by decide +kernel
theorem certified2492swap : Certified (graph core2492) (root 10) 4 0 :=
  of_native_maps core2492 DegreeTwoThreeSpectrum5948.graph DegreeTwoThreeSpectrum5127.graph
    sourceMap2492swap fusedMap2492swap sourceMap2492swap_checked fusedMap2492swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2492
#print axioms sourceMap2492swap_checked
#print axioms fusedMap2492swap_checked
#print axioms certified2492swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
