/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2473 : Family 10 := level10.get ⟨109,by decide⟩
def sourceMap2473 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2473 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2473_checked : acceptsGraphIso
    (source (graph core2473) (root 10) 0 4) DegreeTwoThreeSpectrum5627.graph sourceMap2473=true := by decide +kernel
theorem fusedMap2473_checked : acceptsGraphIso
    (fused (graph core2473) (root 10) 0 4) DegreeTwoThreeSpectrum5032.graph fusedMap2473=true := by decide +kernel
theorem certified2473 : Certified (graph core2473) (root 10) 0 4 :=
  of_native_maps core2473 DegreeTwoThreeSpectrum5627.graph DegreeTwoThreeSpectrum5032.graph
    sourceMap2473 fusedMap2473 sourceMap2473_checked fusedMap2473_checked
    DegreeTwoThreeFiniteComparisons.comparison2473
#print axioms sourceMap2473_checked
#print axioms fusedMap2473_checked
#print axioms certified2473
def sourceMap2473swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2473swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2473swap_checked : acceptsGraphIso
    (source (graph core2473) (root 10) 4 0) DegreeTwoThreeSpectrum5627.graph sourceMap2473swap=true := by decide +kernel
theorem fusedMap2473swap_checked : acceptsGraphIso
    (fused (graph core2473) (root 10) 4 0) DegreeTwoThreeSpectrum5032.graph fusedMap2473swap=true := by decide +kernel
theorem certified2473swap : Certified (graph core2473) (root 10) 4 0 :=
  of_native_maps core2473 DegreeTwoThreeSpectrum5627.graph DegreeTwoThreeSpectrum5032.graph
    sourceMap2473swap fusedMap2473swap sourceMap2473swap_checked fusedMap2473swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2473
#print axioms sourceMap2473swap_checked
#print axioms fusedMap2473swap_checked
#print axioms certified2473swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
