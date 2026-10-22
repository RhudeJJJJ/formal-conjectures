/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2493 : Family 10 := level10.get ⟨182,by decide⟩
def sourceMap2493 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,7,8,2,3,4,5,6] (sourceLabel 10 0 4 v)
def fusedMap2493 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2493_checked : acceptsGraphIso
    (source (graph core2493) (root 10) 0 4) DegreeTwoThreeSpectrum5949.graph sourceMap2493=true := by decide +kernel
theorem fusedMap2493_checked : acceptsGraphIso
    (fused (graph core2493) (root 10) 0 4) DegreeTwoThreeSpectrum5129.graph fusedMap2493=true := by decide +kernel
theorem certified2493 : Certified (graph core2493) (root 10) 0 4 :=
  of_native_maps core2493 DegreeTwoThreeSpectrum5949.graph DegreeTwoThreeSpectrum5129.graph
    sourceMap2493 fusedMap2493 sourceMap2493_checked fusedMap2493_checked
    DegreeTwoThreeFiniteComparisons.comparison2493
#print axioms sourceMap2493_checked
#print axioms fusedMap2493_checked
#print axioms certified2493
def sourceMap2493swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,7,2,3,4,5,6,8] (sourceLabel 10 4 0 v)
def fusedMap2493swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2493swap_checked : acceptsGraphIso
    (source (graph core2493) (root 10) 4 0) DegreeTwoThreeSpectrum5949.graph sourceMap2493swap=true := by decide +kernel
theorem fusedMap2493swap_checked : acceptsGraphIso
    (fused (graph core2493) (root 10) 4 0) DegreeTwoThreeSpectrum5129.graph fusedMap2493swap=true := by decide +kernel
theorem certified2493swap : Certified (graph core2493) (root 10) 4 0 :=
  of_native_maps core2493 DegreeTwoThreeSpectrum5949.graph DegreeTwoThreeSpectrum5129.graph
    sourceMap2493swap fusedMap2493swap sourceMap2493swap_checked fusedMap2493swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2493
#print axioms sourceMap2493swap_checked
#print axioms fusedMap2493swap_checked
#print axioms certified2493swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
