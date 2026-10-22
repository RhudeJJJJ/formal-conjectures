/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3228 : Family 8 := level8.get ⟨245,by decide⟩
def sourceMap3228 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3228 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3228_checked : acceptsGraphIso
    (source (graph core3228) (root 8) 0 5) DegreeTwoThreeSpectrum4460.graph sourceMap3228=true := by decide +kernel
theorem fusedMap3228_checked : acceptsGraphIso
    (fused (graph core3228) (root 8) 0 5) DegreeTwoThreeSpectrum4461.graph fusedMap3228=true := by decide +kernel
theorem certified3228 : Certified (graph core3228) (root 8) 0 5 :=
  of_native_maps core3228 DegreeTwoThreeSpectrum4460.graph DegreeTwoThreeSpectrum4461.graph
    sourceMap3228 fusedMap3228 sourceMap3228_checked fusedMap3228_checked
    DegreeTwoThreeFiniteComparisons.comparison3228
#print axioms sourceMap3228_checked
#print axioms fusedMap3228_checked
#print axioms certified3228
def sourceMap3228swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3228swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3228swap_checked : acceptsGraphIso
    (source (graph core3228) (root 8) 5 0) DegreeTwoThreeSpectrum4460.graph sourceMap3228swap=true := by decide +kernel
theorem fusedMap3228swap_checked : acceptsGraphIso
    (fused (graph core3228) (root 8) 5 0) DegreeTwoThreeSpectrum4461.graph fusedMap3228swap=true := by decide +kernel
theorem certified3228swap : Certified (graph core3228) (root 8) 5 0 :=
  of_native_maps core3228 DegreeTwoThreeSpectrum4460.graph DegreeTwoThreeSpectrum4461.graph
    sourceMap3228swap fusedMap3228swap sourceMap3228swap_checked fusedMap3228swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3228
#print axioms sourceMap3228swap_checked
#print axioms fusedMap3228swap_checked
#print axioms certified3228swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
