/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3221 : Family 8 := level8.get ⟨233,by decide⟩
def sourceMap3221 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3221 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3221_checked : acceptsGraphIso
    (source (graph core3221) (root 8) 0 5) DegreeTwoThreeSpectrum4399.graph sourceMap3221=true := by decide +kernel
theorem fusedMap3221_checked : acceptsGraphIso
    (fused (graph core3221) (root 8) 0 5) DegreeTwoThreeSpectrum4400.graph fusedMap3221=true := by decide +kernel
theorem certified3221 : Certified (graph core3221) (root 8) 0 5 :=
  of_native_maps core3221 DegreeTwoThreeSpectrum4399.graph DegreeTwoThreeSpectrum4400.graph
    sourceMap3221 fusedMap3221 sourceMap3221_checked fusedMap3221_checked
    DegreeTwoThreeFiniteComparisons.comparison3221
#print axioms sourceMap3221_checked
#print axioms fusedMap3221_checked
#print axioms certified3221
def sourceMap3221swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3221swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3221swap_checked : acceptsGraphIso
    (source (graph core3221) (root 8) 5 0) DegreeTwoThreeSpectrum4399.graph sourceMap3221swap=true := by decide +kernel
theorem fusedMap3221swap_checked : acceptsGraphIso
    (fused (graph core3221) (root 8) 5 0) DegreeTwoThreeSpectrum4400.graph fusedMap3221swap=true := by decide +kernel
theorem certified3221swap : Certified (graph core3221) (root 8) 5 0 :=
  of_native_maps core3221 DegreeTwoThreeSpectrum4399.graph DegreeTwoThreeSpectrum4400.graph
    sourceMap3221swap fusedMap3221swap sourceMap3221swap_checked fusedMap3221swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3221
#print axioms sourceMap3221swap_checked
#print axioms fusedMap3221swap_checked
#print axioms certified3221swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
