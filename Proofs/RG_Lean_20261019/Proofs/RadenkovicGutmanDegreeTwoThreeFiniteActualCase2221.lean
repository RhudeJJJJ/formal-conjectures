/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2221 : Family 9 := level9.get ⟨40,by decide⟩
def sourceMap2221 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,7,8,2,3,4,5,6] (sourceLabel 9 0 4 v)
def fusedMap2221 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,8,9,10,11,12,13,14,15,7,1,2,3,4,5,6] (fusedLabel 9 0 4 v)
theorem sourceMap2221_checked : acceptsGraphIso
    (source (graph core2221) (root 9) 0 4) DegreeTwoThreeSpectrum4165.graph sourceMap2221=true := by decide +kernel
theorem fusedMap2221_checked : acceptsGraphIso
    (fused (graph core2221) (root 9) 0 4) DegreeTwoThreeSpectrum3890.graph fusedMap2221=true := by decide +kernel
theorem certified2221 : Certified (graph core2221) (root 9) 0 4 :=
  of_native_maps core2221 DegreeTwoThreeSpectrum4165.graph DegreeTwoThreeSpectrum3890.graph
    sourceMap2221 fusedMap2221 sourceMap2221_checked fusedMap2221_checked
    DegreeTwoThreeFiniteComparisons.comparison2221
#print axioms sourceMap2221_checked
#print axioms fusedMap2221_checked
#print axioms certified2221
def sourceMap2221swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,7,2,3,4,5,6,8] (sourceLabel 9 4 0 v)
def fusedMap2221swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,8,9,10,11,12,13,14,15,7,1,2,3,4,5,6] (fusedLabel 9 4 0 v)
theorem sourceMap2221swap_checked : acceptsGraphIso
    (source (graph core2221) (root 9) 4 0) DegreeTwoThreeSpectrum4165.graph sourceMap2221swap=true := by decide +kernel
theorem fusedMap2221swap_checked : acceptsGraphIso
    (fused (graph core2221) (root 9) 4 0) DegreeTwoThreeSpectrum3890.graph fusedMap2221swap=true := by decide +kernel
theorem certified2221swap : Certified (graph core2221) (root 9) 4 0 :=
  of_native_maps core2221 DegreeTwoThreeSpectrum4165.graph DegreeTwoThreeSpectrum3890.graph
    sourceMap2221swap fusedMap2221swap sourceMap2221swap_checked fusedMap2221swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2221
#print axioms sourceMap2221swap_checked
#print axioms fusedMap2221swap_checked
#print axioms certified2221swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
