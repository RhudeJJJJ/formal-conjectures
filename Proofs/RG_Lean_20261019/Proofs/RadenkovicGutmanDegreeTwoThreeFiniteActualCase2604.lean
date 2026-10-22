/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2604 : Family 10 := level10.get ⟨545,by decide⟩
def sourceMap2604 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2604 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2604_checked : acceptsGraphIso
    (source (graph core2604) (root 10) 0 4) DegreeTwoThreeSpectrum6151.graph sourceMap2604=true := by decide +kernel
theorem fusedMap2604_checked : acceptsGraphIso
    (fused (graph core2604) (root 10) 0 4) DegreeTwoThreeSpectrum5196.graph fusedMap2604=true := by decide +kernel
theorem certified2604 : Certified (graph core2604) (root 10) 0 4 :=
  of_native_maps core2604 DegreeTwoThreeSpectrum6151.graph DegreeTwoThreeSpectrum5196.graph
    sourceMap2604 fusedMap2604 sourceMap2604_checked fusedMap2604_checked
    DegreeTwoThreeFiniteComparisons.comparison2604
#print axioms sourceMap2604_checked
#print axioms fusedMap2604_checked
#print axioms certified2604
def sourceMap2604swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2604swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2604swap_checked : acceptsGraphIso
    (source (graph core2604) (root 10) 4 0) DegreeTwoThreeSpectrum6151.graph sourceMap2604swap=true := by decide +kernel
theorem fusedMap2604swap_checked : acceptsGraphIso
    (fused (graph core2604) (root 10) 4 0) DegreeTwoThreeSpectrum5196.graph fusedMap2604swap=true := by decide +kernel
theorem certified2604swap : Certified (graph core2604) (root 10) 4 0 :=
  of_native_maps core2604 DegreeTwoThreeSpectrum6151.graph DegreeTwoThreeSpectrum5196.graph
    sourceMap2604swap fusedMap2604swap sourceMap2604swap_checked fusedMap2604swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2604
#print axioms sourceMap2604swap_checked
#print axioms fusedMap2604swap_checked
#print axioms certified2604swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
