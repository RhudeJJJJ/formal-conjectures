/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2364 : Family 9 := level9.get ⟨460,by decide⟩
def sourceMap2364 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2364 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2364_checked : acceptsGraphIso
    (source (graph core2364) (root 9) 0 4) DegreeTwoThreeSpectrum4485.graph sourceMap2364=true := by decide +kernel
theorem fusedMap2364_checked : acceptsGraphIso
    (fused (graph core2364) (root 9) 0 4) DegreeTwoThreeSpectrum4486.graph fusedMap2364=true := by decide +kernel
theorem certified2364 : Certified (graph core2364) (root 9) 0 4 :=
  of_native_maps core2364 DegreeTwoThreeSpectrum4485.graph DegreeTwoThreeSpectrum4486.graph
    sourceMap2364 fusedMap2364 sourceMap2364_checked fusedMap2364_checked
    DegreeTwoThreeFiniteComparisons.comparison2364
#print axioms sourceMap2364_checked
#print axioms fusedMap2364_checked
#print axioms certified2364
def sourceMap2364swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2364swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2364swap_checked : acceptsGraphIso
    (source (graph core2364) (root 9) 4 0) DegreeTwoThreeSpectrum4485.graph sourceMap2364swap=true := by decide +kernel
theorem fusedMap2364swap_checked : acceptsGraphIso
    (fused (graph core2364) (root 9) 4 0) DegreeTwoThreeSpectrum4486.graph fusedMap2364swap=true := by decide +kernel
theorem certified2364swap : Certified (graph core2364) (root 9) 4 0 :=
  of_native_maps core2364 DegreeTwoThreeSpectrum4485.graph DegreeTwoThreeSpectrum4486.graph
    sourceMap2364swap fusedMap2364swap sourceMap2364swap_checked fusedMap2364swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2364
#print axioms sourceMap2364swap_checked
#print axioms fusedMap2364swap_checked
#print axioms certified2364swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
