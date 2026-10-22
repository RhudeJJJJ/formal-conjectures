/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2219 : Family 9 := level9.get ⟨33,by decide⟩
def sourceMap2219 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2219 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2219_checked : acceptsGraphIso
    (source (graph core2219) (root 9) 0 4) DegreeTwoThreeSpectrum4147.graph sourceMap2219=true := by decide +kernel
theorem fusedMap2219_checked : acceptsGraphIso
    (fused (graph core2219) (root 9) 0 4) DegreeTwoThreeSpectrum3881.graph fusedMap2219=true := by decide +kernel
theorem certified2219 : Certified (graph core2219) (root 9) 0 4 :=
  of_native_maps core2219 DegreeTwoThreeSpectrum4147.graph DegreeTwoThreeSpectrum3881.graph
    sourceMap2219 fusedMap2219 sourceMap2219_checked fusedMap2219_checked
    DegreeTwoThreeFiniteComparisons.comparison2219
#print axioms sourceMap2219_checked
#print axioms fusedMap2219_checked
#print axioms certified2219
def sourceMap2219swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2219swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2219swap_checked : acceptsGraphIso
    (source (graph core2219) (root 9) 4 0) DegreeTwoThreeSpectrum4147.graph sourceMap2219swap=true := by decide +kernel
theorem fusedMap2219swap_checked : acceptsGraphIso
    (fused (graph core2219) (root 9) 4 0) DegreeTwoThreeSpectrum3881.graph fusedMap2219swap=true := by decide +kernel
theorem certified2219swap : Certified (graph core2219) (root 9) 4 0 :=
  of_native_maps core2219 DegreeTwoThreeSpectrum4147.graph DegreeTwoThreeSpectrum3881.graph
    sourceMap2219swap fusedMap2219swap sourceMap2219swap_checked fusedMap2219swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2219
#print axioms sourceMap2219swap_checked
#print axioms fusedMap2219swap_checked
#print axioms certified2219swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
