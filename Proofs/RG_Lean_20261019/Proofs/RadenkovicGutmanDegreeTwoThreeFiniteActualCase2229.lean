/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2229 : Family 9 := level9.get ⟨73,by decide⟩
def sourceMap2229 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2229 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2229_checked : acceptsGraphIso
    (source (graph core2229) (root 9) 0 4) DegreeTwoThreeSpectrum3999.graph sourceMap2229=true := by decide +kernel
theorem fusedMap2229_checked : acceptsGraphIso
    (fused (graph core2229) (root 9) 0 4) DegreeTwoThreeSpectrum4000.graph fusedMap2229=true := by decide +kernel
theorem certified2229 : Certified (graph core2229) (root 9) 0 4 :=
  of_native_maps core2229 DegreeTwoThreeSpectrum3999.graph DegreeTwoThreeSpectrum4000.graph
    sourceMap2229 fusedMap2229 sourceMap2229_checked fusedMap2229_checked
    DegreeTwoThreeFiniteComparisons.comparison2229
#print axioms sourceMap2229_checked
#print axioms fusedMap2229_checked
#print axioms certified2229
def sourceMap2229swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2229swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2229swap_checked : acceptsGraphIso
    (source (graph core2229) (root 9) 4 0) DegreeTwoThreeSpectrum3999.graph sourceMap2229swap=true := by decide +kernel
theorem fusedMap2229swap_checked : acceptsGraphIso
    (fused (graph core2229) (root 9) 4 0) DegreeTwoThreeSpectrum4000.graph fusedMap2229swap=true := by decide +kernel
theorem certified2229swap : Certified (graph core2229) (root 9) 4 0 :=
  of_native_maps core2229 DegreeTwoThreeSpectrum3999.graph DegreeTwoThreeSpectrum4000.graph
    sourceMap2229swap fusedMap2229swap sourceMap2229swap_checked fusedMap2229swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2229
#print axioms sourceMap2229swap_checked
#print axioms fusedMap2229swap_checked
#print axioms certified2229swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
