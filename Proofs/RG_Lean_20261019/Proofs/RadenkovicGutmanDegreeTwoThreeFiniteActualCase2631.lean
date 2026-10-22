/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2631 : Family 10 := level10.get ⟨630,by decide⟩
def sourceMap2631 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2631 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2631_checked : acceptsGraphIso
    (source (graph core2631) (root 10) 0 4) DegreeTwoThreeSpectrum6381.graph sourceMap2631=true := by decide +kernel
theorem fusedMap2631_checked : acceptsGraphIso
    (fused (graph core2631) (root 10) 0 4) DegreeTwoThreeSpectrum5321.graph fusedMap2631=true := by decide +kernel
theorem certified2631 : Certified (graph core2631) (root 10) 0 4 :=
  of_native_maps core2631 DegreeTwoThreeSpectrum6381.graph DegreeTwoThreeSpectrum5321.graph
    sourceMap2631 fusedMap2631 sourceMap2631_checked fusedMap2631_checked
    DegreeTwoThreeFiniteComparisons.comparison2631
#print axioms sourceMap2631_checked
#print axioms fusedMap2631_checked
#print axioms certified2631
def sourceMap2631swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2631swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2631swap_checked : acceptsGraphIso
    (source (graph core2631) (root 10) 4 0) DegreeTwoThreeSpectrum6381.graph sourceMap2631swap=true := by decide +kernel
theorem fusedMap2631swap_checked : acceptsGraphIso
    (fused (graph core2631) (root 10) 4 0) DegreeTwoThreeSpectrum5321.graph fusedMap2631swap=true := by decide +kernel
theorem certified2631swap : Certified (graph core2631) (root 10) 4 0 :=
  of_native_maps core2631 DegreeTwoThreeSpectrum6381.graph DegreeTwoThreeSpectrum5321.graph
    sourceMap2631swap fusedMap2631swap sourceMap2631swap_checked fusedMap2631swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2631
#print axioms sourceMap2631swap_checked
#print axioms fusedMap2631swap_checked
#print axioms certified2631swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
