/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2339 : Family 9 := level9.get ⟨399,by decide⟩
def sourceMap2339 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2339 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2339_checked : acceptsGraphIso
    (source (graph core2339) (root 9) 0 4) DegreeTwoThreeSpectrum4353.graph sourceMap2339=true := by decide +kernel
theorem fusedMap2339_checked : acceptsGraphIso
    (fused (graph core2339) (root 9) 0 4) DegreeTwoThreeSpectrum4354.graph fusedMap2339=true := by decide +kernel
theorem certified2339 : Certified (graph core2339) (root 9) 0 4 :=
  of_native_maps core2339 DegreeTwoThreeSpectrum4353.graph DegreeTwoThreeSpectrum4354.graph
    sourceMap2339 fusedMap2339 sourceMap2339_checked fusedMap2339_checked
    DegreeTwoThreeFiniteComparisons.comparison2339
#print axioms sourceMap2339_checked
#print axioms fusedMap2339_checked
#print axioms certified2339
def sourceMap2339swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2339swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2339swap_checked : acceptsGraphIso
    (source (graph core2339) (root 9) 4 0) DegreeTwoThreeSpectrum4353.graph sourceMap2339swap=true := by decide +kernel
theorem fusedMap2339swap_checked : acceptsGraphIso
    (fused (graph core2339) (root 9) 4 0) DegreeTwoThreeSpectrum4354.graph fusedMap2339swap=true := by decide +kernel
theorem certified2339swap : Certified (graph core2339) (root 9) 4 0 :=
  of_native_maps core2339 DegreeTwoThreeSpectrum4353.graph DegreeTwoThreeSpectrum4354.graph
    sourceMap2339swap fusedMap2339swap sourceMap2339swap_checked fusedMap2339swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2339
#print axioms sourceMap2339swap_checked
#print axioms fusedMap2339swap_checked
#print axioms certified2339swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
