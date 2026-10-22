/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons54
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2742 : Family 10 := level10.get ⟨930,by decide⟩
def sourceMap2742 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2742 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2742_checked : acceptsGraphIso
    (source (graph core2742) (root 10) 0 4) DegreeTwoThreeSpectrum7006.graph sourceMap2742=true := by decide +kernel
theorem fusedMap2742_checked : acceptsGraphIso
    (fused (graph core2742) (root 10) 0 4) DegreeTwoThreeSpectrum5824.graph fusedMap2742=true := by decide +kernel
theorem certified2742 : Certified (graph core2742) (root 10) 0 4 :=
  of_native_maps core2742 DegreeTwoThreeSpectrum7006.graph DegreeTwoThreeSpectrum5824.graph
    sourceMap2742 fusedMap2742 sourceMap2742_checked fusedMap2742_checked
    DegreeTwoThreeFiniteComparisons.comparison2742
#print axioms sourceMap2742_checked
#print axioms fusedMap2742_checked
#print axioms certified2742
def sourceMap2742swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2742swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2742swap_checked : acceptsGraphIso
    (source (graph core2742) (root 10) 4 0) DegreeTwoThreeSpectrum7006.graph sourceMap2742swap=true := by decide +kernel
theorem fusedMap2742swap_checked : acceptsGraphIso
    (fused (graph core2742) (root 10) 4 0) DegreeTwoThreeSpectrum5824.graph fusedMap2742swap=true := by decide +kernel
theorem certified2742swap : Certified (graph core2742) (root 10) 4 0 :=
  of_native_maps core2742 DegreeTwoThreeSpectrum7006.graph DegreeTwoThreeSpectrum5824.graph
    sourceMap2742swap fusedMap2742swap sourceMap2742swap_checked fusedMap2742swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2742
#print axioms sourceMap2742swap_checked
#print axioms fusedMap2742swap_checked
#print axioms certified2742swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
