/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3742 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap3742 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 12) → Fin 16 :=
  fun v => ![5,6,7,8,4,3,2,1,0,9,10,11,12,13,14,15] (sourceLabel 2 0 11 v)
def fusedMap3742 : (Vertices 2 ⊕ Fin 13) → Fin 16 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 2 0 11 v)
theorem sourceMap3742_checked : acceptsGraphIso
    (source (graph core3742) (root 2) 0 11) DegreeTwoThreeSpectrum3854.graph sourceMap3742=true := by decide +kernel
theorem fusedMap3742_checked : acceptsGraphIso
    (fused (graph core3742) (root 2) 0 11) DegreeTwoThreeSpectrum3861.graph fusedMap3742=true := by decide +kernel
theorem certified3742 : Certified (graph core3742) (root 2) 0 11 :=
  of_native_maps core3742 DegreeTwoThreeSpectrum3854.graph DegreeTwoThreeSpectrum3861.graph
    sourceMap3742 fusedMap3742 sourceMap3742_checked fusedMap3742_checked
    DegreeTwoThreeFiniteComparisons.comparison3742
#print axioms sourceMap3742_checked
#print axioms fusedMap3742_checked
#print axioms certified3742
def sourceMap3742swap : (Vertices 2 ⊕ Fin 12 ⊕ Fin 1) → Fin 16 :=
  fun v => ![5,6,7,4,3,2,1,0,9,10,11,12,13,14,15,8] (sourceLabel 2 11 0 v)
def fusedMap3742swap : (Vertices 2 ⊕ Fin 13) → Fin 16 :=
  fun v => ![6,7,8,5,4,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 2 11 0 v)
theorem sourceMap3742swap_checked : acceptsGraphIso
    (source (graph core3742) (root 2) 11 0) DegreeTwoThreeSpectrum3854.graph sourceMap3742swap=true := by decide +kernel
theorem fusedMap3742swap_checked : acceptsGraphIso
    (fused (graph core3742) (root 2) 11 0) DegreeTwoThreeSpectrum3861.graph fusedMap3742swap=true := by decide +kernel
theorem certified3742swap : Certified (graph core3742) (root 2) 11 0 :=
  of_native_maps core3742 DegreeTwoThreeSpectrum3854.graph DegreeTwoThreeSpectrum3861.graph
    sourceMap3742swap fusedMap3742swap sourceMap3742swap_checked fusedMap3742swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3742
#print axioms sourceMap3742swap_checked
#print axioms fusedMap3742swap_checked
#print axioms certified3742swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
