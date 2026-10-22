/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0752 : Family 10 := level10.get ⟨1089,by decide⟩
def sourceMap0752 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0752 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0752_checked : acceptsGraphIso
    (source (graph core0752) (root 10) 0 0) DegreeTwoThreeSpectrum1406.graph sourceMap0752=true := by decide +kernel
theorem fusedMap0752_checked : acceptsGraphIso
    (fused (graph core0752) (root 10) 0 0) DegreeTwoThreeSpectrum1382.graph fusedMap0752=true := by decide +kernel
theorem certified0752 : Certified (graph core0752) (root 10) 0 0 :=
  of_native_maps core0752 DegreeTwoThreeSpectrum1406.graph DegreeTwoThreeSpectrum1382.graph
    sourceMap0752 fusedMap0752 sourceMap0752_checked fusedMap0752_checked
    DegreeTwoThreeFiniteComparisons.comparison0752
#print axioms sourceMap0752_checked
#print axioms fusedMap0752_checked
#print axioms certified0752
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
