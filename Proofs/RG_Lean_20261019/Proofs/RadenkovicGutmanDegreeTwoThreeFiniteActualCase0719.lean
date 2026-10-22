/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0719 : Family 10 := level10.get ⟨1006,by decide⟩
def sourceMap0719 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0719 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0719_checked : acceptsGraphIso
    (source (graph core0719) (root 10) 0 0) DegreeTwoThreeSpectrum1304.graph sourceMap0719=true := by decide +kernel
theorem fusedMap0719_checked : acceptsGraphIso
    (fused (graph core0719) (root 10) 0 0) DegreeOneSmallSpectrum1550.graph fusedMap0719=true := by decide +kernel
theorem certified0719 : Certified (graph core0719) (root 10) 0 0 :=
  of_native_maps core0719 DegreeTwoThreeSpectrum1304.graph DegreeOneSmallSpectrum1550.graph
    sourceMap0719 fusedMap0719 sourceMap0719_checked fusedMap0719_checked
    DegreeTwoThreeFiniteComparisons.comparison0719
#print axioms sourceMap0719_checked
#print axioms fusedMap0719_checked
#print axioms certified0719
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
