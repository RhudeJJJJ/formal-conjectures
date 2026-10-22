/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0721 : Family 10 := level10.get ⟨1014,by decide⟩
def sourceMap0721 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0721 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0721_checked : acceptsGraphIso
    (source (graph core0721) (root 10) 0 0) DegreeTwoThreeSpectrum1321.graph sourceMap0721=true := by decide +kernel
theorem fusedMap0721_checked : acceptsGraphIso
    (fused (graph core0721) (root 10) 0 0) DegreeOneSmallSpectrum1576.graph fusedMap0721=true := by decide +kernel
theorem certified0721 : Certified (graph core0721) (root 10) 0 0 :=
  of_native_maps core0721 DegreeTwoThreeSpectrum1321.graph DegreeOneSmallSpectrum1576.graph
    sourceMap0721 fusedMap0721 sourceMap0721_checked fusedMap0721_checked
    DegreeTwoThreeFiniteComparisons.comparison0721
#print axioms sourceMap0721_checked
#print axioms fusedMap0721_checked
#print axioms certified0721
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
