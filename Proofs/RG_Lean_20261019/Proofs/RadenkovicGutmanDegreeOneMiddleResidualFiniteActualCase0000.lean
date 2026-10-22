/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0000 : Family 7 := level7.get ⟨0,by decide⟩
def sourceMap0000 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![2,1,0,9,10,11,12,13,3,4,5,6,7,8] (sourceLabel 7 2 2 v)
def fusedMap0000 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,7,8,9,10,11,12,13,1,2,3,4,5,6] (fusedLabel 7 2 2 v)
theorem sourceMap0000_checked : acceptsGraphIso
    (source (graph core0000) (root 7) 2 2) DegreeTwoThreeSpectrum1861.graph sourceMap0000=true := by decide +kernel
theorem fusedMap0000_checked : acceptsGraphIso
    (fused (graph core0000) (root 7) 2 2) DegreeOneMiddleResidualSpectrum000.graph fusedMap0000=true := by decide +kernel
theorem certified0000 : Certified (graph core0000) (root 7) 2 2 :=
  of_native_maps core0000 DegreeTwoThreeSpectrum1861.graph DegreeOneMiddleResidualSpectrum000.graph
    sourceMap0000 fusedMap0000 sourceMap0000_checked fusedMap0000_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0000
#print axioms sourceMap0000_checked
#print axioms fusedMap0000_checked
#print axioms certified0000
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
