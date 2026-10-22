/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0719 : Family 10 := level10.get ⟨334,by decide⟩
def sourceMap0719 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0719 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0719_checked : acceptsGraphIso
    (source (graph core0719) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1804.graph sourceMap0719=true := by decide +kernel
theorem fusedMap0719_checked : acceptsGraphIso
    (fused (graph core0719) (root 10) 2 2) DegreeTwoThreeSpectrum5579.graph fusedMap0719=true := by decide +kernel
theorem certified0719 : Certified (graph core0719) (root 10) 2 2 :=
  of_native_maps core0719 DegreeOneMiddleResidualSpectrum1804.graph DegreeTwoThreeSpectrum5579.graph
    sourceMap0719 fusedMap0719 sourceMap0719_checked fusedMap0719_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0719
#print axioms sourceMap0719_checked
#print axioms fusedMap0719_checked
#print axioms certified0719
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
