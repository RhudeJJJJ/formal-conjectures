/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0777 : Family 10 := level10.get ⟨435,by decide⟩
def sourceMap0777 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0777 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0777_checked : acceptsGraphIso
    (source (graph core0777) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1930.graph sourceMap0777=true := by decide +kernel
theorem fusedMap0777_checked : acceptsGraphIso
    (fused (graph core0777) (root 10) 2 2) DegreeTwoThreeSpectrum5844.graph fusedMap0777=true := by decide +kernel
theorem certified0777 : Certified (graph core0777) (root 10) 2 2 :=
  of_native_maps core0777 DegreeOneMiddleResidualSpectrum1930.graph DegreeTwoThreeSpectrum5844.graph
    sourceMap0777 fusedMap0777 sourceMap0777_checked fusedMap0777_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0777
#print axioms sourceMap0777_checked
#print axioms fusedMap0777_checked
#print axioms certified0777
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
