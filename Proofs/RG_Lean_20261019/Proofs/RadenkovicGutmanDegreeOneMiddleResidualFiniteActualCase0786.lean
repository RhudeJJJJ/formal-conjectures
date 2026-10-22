/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0786 : Family 10 := level10.get ⟨450,by decide⟩
def sourceMap0786 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0786 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0786_checked : acceptsGraphIso
    (source (graph core0786) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1859.graph sourceMap0786=true := by decide +kernel
theorem fusedMap0786_checked : acceptsGraphIso
    (fused (graph core0786) (root 10) 2 2) DegreeTwoThreeSpectrum5877.graph fusedMap0786=true := by decide +kernel
theorem certified0786 : Certified (graph core0786) (root 10) 2 2 :=
  of_native_maps core0786 DegreeOneMiddleResidualSpectrum1859.graph DegreeTwoThreeSpectrum5877.graph
    sourceMap0786 fusedMap0786 sourceMap0786_checked fusedMap0786_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0786
#print axioms sourceMap0786_checked
#print axioms fusedMap0786_checked
#print axioms certified0786
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
