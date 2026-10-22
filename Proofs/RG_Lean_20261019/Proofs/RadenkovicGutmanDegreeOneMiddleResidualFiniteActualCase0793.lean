/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0793 : Family 10 := level10.get ⟨468,by decide⟩
def sourceMap0793 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,12,13,14,15,16,8,9,10,11,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0793 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0793_checked : acceptsGraphIso
    (source (graph core0793) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1838.graph sourceMap0793=true := by decide +kernel
theorem fusedMap0793_checked : acceptsGraphIso
    (fused (graph core0793) (root 10) 2 2) DegreeTwoThreeSpectrum5918.graph fusedMap0793=true := by decide +kernel
theorem certified0793 : Certified (graph core0793) (root 10) 2 2 :=
  of_native_maps core0793 DegreeOneMiddleResidualSpectrum1838.graph DegreeTwoThreeSpectrum5918.graph
    sourceMap0793 fusedMap0793 sourceMap0793_checked fusedMap0793_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0793
#print axioms sourceMap0793_checked
#print axioms fusedMap0793_checked
#print axioms certified0793
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
