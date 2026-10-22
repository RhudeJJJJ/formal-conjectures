/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0768 : Family 10 := level10.get ⟨417,by decide⟩
def sourceMap0768 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,8,9,10,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0768 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0768_checked : acceptsGraphIso
    (source (graph core0768) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1846.graph sourceMap0768=true := by decide +kernel
theorem fusedMap0768_checked : acceptsGraphIso
    (fused (graph core0768) (root 10) 2 2) DegreeTwoThreeSpectrum5801.graph fusedMap0768=true := by decide +kernel
theorem certified0768 : Certified (graph core0768) (root 10) 2 2 :=
  of_native_maps core0768 DegreeOneMiddleResidualSpectrum1846.graph DegreeTwoThreeSpectrum5801.graph
    sourceMap0768 fusedMap0768 sourceMap0768_checked fusedMap0768_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0768
#print axioms sourceMap0768_checked
#print axioms fusedMap0768_checked
#print axioms certified0768
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
