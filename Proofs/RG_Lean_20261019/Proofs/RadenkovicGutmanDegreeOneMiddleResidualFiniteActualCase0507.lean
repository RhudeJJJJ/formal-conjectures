/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0507 : Family 10 := level10.get ⟨26,by decide⟩
def sourceMap0507 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0507 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0507_checked : acceptsGraphIso
    (source (graph core0507) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1380.graph sourceMap0507=true := by decide +kernel
theorem fusedMap0507_checked : acceptsGraphIso
    (fused (graph core0507) (root 10) 2 2) DegreeTwoThreeSpectrum5055.graph fusedMap0507=true := by decide +kernel
theorem certified0507 : Certified (graph core0507) (root 10) 2 2 :=
  of_native_maps core0507 DegreeOneMiddleResidualSpectrum1380.graph DegreeTwoThreeSpectrum5055.graph
    sourceMap0507 fusedMap0507 sourceMap0507_checked fusedMap0507_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0507
#print axioms sourceMap0507_checked
#print axioms fusedMap0507_checked
#print axioms certified0507
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
