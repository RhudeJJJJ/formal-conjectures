/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0543 : Family 10 := level10.get ⟨71,by decide⟩
def sourceMap0543 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0543 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0543_checked : acceptsGraphIso
    (source (graph core0543) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1684.graph sourceMap0543=true := by decide +kernel
theorem fusedMap0543_checked : acceptsGraphIso
    (fused (graph core0543) (root 10) 2 2) DegreeTwoThreeSpectrum4985.graph fusedMap0543=true := by decide +kernel
theorem certified0543 : Certified (graph core0543) (root 10) 2 2 :=
  of_native_maps core0543 DegreeOneMiddleResidualSpectrum1684.graph DegreeTwoThreeSpectrum4985.graph
    sourceMap0543 fusedMap0543 sourceMap0543_checked fusedMap0543_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0543
#print axioms sourceMap0543_checked
#print axioms fusedMap0543_checked
#print axioms certified0543
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
