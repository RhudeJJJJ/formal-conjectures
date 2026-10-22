/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0560 : Family 10 := level10.get ⟨95,by decide⟩
def sourceMap0560 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0560 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0560_checked : acceptsGraphIso
    (source (graph core0560) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1778.graph sourceMap0560=true := by decide +kernel
theorem fusedMap0560_checked : acceptsGraphIso
    (fused (graph core0560) (root 10) 2 2) DegreeTwoThreeSpectrum5016.graph fusedMap0560=true := by decide +kernel
theorem certified0560 : Certified (graph core0560) (root 10) 2 2 :=
  of_native_maps core0560 DegreeOneMiddleResidualSpectrum1778.graph DegreeTwoThreeSpectrum5016.graph
    sourceMap0560 fusedMap0560 sourceMap0560_checked fusedMap0560_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0560
#print axioms sourceMap0560_checked
#print axioms fusedMap0560_checked
#print axioms certified0560
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
