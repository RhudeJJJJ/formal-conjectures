/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0863 : Family 10 := level10.get ⟨596,by decide⟩
def sourceMap0863 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0863 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0863_checked : acceptsGraphIso
    (source (graph core0863) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2093.graph sourceMap0863=true := by decide +kernel
theorem fusedMap0863_checked : acceptsGraphIso
    (fused (graph core0863) (root 10) 2 2) DegreeTwoThreeSpectrum5270.graph fusedMap0863=true := by decide +kernel
theorem certified0863 : Certified (graph core0863) (root 10) 2 2 :=
  of_native_maps core0863 DegreeOneMiddleResidualSpectrum2093.graph DegreeTwoThreeSpectrum5270.graph
    sourceMap0863 fusedMap0863 sourceMap0863_checked fusedMap0863_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0863
#print axioms sourceMap0863_checked
#print axioms fusedMap0863_checked
#print axioms certified0863
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
