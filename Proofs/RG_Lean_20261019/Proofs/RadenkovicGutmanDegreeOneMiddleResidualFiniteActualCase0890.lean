/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0890 : Family 10 := level10.get ⟨653,by decide⟩
def sourceMap0890 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap0890 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0890_checked : acceptsGraphIso
    (source (graph core0890) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2133.graph sourceMap0890=true := by decide +kernel
theorem fusedMap0890_checked : acceptsGraphIso
    (fused (graph core0890) (root 10) 2 2) DegreeTwoThreeSpectrum5362.graph fusedMap0890=true := by decide +kernel
theorem certified0890 : Certified (graph core0890) (root 10) 2 2 :=
  of_native_maps core0890 DegreeOneMiddleResidualSpectrum2133.graph DegreeTwoThreeSpectrum5362.graph
    sourceMap0890 fusedMap0890 sourceMap0890_checked fusedMap0890_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0890
#print axioms sourceMap0890_checked
#print axioms fusedMap0890_checked
#print axioms certified0890
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
