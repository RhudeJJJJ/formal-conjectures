/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0847 : Family 10 := level10.get ⟨570,by decide⟩
def sourceMap0847 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0847 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0847_checked : acceptsGraphIso
    (source (graph core0847) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2061.graph sourceMap0847=true := by decide +kernel
theorem fusedMap0847_checked : acceptsGraphIso
    (fused (graph core0847) (root 10) 2 2) DegreeTwoThreeSpectrum5235.graph fusedMap0847=true := by decide +kernel
theorem certified0847 : Certified (graph core0847) (root 10) 2 2 :=
  of_native_maps core0847 DegreeOneMiddleResidualSpectrum2061.graph DegreeTwoThreeSpectrum5235.graph
    sourceMap0847 fusedMap0847 sourceMap0847_checked fusedMap0847_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0847
#print axioms sourceMap0847_checked
#print axioms fusedMap0847_checked
#print axioms certified0847
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
