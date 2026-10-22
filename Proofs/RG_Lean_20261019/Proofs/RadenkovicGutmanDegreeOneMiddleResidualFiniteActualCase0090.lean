/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0090 : Family 8 := level8.get ⟨40,by decide⟩
def sourceMap0090 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0090 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0090_checked : acceptsGraphIso
    (source (graph core0090) (root 8) 2 2) DegreeOneMiddleResidualSpectrum284.graph sourceMap0090=true := by decide +kernel
theorem fusedMap0090_checked : acceptsGraphIso
    (fused (graph core0090) (root 8) 2 2) DegreeTwoThreeSpectrum2322.graph fusedMap0090=true := by decide +kernel
theorem certified0090 : Certified (graph core0090) (root 8) 2 2 :=
  of_native_maps core0090 DegreeOneMiddleResidualSpectrum284.graph DegreeTwoThreeSpectrum2322.graph
    sourceMap0090 fusedMap0090 sourceMap0090_checked fusedMap0090_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0090
#print axioms sourceMap0090_checked
#print axioms fusedMap0090_checked
#print axioms certified0090
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
