/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0903 : Family 10 := level10.get ⟨688,by decide⟩
def sourceMap0903 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0903 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0903_checked : acceptsGraphIso
    (source (graph core0903) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2155.graph sourceMap0903=true := by decide +kernel
theorem fusedMap0903_checked : acceptsGraphIso
    (fused (graph core0903) (root 10) 2 2) DegreeTwoThreeSpectrum5424.graph fusedMap0903=true := by decide +kernel
theorem certified0903 : Certified (graph core0903) (root 10) 2 2 :=
  of_native_maps core0903 DegreeOneMiddleResidualSpectrum2155.graph DegreeTwoThreeSpectrum5424.graph
    sourceMap0903 fusedMap0903 sourceMap0903_checked fusedMap0903_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0903
#print axioms sourceMap0903_checked
#print axioms fusedMap0903_checked
#print axioms certified0903
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
