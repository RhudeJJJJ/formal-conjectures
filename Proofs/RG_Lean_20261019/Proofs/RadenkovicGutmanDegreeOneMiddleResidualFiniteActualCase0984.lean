/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0984 : Family 10 := level10.get ⟨853,by decide⟩
def sourceMap0984 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0984 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0984_checked : acceptsGraphIso
    (source (graph core0984) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2285.graph sourceMap0984=true := by decide +kernel
theorem fusedMap0984_checked : acceptsGraphIso
    (fused (graph core0984) (root 10) 2 2) DegreeTwoThreeSpectrum5689.graph fusedMap0984=true := by decide +kernel
theorem certified0984 : Certified (graph core0984) (root 10) 2 2 :=
  of_native_maps core0984 DegreeOneMiddleResidualSpectrum2285.graph DegreeTwoThreeSpectrum5689.graph
    sourceMap0984 fusedMap0984 sourceMap0984_checked fusedMap0984_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0984
#print axioms sourceMap0984_checked
#print axioms fusedMap0984_checked
#print axioms certified0984
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
