/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0629 : Family 10 := level10.get ⟨198,by decide⟩
def sourceMap0629 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0629 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0629_checked : acceptsGraphIso
    (source (graph core0629) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1569.graph sourceMap0629=true := by decide +kernel
theorem fusedMap0629_checked : acceptsGraphIso
    (fused (graph core0629) (root 10) 2 2) DegreeTwoThreeSpectrum5177.graph fusedMap0629=true := by decide +kernel
theorem certified0629 : Certified (graph core0629) (root 10) 2 2 :=
  of_native_maps core0629 DegreeOneMiddleResidualSpectrum1569.graph DegreeTwoThreeSpectrum5177.graph
    sourceMap0629 fusedMap0629 sourceMap0629_checked fusedMap0629_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0629
#print axioms sourceMap0629_checked
#print axioms fusedMap0629_checked
#print axioms certified0629
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
