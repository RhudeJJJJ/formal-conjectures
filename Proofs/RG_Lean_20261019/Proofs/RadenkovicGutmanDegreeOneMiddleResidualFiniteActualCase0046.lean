/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0046 : Family 7 := level7.get ⟨86,by decide⟩
def sourceMap0046 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0046 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0046_checked : acceptsGraphIso
    (source (graph core0046) (root 7) 2 2) DegreeOneMiddleResidualSpectrum103.graph sourceMap0046=true := by decide +kernel
theorem fusedMap0046_checked : acceptsGraphIso
    (fused (graph core0046) (root 7) 2 2) DegreeOneMiddleResidualSpectrum040.graph fusedMap0046=true := by decide +kernel
theorem certified0046 : Certified (graph core0046) (root 7) 2 2 :=
  of_native_maps core0046 DegreeOneMiddleResidualSpectrum103.graph DegreeOneMiddleResidualSpectrum040.graph
    sourceMap0046 fusedMap0046 sourceMap0046_checked fusedMap0046_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0046
#print axioms sourceMap0046_checked
#print axioms fusedMap0046_checked
#print axioms certified0046
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
