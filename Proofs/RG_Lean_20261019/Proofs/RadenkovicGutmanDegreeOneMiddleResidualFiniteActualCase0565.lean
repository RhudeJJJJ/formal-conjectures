/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0565 : Family 10 := level10.get ⟨101,by decide⟩
def sourceMap0565 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0565 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0565_checked : acceptsGraphIso
    (source (graph core0565) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1806.graph sourceMap0565=true := by decide +kernel
theorem fusedMap0565_checked : acceptsGraphIso
    (fused (graph core0565) (root 10) 2 2) DegreeTwoThreeSpectrum5023.graph fusedMap0565=true := by decide +kernel
theorem certified0565 : Certified (graph core0565) (root 10) 2 2 :=
  of_native_maps core0565 DegreeOneMiddleResidualSpectrum1806.graph DegreeTwoThreeSpectrum5023.graph
    sourceMap0565 fusedMap0565 sourceMap0565_checked fusedMap0565_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0565
#print axioms sourceMap0565_checked
#print axioms fusedMap0565_checked
#print axioms certified0565
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
