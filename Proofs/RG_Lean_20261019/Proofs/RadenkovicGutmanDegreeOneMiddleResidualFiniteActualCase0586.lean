/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0586 : Family 10 := level10.get ⟨129,by decide⟩
def sourceMap0586 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0586 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0586_checked : acceptsGraphIso
    (source (graph core0586) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1881.graph sourceMap0586=true := by decide +kernel
theorem fusedMap0586_checked : acceptsGraphIso
    (fused (graph core0586) (root 10) 2 2) DegreeTwoThreeSpectrum5058.graph fusedMap0586=true := by decide +kernel
theorem certified0586 : Certified (graph core0586) (root 10) 2 2 :=
  of_native_maps core0586 DegreeOneMiddleResidualSpectrum1881.graph DegreeTwoThreeSpectrum5058.graph
    sourceMap0586 fusedMap0586 sourceMap0586_checked fusedMap0586_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0586
#print axioms sourceMap0586_checked
#print axioms fusedMap0586_checked
#print axioms certified0586
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
