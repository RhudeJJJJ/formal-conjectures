/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0612 : Family 10 := level10.get ⟨167,by decide⟩
def sourceMap0612 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0612 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0612_checked : acceptsGraphIso
    (source (graph core0612) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1893.graph sourceMap0612=true := by decide +kernel
theorem fusedMap0612_checked : acceptsGraphIso
    (fused (graph core0612) (root 10) 2 2) DegreeTwoThreeSpectrum5109.graph fusedMap0612=true := by decide +kernel
theorem certified0612 : Certified (graph core0612) (root 10) 2 2 :=
  of_native_maps core0612 DegreeOneMiddleResidualSpectrum1893.graph DegreeTwoThreeSpectrum5109.graph
    sourceMap0612 fusedMap0612 sourceMap0612_checked fusedMap0612_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0612
#print axioms sourceMap0612_checked
#print axioms fusedMap0612_checked
#print axioms certified0612
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
