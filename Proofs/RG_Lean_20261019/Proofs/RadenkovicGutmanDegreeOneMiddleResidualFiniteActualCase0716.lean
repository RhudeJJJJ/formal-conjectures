/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0716 : Family 10 := level10.get ⟨330,by decide⟩
def sourceMap0716 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0716 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0716_checked : acceptsGraphIso
    (source (graph core0716) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1800.graph sourceMap0716=true := by decide +kernel
theorem fusedMap0716_checked : acceptsGraphIso
    (fused (graph core0716) (root 10) 2 2) DegreeTwoThreeSpectrum5567.graph fusedMap0716=true := by decide +kernel
theorem certified0716 : Certified (graph core0716) (root 10) 2 2 :=
  of_native_maps core0716 DegreeOneMiddleResidualSpectrum1800.graph DegreeTwoThreeSpectrum5567.graph
    sourceMap0716 fusedMap0716 sourceMap0716_checked fusedMap0716_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0716
#print axioms sourceMap0716_checked
#print axioms fusedMap0716_checked
#print axioms certified0716
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
