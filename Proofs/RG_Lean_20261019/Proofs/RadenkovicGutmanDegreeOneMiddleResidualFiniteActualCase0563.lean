/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0563 : Family 10 := level10.get ⟨99,by decide⟩
def sourceMap0563 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0563 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0563_checked : acceptsGraphIso
    (source (graph core0563) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1797.graph sourceMap0563=true := by decide +kernel
theorem fusedMap0563_checked : acceptsGraphIso
    (fused (graph core0563) (root 10) 2 2) DegreeTwoThreeSpectrum5021.graph fusedMap0563=true := by decide +kernel
theorem certified0563 : Certified (graph core0563) (root 10) 2 2 :=
  of_native_maps core0563 DegreeOneMiddleResidualSpectrum1797.graph DegreeTwoThreeSpectrum5021.graph
    sourceMap0563 fusedMap0563 sourceMap0563_checked fusedMap0563_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0563
#print axioms sourceMap0563_checked
#print axioms fusedMap0563_checked
#print axioms certified0563
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
