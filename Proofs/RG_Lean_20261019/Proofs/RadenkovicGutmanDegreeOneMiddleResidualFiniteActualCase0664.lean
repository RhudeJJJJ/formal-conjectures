/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0664 : Family 10 := level10.get ⟨247,by decide⟩
def sourceMap0664 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0664 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0664_checked : acceptsGraphIso
    (source (graph core0664) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1675.graph sourceMap0664=true := by decide +kernel
theorem fusedMap0664_checked : acceptsGraphIso
    (fused (graph core0664) (root 10) 2 2) DegreeTwoThreeSpectrum5333.graph fusedMap0664=true := by decide +kernel
theorem certified0664 : Certified (graph core0664) (root 10) 2 2 :=
  of_native_maps core0664 DegreeOneMiddleResidualSpectrum1675.graph DegreeTwoThreeSpectrum5333.graph
    sourceMap0664 fusedMap0664 sourceMap0664_checked fusedMap0664_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0664
#print axioms sourceMap0664_checked
#print axioms fusedMap0664_checked
#print axioms certified0664
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
