/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0731 : Family 10 := level10.get ⟨355,by decide⟩
def sourceMap0731 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,6,0,1,2,3,4,5,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0731 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0731_checked : acceptsGraphIso
    (source (graph core0731) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1823.graph sourceMap0731=true := by decide +kernel
theorem fusedMap0731_checked : acceptsGraphIso
    (fused (graph core0731) (root 10) 2 2) DegreeTwoThreeSpectrum5634.graph fusedMap0731=true := by decide +kernel
theorem certified0731 : Certified (graph core0731) (root 10) 2 2 :=
  of_native_maps core0731 DegreeOneMiddleResidualSpectrum1823.graph DegreeTwoThreeSpectrum5634.graph
    sourceMap0731 fusedMap0731 sourceMap0731_checked fusedMap0731_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0731
#print axioms sourceMap0731_checked
#print axioms fusedMap0731_checked
#print axioms certified0731
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
