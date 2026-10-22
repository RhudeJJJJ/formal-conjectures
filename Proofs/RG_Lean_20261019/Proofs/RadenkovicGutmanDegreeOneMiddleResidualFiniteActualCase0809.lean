/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0809 : Family 10 := level10.get ⟨507,by decide⟩
def sourceMap0809 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0809 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0809_checked : acceptsGraphIso
    (source (graph core0809) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1983.graph sourceMap0809=true := by decide +kernel
theorem fusedMap0809_checked : acceptsGraphIso
    (fused (graph core0809) (root 10) 2 2) DegreeTwoThreeSpectrum5145.graph fusedMap0809=true := by decide +kernel
theorem certified0809 : Certified (graph core0809) (root 10) 2 2 :=
  of_native_maps core0809 DegreeOneMiddleResidualSpectrum1983.graph DegreeTwoThreeSpectrum5145.graph
    sourceMap0809 fusedMap0809 sourceMap0809_checked fusedMap0809_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0809
#print axioms sourceMap0809_checked
#print axioms fusedMap0809_checked
#print axioms certified0809
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
