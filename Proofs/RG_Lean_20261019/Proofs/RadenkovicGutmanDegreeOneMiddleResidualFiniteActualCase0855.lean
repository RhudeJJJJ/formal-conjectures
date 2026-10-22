/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0855 : Family 10 := level10.get ⟨583,by decide⟩
def sourceMap0855 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap0855 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0855_checked : acceptsGraphIso
    (source (graph core0855) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2077.graph sourceMap0855=true := by decide +kernel
theorem fusedMap0855_checked : acceptsGraphIso
    (fused (graph core0855) (root 10) 2 2) DegreeTwoThreeSpectrum5252.graph fusedMap0855=true := by decide +kernel
theorem certified0855 : Certified (graph core0855) (root 10) 2 2 :=
  of_native_maps core0855 DegreeOneMiddleResidualSpectrum2077.graph DegreeTwoThreeSpectrum5252.graph
    sourceMap0855 fusedMap0855 sourceMap0855_checked fusedMap0855_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0855
#print axioms sourceMap0855_checked
#print axioms fusedMap0855_checked
#print axioms certified0855
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
