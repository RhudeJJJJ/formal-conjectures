/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0999 : Family 10 := level10.get ⟨885,by decide⟩
def sourceMap0999 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0999 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0999_checked : acceptsGraphIso
    (source (graph core0999) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2302.graph sourceMap0999=true := by decide +kernel
theorem fusedMap0999_checked : acceptsGraphIso
    (fused (graph core0999) (root 10) 2 2) DegreeTwoThreeSpectrum5739.graph fusedMap0999=true := by decide +kernel
theorem certified0999 : Certified (graph core0999) (root 10) 2 2 :=
  of_native_maps core0999 DegreeOneMiddleResidualSpectrum2302.graph DegreeTwoThreeSpectrum5739.graph
    sourceMap0999 fusedMap0999 sourceMap0999_checked fusedMap0999_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0999
#print axioms sourceMap0999_checked
#print axioms fusedMap0999_checked
#print axioms certified0999
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
