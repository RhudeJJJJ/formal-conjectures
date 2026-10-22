/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0940 : Family 10 := level10.get ⟨753,by decide⟩
def sourceMap0940 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap0940 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0940_checked : acceptsGraphIso
    (source (graph core0940) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2218.graph sourceMap0940=true := by decide +kernel
theorem fusedMap0940_checked : acceptsGraphIso
    (fused (graph core0940) (root 10) 2 2) DegreeTwoThreeSpectrum5519.graph fusedMap0940=true := by decide +kernel
theorem certified0940 : Certified (graph core0940) (root 10) 2 2 :=
  of_native_maps core0940 DegreeOneMiddleResidualSpectrum2218.graph DegreeTwoThreeSpectrum5519.graph
    sourceMap0940 fusedMap0940 sourceMap0940_checked fusedMap0940_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0940
#print axioms sourceMap0940_checked
#print axioms fusedMap0940_checked
#print axioms certified0940
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
