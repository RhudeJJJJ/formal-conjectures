/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0490 : Family 10 := level10.get ⟨6,by decide⟩
def sourceMap0490 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![3,2,1,0,10,11,12,13,14,15,16,4,5,6,7,8,9] (sourceLabel 10 2 2 v)
def fusedMap0490 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0490_checked : acceptsGraphIso
    (source (graph core0490) (root 10) 2 2) DegreeTwoThreeSpectrum5670.graph sourceMap0490=true := by decide +kernel
theorem fusedMap0490_checked : acceptsGraphIso
    (fused (graph core0490) (root 10) 2 2) DegreeTwoThreeSpectrum4964.graph fusedMap0490=true := by decide +kernel
theorem certified0490 : Certified (graph core0490) (root 10) 2 2 :=
  of_native_maps core0490 DegreeTwoThreeSpectrum5670.graph DegreeTwoThreeSpectrum4964.graph
    sourceMap0490 fusedMap0490 sourceMap0490_checked fusedMap0490_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0490
#print axioms sourceMap0490_checked
#print axioms fusedMap0490_checked
#print axioms certified0490
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
