/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0491 : Family 10 := level10.get ⟨7,by decide⟩
def sourceMap0491 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![3,2,1,0,11,12,13,14,15,16,10,4,5,6,7,8,9] (sourceLabel 10 2 2 v)
def fusedMap0491 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0491_checked : acceptsGraphIso
    (source (graph core0491) (root 10) 2 2) DegreeTwoThreeSpectrum5668.graph sourceMap0491=true := by decide +kernel
theorem fusedMap0491_checked : acceptsGraphIso
    (fused (graph core0491) (root 10) 2 2) DegreeTwoThreeSpectrum4965.graph fusedMap0491=true := by decide +kernel
theorem certified0491 : Certified (graph core0491) (root 10) 2 2 :=
  of_native_maps core0491 DegreeTwoThreeSpectrum5668.graph DegreeTwoThreeSpectrum4965.graph
    sourceMap0491 fusedMap0491 sourceMap0491_checked fusedMap0491_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0491
#print axioms sourceMap0491_checked
#print axioms fusedMap0491_checked
#print axioms certified0491
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
