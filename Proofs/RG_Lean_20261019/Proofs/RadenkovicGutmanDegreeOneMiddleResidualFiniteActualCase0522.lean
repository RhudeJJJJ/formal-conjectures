/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0522 : Family 10 := level10.get ⟨44,by decide⟩
def sourceMap0522 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,9,10,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0522 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0522_checked : acceptsGraphIso
    (source (graph core0522) (root 10) 2 2) DegreeTwoThreeSpectrum5666.graph sourceMap0522=true := by decide +kernel
theorem fusedMap0522_checked : acceptsGraphIso
    (fused (graph core0522) (root 10) 2 2) DegreeTwoThreeSpectrum5128.graph fusedMap0522=true := by decide +kernel
theorem certified0522 : Certified (graph core0522) (root 10) 2 2 :=
  of_native_maps core0522 DegreeTwoThreeSpectrum5666.graph DegreeTwoThreeSpectrum5128.graph
    sourceMap0522 fusedMap0522 sourceMap0522_checked fusedMap0522_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0522
#print axioms sourceMap0522_checked
#print axioms fusedMap0522_checked
#print axioms certified0522
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
