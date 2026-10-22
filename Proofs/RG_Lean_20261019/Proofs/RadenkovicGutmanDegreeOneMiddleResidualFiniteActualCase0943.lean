/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0943 : Family 10 := level10.get ⟨764,by decide⟩
def sourceMap0943 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0943 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0943_checked : acceptsGraphIso
    (source (graph core0943) (root 10) 2 2) DegreeOneMiddleResidualSpectrum2224.graph sourceMap0943=true := by decide +kernel
theorem fusedMap0943_checked : acceptsGraphIso
    (fused (graph core0943) (root 10) 2 2) DegreeTwoThreeSpectrum5541.graph fusedMap0943=true := by decide +kernel
theorem certified0943 : Certified (graph core0943) (root 10) 2 2 :=
  of_native_maps core0943 DegreeOneMiddleResidualSpectrum2224.graph DegreeTwoThreeSpectrum5541.graph
    sourceMap0943 fusedMap0943 sourceMap0943_checked fusedMap0943_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0943
#print axioms sourceMap0943_checked
#print axioms fusedMap0943_checked
#print axioms certified0943
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
