/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0082 : Family 8 := level8.get ⟨27,by decide⟩
def sourceMap0082 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,9,10,11,12,13,14,8,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0082 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0082_checked : acceptsGraphIso
    (source (graph core0082) (root 8) 2 2) DegreeTwoThreeSpectrum2821.graph sourceMap0082=true := by decide +kernel
theorem fusedMap0082_checked : acceptsGraphIso
    (fused (graph core0082) (root 8) 2 2) DegreeTwoThreeSpectrum2422.graph fusedMap0082=true := by decide +kernel
theorem certified0082 : Certified (graph core0082) (root 8) 2 2 :=
  of_native_maps core0082 DegreeTwoThreeSpectrum2821.graph DegreeTwoThreeSpectrum2422.graph
    sourceMap0082 fusedMap0082 sourceMap0082_checked fusedMap0082_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0082
#print axioms sourceMap0082_checked
#print axioms fusedMap0082_checked
#print axioms certified0082
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
